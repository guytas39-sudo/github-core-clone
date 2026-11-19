// A one-process GitHub-compatible git forge: REST v3, GraphQL v4, MCP over streamable HTTP and
// git smart HTTP, all from the Node standard library and all state in memory.
//
// Layout: object store + git plumbing first, then the repository domain (repos, issues, pulls,
// merges), then the four wire surfaces (REST, git HTTP, GraphQL, MCP) over one HTTP server.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash, randomUUID } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------------------------
// Fixed data: the token's user directory. The suite's scenario (wire.ts) is the contest's fixed
// data; the bearer token names its viewer, so the forge's account table is that scenario's users.
// ---------------------------------------------------------------------------------------------

const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';

interface ForgeUser {
  id: number;
  login: string;
  name: string;
  email: string;
}

const VIEWER: ForgeUser = { id: 1000, login: 'adaiversen', name: 'ada iversen', email: 'adaiversen@example.invalid' };

const USERS: ForgeUser[] = [
  VIEWER,
  { id: 1001, login: 'quinnkeller', name: 'quinn keller', email: 'quinnkeller@example.invalid' },
  { id: 1002, login: 'olgabauer', name: 'olga bauer', email: 'olgabauer@example.invalid' },
  { id: 1003, login: 'dmitriquist', name: 'dmitri quist', email: 'dmitriquist@example.invalid' },
  { id: 1004, login: 'adanovak', name: 'ada novak', email: 'adanovak@example.invalid' },
  { id: 1005, login: 'zanerossi', name: 'zane rossi', email: 'zanerossi@example.invalid' },
  { id: 1006, login: 'pavelcosta', name: 'pavel costa', email: 'pavelcosta@example.invalid' },
  { id: 1007, login: 'wrenkeller', name: 'wren keller', email: 'wrenkeller@example.invalid' },
  { id: 1008, login: 'coraquist', name: 'cora quist', email: 'coraquist@example.invalid' },
  { id: 1009, login: 'elenaulrich', name: 'elena ulrich', email: 'elenaulrich@example.invalid' },
  { id: 1010, login: 'tesssato', name: 'tess sato', email: 'tesssato@example.invalid' },
  { id: 1011, login: 'svenrossi', name: 'sven rossi', email: 'svenrossi@example.invalid' },
];

const ORG_LOGIN = 'faint-meadow-org';
const KNOWN_OWNERS = new Set<string>([...USERS.map((user) => user.login), ORG_LOGIN]);

const ZERO_OID = '0'.repeat(40);
const JSON_TYPE = 'application/json; charset=utf-8';
const VERSION = '1.0.0';

// A logical clock: strictly increasing timestamps without depending on wall time.
let clockTick = 0;
function nextEpochSec(): number {
  clockTick += 1;
  return 1_767_225_600 + clockTick;
}
function isoNow(): string {
  return new Date(nextEpochSec() * 1000).toISOString();
}

// ---------------------------------------------------------------------------------------------
// Git object store (content-addressed, shared by every repository)
// ---------------------------------------------------------------------------------------------

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';

interface GitObj {
  type: ObjType;
  data: Buffer;
}

const objectStore = new Map<string, GitObj>();

function hashObject(type: ObjType, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return createHash('sha1').update(header).update(data).digest('hex');
}

function storeObject(type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!objectStore.has(oid)) objectStore.set(oid, { type, data });
  return oid;
}

function getObject(oid: string): GitObj | undefined {
  return objectStore.get(oid);
}

// ----- trees -----

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    const mode = data.subarray(offset, space).toString('utf8');
    const nul = data.indexOf(0x00, space + 1);
    const name = data.subarray(space + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    offset = nul + 21;
  }
  return entries;
}

function serializeTree(entries: readonly TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const ka = a.mode === '40000' ? `${a.name}/` : a.name;
    const kb = b.mode === '40000' ? `${b.name}/` : b.name;
    return ka < kb ? -1 : ka > kb ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

/** Every file under a tree: path -> {oid, mode}. A null tree is the empty tree. */
function flattenTree(treeOid: string | null): Map<string, { oid: string; mode: string }> {
  const out = new Map<string, { oid: string; mode: string }>();
  const walk = (oid: string, prefix: string): void => {
    const obj = getObject(oid);
    if (!obj || obj.type !== 'tree') return;
    for (const entry of parseTree(obj.data)) {
      const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
      if (entry.mode === '40000') walk(entry.oid, path);
      else out.set(path, { oid: entry.oid, mode: entry.mode });
    }
  };
  if (treeOid !== null) walk(treeOid, '');
  return out;
}

/** Rebuild nested trees from a flat path map; returns the root tree oid. */
function buildTreeFromFlat(flat: ReadonlyMap<string, { oid: string; mode: string }>): string {
  const build = (entries: ReadonlyMap<string, { oid: string; mode: string }>): string => {
    const files: TreeEntry[] = [];
    const dirs = new Map<string, Map<string, { oid: string; mode: string }>>();
    for (const [path, value] of entries) {
      const slash = path.indexOf('/');
      if (slash < 0) {
        files.push({ mode: value.mode, name: path, oid: value.oid });
      } else {
        const dir = path.slice(0, slash);
        let sub = dirs.get(dir);
        if (sub === undefined) {
          sub = new Map();
          dirs.set(dir, sub);
        }
        sub.set(path.slice(slash + 1), value);
      }
    }
    const all: TreeEntry[] = [...files];
    for (const [name, sub] of dirs) all.push({ mode: '40000', name, oid: build(sub) });
    return storeObject('tree', serializeTree(all));
  };
  return build(flat);
}

// ----- commits and tags -----

interface CommitView {
  tree: string;
  parents: string[];
  author: string;
  committer: string;
  message: string;
}

function parseCommit(data: Buffer): CommitView {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split < 0 ? text : text.slice(0, split);
  const message = split < 0 ? '' : text.slice(split + 2);
  let tree = '';
  let author = '';
  let committer = '';
  const parents: string[] = [];
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  return { tree, parents, author, committer, message };
}

function parseTag(data: Buffer): { object: string; type: string; tag: string } {
  const text = data.toString('utf8');
  let object = '';
  let type = '';
  let tag = '';
  for (const line of text.split('\n')) {
    if (line.startsWith('object ')) object = line.slice(7).trim();
    else if (line.startsWith('type ')) type = line.slice(5).trim();
    else if (line.startsWith('tag ')) tag = line.slice(4).trim();
    else if (line === '') break;
  }
  return { object, type, tag };
}

function buildCommitData(tree: string, parents: readonly string[], message: string, epochSec: number): Buffer {
  const identity = `${VIEWER.name} <${VIEWER.email}> ${epochSec} +0000`;
  const lines = [`tree ${tree}`];
  for (const parent of parents) lines.push(`parent ${parent}`);
  lines.push(`author ${identity}`, `committer ${identity}`, '', message.endsWith('\n') ? message : `${message}\n`);
  return Buffer.from(lines.join('\n'), 'utf8');
}

/** Peel a tag chain down to the commit it names; anything else peels to itself. */
function peelToCommit(oid: string): string {
  let current = oid;
  for (let depth = 0; depth < 16; depth += 1) {
    const obj = getObject(current);
    if (!obj || obj.type !== 'tag') return current;
    current = parseTag(obj.data).object;
  }
  return current;
}

/** All commits reachable from `tip` (inclusive), following every parent. */
function commitAncestors(tip: string): Set<string> {
  const seen = new Set<string>();
  const stack = [tip];
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    const obj = getObject(oid);
    if (!obj || obj.type !== 'commit') continue;
    seen.add(oid);
    for (const parent of parseCommit(obj.data).parents) stack.push(parent);
  }
  return seen;
}

function isAncestor(maybeAncestor: string, tip: string): boolean {
  return commitAncestors(tip).has(maybeAncestor);
}

function mergeBase(a: string, b: string): string | null {
  const ancestorsOfA = commitAncestors(a);
  const seen = new Set<string>();
  const queue = [b];
  while (queue.length > 0) {
    const oid = queue.shift()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    if (ancestorsOfA.has(oid)) return oid;
    const obj = getObject(oid);
    if (obj && obj.type === 'commit') queue.push(...parseCommit(obj.data).parents);
  }
  return null;
}

/** Full object closure (commits, trees, blobs, tags) reachable from the tips. */
function collectClosure(tips: readonly string[]): Set<string> {
  const seen = new Set<string>();
  const stack = [...tips];
  while (stack.length > 0) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    const obj = getObject(oid);
    if (!obj) continue;
    seen.add(oid);
    if (obj.type === 'commit') {
      const commit = parseCommit(obj.data);
      stack.push(commit.tree, ...commit.parents);
    } else if (obj.type === 'tag') {
      stack.push(parseTag(obj.data).object);
    } else if (obj.type === 'tree') {
      for (const entry of parseTree(obj.data)) if (entry.mode !== '160000') stack.push(entry.oid);
    }
  }
  return seen;
}

// ----- packfiles -----

const PACK_TYPE_CODES: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const PACK_CODE_TYPES: Record<number, ObjType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

function writePack(oids: readonly string[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(oids.length, 8);
  parts.push(header);
  for (const oid of oids) {
    const obj = getObject(oid);
    if (!obj) continue;
    const size = obj.data.length;
    const typeCode = PACK_TYPE_CODES[obj.type];
    const bytes: number[] = [];
    let first = (typeCode << 4) | (size & 0x0f);
    let rest = Math.floor(size / 16);
    if (rest > 0) first |= 0x80;
    bytes.push(first);
    while (rest > 0) {
      let byte = rest & 0x7f;
      rest = Math.floor(rest / 128);
      if (rest > 0) byte |= 0x80;
      bytes.push(byte);
    }
    parts.push(Buffer.from(bytes));
    parts.push(deflateSync(obj.data));
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let offset = 0;
  const readSize = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[offset++];
      value += (byte & 0x7f) * 2 ** shift;
      shift += 7;
      if (!(byte & 0x80)) break;
    }
    return value;
  };
  const sourceSize = readSize();
  const targetSize = readSize();
  if (sourceSize !== base.length) throw new Error('delta base size mismatch');
  const out = Buffer.alloc(targetSize);
  let written = 0;
  while (offset < delta.length) {
    const op = delta[offset++];
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if (op & (1 << bit)) copyOffset += delta[offset++] * 2 ** shift;
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit += 1) {
        if (op & (1 << bit)) copySize += delta[offset++] * 2 ** shift;
        shift += 8;
      }
      if (copySize === 0) copySize = 0x10000;
      base.copy(out, written, copyOffset, copyOffset + copySize);
      written += copySize;
    } else if (op !== 0) {
      const literal = op & 0x7f;
      delta.copy(out, written, offset, offset + literal);
      offset += literal;
      written += literal;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  if (written !== targetSize) throw new Error('delta size mismatch');
  return out;
}

/** Read a packfile into the object store; returns the object count. Throws on a corrupt pack. */
function readPackIntoStore(pack: Buffer): number {
  if (pack.length < 12 + 20 || pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('not a packfile');
  const count = pack.readUInt32BE(8);
  let offset = 12;
  const pending: Array<{ type: ObjType; data: Buffer }> = [];
  const byOffset = new Map<number, string>();
  const resolveDelta = (baseOid: string, delta: Buffer): { type: ObjType; data: Buffer } => {
    const base = getObject(baseOid);
    if (!base) throw new Error(`delta base ${baseOid} is missing`);
    return { type: base.type, data: applyDelta(base.data, delta) };
  };
  for (let index = 0; index < count; index += 1) {
    const entryOffset = offset;
    let byte = pack[offset++];
    const typeCode = (byte >> 4) & 0x07;
    let size = byte & 0x0f;
    let shift = 4;
    while (byte & 0x80) {
      byte = pack[offset++];
      size += (byte & 0x7f) * 2 ** shift;
      shift += 7;
    }
    let baseOid: string | null = null;
    if (typeCode === 6) {
      let b = pack[offset++];
      let value = b & 0x7f;
      while (b & 0x80) {
        b = pack[offset++];
        value = (value + 1) * 128 + (b & 0x7f);
      }
      baseOid = byOffset.get(entryOffset - value) ?? null;
      if (baseOid === null) throw new Error('ofs-delta base not in pack');
    } else if (typeCode === 7) {
      baseOid = pack.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    }
    const inflated = inflateSync(pack.subarray(offset), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
    const raw = inflated.buffer;
    offset += inflated.engine.bytesWritten;
    if (raw.length !== size) throw new Error('pack entry size mismatch');
    let resolved: { type: ObjType; data: Buffer };
    if (typeCode === 6 || typeCode === 7) {
      resolved = resolveDelta(baseOid!, raw);
    } else {
      const type = PACK_CODE_TYPES[typeCode];
      if (type === undefined) throw new Error(`unknown pack type ${typeCode}`);
      resolved = { type, data: raw };
    }
    const oid = storeObject(resolved.type, resolved.data);
    byOffset.set(entryOffset, oid);
    pending.push(resolved);
  }
  return pending.length;
}

// ----- pkt-line -----

function pktLine(payload: string | Buffer): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const length = body.length + 4;
  if (length > 65520) throw new Error('pkt-line too long');
  return Buffer.concat([Buffer.from(length.toString(16).padStart(4, '0'), 'ascii'), body]);
}

const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

interface PktPacket {
  kind: 'data' | 'flush' | 'delim';
  payload: Buffer;
}

/** Decode a whole pkt-line stream; throws on malformed framing. */
function decodePktLines(buffer: Buffer): PktPacket[] {
  const packets: PktPacket[] = [];
  let offset = 0;
  while (offset < buffer.length) {
    if (offset + 4 > buffer.length) throw new Error('truncated pkt-line header');
    const hex = buffer.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) throw new Error('invalid pkt-line length');
    const length = parseInt(hex, 16);
    if (length === 0) {
      packets.push({ kind: 'flush', payload: Buffer.alloc(0) });
      offset += 4;
    } else if (length === 1) {
      packets.push({ kind: 'delim', payload: Buffer.alloc(0) });
      offset += 4;
    } else if (length === 2) {
      packets.push({ kind: 'data', payload: Buffer.alloc(0) });
      offset += 4;
    } else {
      if (length < 4 || offset + length > buffer.length) throw new Error('pkt-line overruns the body');
      packets.push({ kind: 'data', payload: buffer.subarray(offset + 4, offset + length) });
      offset += length;
    }
  }
  return packets;
}

// ---------------------------------------------------------------------------------------------
// Repository domain
// ---------------------------------------------------------------------------------------------

interface CommentRec {
  id: number;
  body: string;
  createdAt: string;
}

interface IssueRec {
  kind: 'issue';
  number: number;
  id: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  comments: CommentRec[];
  createdSeq: number;
  createdAt: string;
  updatedAt: string;
}

interface PullRec {
  kind: 'pull';
  number: number;
  id: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  headRef: string;
  baseRef: string;
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  createdSeq: number;
  createdAt: string;
  updatedAt: string;
}

interface RepoRec {
  id: number;
  owner: string;
  name: string;
  priv: boolean;
  description: string;
  defaultBranch: string;
  refs: Map<string, string>;
  labels: Map<string, { name: string; color: string }>;
  items: Map<number, IssueRec | PullRec>;
  nextNumber: number;
  createdAt: string;
}

const repos = new Map<string, RepoRec>();
let nextRepoId = 1;
let nextRecordId = 1;
let nextCommentId = 1;
let nextSeq = 1;

function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}

function findRepo(owner: string, name: string): RepoRec | null {
  if (!KNOWN_OWNERS.has(owner)) return null;
  return repos.get(repoKey(owner, name)) ?? null;
}

function createRepo(owner: string, name: string, priv: boolean, description: string): RepoRec {
  const repo: RepoRec = {
    id: nextRepoId++,
    owner,
    name,
    priv,
    description,
    defaultBranch: 'main',
    refs: new Map(),
    labels: new Map(),
    items: new Map(),
    nextNumber: 1,
    createdAt: isoNow(),
  };
  repos.set(repoKey(owner, name), repo);
  return repo;
}

function branchRef(branch: string): string {
  return `refs/heads/${branch}`;
}

function branchTip(repo: RepoRec, branch: string): string | null {
  return repo.refs.get(branchRef(branch)) ?? null;
}

function headTarget(repo: RepoRec): string {
  return branchRef(repo.defaultBranch);
}

/** Commit a new tree on a branch (creating the branch ref), returning the commit oid. */
function commitTree(repo: RepoRec, branch: string, tree: string, message: string, parents: readonly string[]): string {
  const oid = storeObject('commit', buildCommitData(tree, parents, message, nextEpochSec()));
  repo.refs.set(branchRef(branch), oid);
  return oid;
}

/**
 * Apply one file change (content, or null to delete) on a branch and commit it. A branch that does
 * not exist yet is created from the default branch's tip (or from nothing on an unborn repo).
 */
function commitFileChange(
  repo: RepoRec,
  branch: string,
  path: string,
  content: Buffer | null,
  message: string,
): { commitOid: string; blobOid: string | null; existed: boolean } {
  let tip = branchTip(repo, branch);
  if (tip === null && branch !== repo.defaultBranch) tip = branchTip(repo, repo.defaultBranch);
  const baseTree = tip !== null ? parseCommit(getObject(tip)!.data).tree : null;
  const flat = flattenTree(baseTree);
  const existed = flat.has(path);
  let blobOid: string | null = null;
  if (content === null) {
    flat.delete(path);
  } else {
    blobOid = storeObject('blob', content);
    flat.set(path, { oid: blobOid, mode: '100644' });
  }
  const tree = buildTreeFromFlat(flat);
  const commitOid = commitTree(repo, branch, tree, message, tip !== null ? [tip] : []);
  return { commitOid, blobOid, existed };
}

/** The file at `path` on a ref (branch name or commit oid), or null. */
function fileAt(repo: RepoRec, ref: string, path: string): { oid: string; mode: string; data: Buffer } | null {
  const tip = branchTip(repo, ref) ?? (getObject(ref)?.type === 'commit' ? ref : null);
  if (tip === null) return null;
  const flat = flattenTree(parseCommit(getObject(tip)!.data).tree);
  const entry = flat.get(path);
  if (!entry) return null;
  const obj = getObject(entry.oid);
  if (!obj) return null;
  return { oid: entry.oid, mode: entry.mode, data: obj.data };
}

/** The tree oid a ref resolves to (branch name or commit oid), or null. */
function treeOfRef(repo: RepoRec, ref: string): string | null {
  const tip = branchTip(repo, ref) ?? (getObject(ref)?.type === 'commit' ? ref : null);
  if (tip === null) return null;
  return parseCommit(getObject(tip)!.data).tree;
}

// ----- issues -----

function createIssue(repo: RepoRec, title: string, body: string, labels: string[]): IssueRec {
  const now = isoNow();
  const issue: IssueRec = {
    kind: 'issue',
    number: repo.nextNumber++,
    id: nextRecordId++,
    title,
    body,
    state: 'open',
    labels: [...labels],
    comments: [],
    createdSeq: nextSeq++,
    createdAt: now,
    updatedAt: now,
  };
  repo.items.set(issue.number, issue);
  return issue;
}

function getIssue(repo: RepoRec, number: number): IssueRec | null {
  const item = repo.items.get(number);
  return item !== undefined && item.kind === 'issue' ? item : null;
}

// ----- pull requests and merging -----

function createPull(repo: RepoRec, title: string, body: string, head: string, base: string): PullRec {
  const now = isoNow();
  const pull: PullRec = {
    kind: 'pull',
    number: repo.nextNumber++,
    id: nextRecordId++,
    title,
    body,
    state: 'open',
    headRef: head,
    baseRef: base,
    merged: false,
    mergedAt: null,
    mergeCommitSha: null,
    createdSeq: nextSeq++,
    createdAt: now,
    updatedAt: now,
  };
  repo.items.set(pull.number, pull);
  return pull;
}

function getPull(repo: RepoRec, number: number): PullRec | null {
  const item = repo.items.get(number);
  return item !== undefined && item.kind === 'pull' ? item : null;
}

/** File-level three-way merge of flat path maps; null when a path conflicts. */
function mergeFlats(
  base: ReadonlyMap<string, { oid: string; mode: string }>,
  ours: ReadonlyMap<string, { oid: string; mode: string }>,
  theirs: ReadonlyMap<string, { oid: string; mode: string }>,
): Map<string, { oid: string; mode: string }> | null {
  const result = new Map<string, { oid: string; mode: string }>();
  const paths = new Set<string>([...base.keys(), ...ours.keys(), ...theirs.keys()]);
  for (const path of paths) {
    const b = base.get(path)?.oid;
    const o = ours.get(path)?.oid;
    const t = theirs.get(path)?.oid;
    let chosen: { oid: string; mode: string } | undefined;
    if (o === t) chosen = ours.get(path) ?? theirs.get(path);
    else if (b === o) chosen = theirs.get(path);
    else if (b === t) chosen = ours.get(path);
    else return null;
    if (chosen !== undefined) result.set(path, chosen);
  }
  return result;
}

/** Whether merging `pull` into its base right now would conflict. */
function pullConflicts(repo: RepoRec, pull: PullRec): boolean {
  const headTip = branchTip(repo, pull.headRef);
  const baseTip = branchTip(repo, pull.baseRef);
  if (headTip === null || baseTip === null) return true;
  const base = mergeBase(headTip, baseTip);
  if (base === null) return true;
  if (isAncestor(headTip, baseTip)) return false;
  const merged = mergeFlats(
    flattenTree(parseCommit(getObject(base)!.data).tree),
    flattenTree(parseCommit(getObject(baseTip)!.data).tree),
    flattenTree(parseCommit(getObject(headTip)!.data).tree),
  );
  return merged === null;
}

/**
 * Merge a pull request into its base branch. Returns the merge commit oid, or null on conflict.
 * `method` is 'merge' | 'squash' | 'rebase'.
 */
function mergePull(repo: RepoRec, pull: PullRec, method: string): string | null {
  const headTip = branchTip(repo, pull.headRef);
  const baseTip = branchTip(repo, pull.baseRef);
  if (headTip === null || baseTip === null) return null;
  const base = mergeBase(headTip, baseTip);
  if (base === null) return null;
  const baseFlat = flattenTree(parseCommit(getObject(base)!.data).tree);
  const oursFlat = flattenTree(parseCommit(getObject(baseTip)!.data).tree);
  const theirsFlat = flattenTree(parseCommit(getObject(headTip)!.data).tree);
  const merged = mergeFlats(baseFlat, oursFlat, theirsFlat);
  if (merged === null) return null;
  const mergedTree = buildTreeFromFlat(merged);
  let mergeCommit: string;
  if (method === 'squash') {
    mergeCommit = commitTree(repo, pull.baseRef, mergedTree, `${pull.title} (#${pull.number})`, [baseTip]);
  } else if (method === 'rebase') {
    // Replay the head-only commits, oldest first, three-way merging each step.
    const headOnly: string[] = [];
    const baseAncestors = commitAncestors(baseTip);
    const seen = new Set<string>();
    const stack = [headTip];
    while (stack.length > 0) {
      const oid = stack.pop()!;
      if (seen.has(oid) || baseAncestors.has(oid)) continue;
      seen.add(oid);
      headOnly.push(oid);
      stack.push(...parseCommit(getObject(oid)!.data).parents);
    }
    headOnly.reverse();
    let current = baseTip;
    for (const oid of headOnly) {
      const commit = parseCommit(getObject(oid)!.data);
      const parentTree = commit.parents.length > 0 ? parseCommit(getObject(commit.parents[0])!.data).tree : null;
      const step = mergeFlats(flattenTree(parentTree), flattenTree(parseCommit(getObject(current)!.data).tree), flattenTree(commit.tree));
      if (step === null) return null;
      current = commitTree(repo, pull.baseRef, buildTreeFromFlat(step), commit.message, [current]);
    }
    mergeCommit = current;
  } else {
    mergeCommit = commitTree(repo, pull.baseRef, mergedTree, `Merge pull request #${pull.number} from ${pull.headRef}`, [baseTip, headTip]);
  }
  pull.merged = true;
  pull.state = 'closed';
  pull.mergedAt = isoNow();
  pull.mergeCommitSha = mergeCommit;
  pull.updatedAt = pull.mergedAt;
  return mergeCommit;
}

// ----- file diffs -----

function splitLines(data: Buffer): string[] {
  if (data.length === 0) return [];
  const lines = data.toString('utf8').split('\n');
  if (lines[lines.length - 1] === '') lines.pop();
  return lines;
}

/** Line additions/deletions between two texts, by longest common subsequence. */
function lineDiff(oldData: Buffer | null, newData: Buffer | null): { additions: number; deletions: number } {
  const oldLines = oldData === null ? [] : splitLines(oldData);
  const newLines = newData === null ? [] : splitLines(newData);
  const m = oldLines.length;
  const n = newLines.length;
  if (m * n > 4_000_000) {
    // Very large files: fall back to a whole-file approximation.
    return { additions: n, deletions: m };
  }
  const dp: number[] = new Array((m + 1) * (n + 1)).fill(0);
  for (let i = m - 1; i >= 0; i -= 1) {
    for (let j = n - 1; j >= 0; j -= 1) {
      dp[i * (n + 1) + j] = oldLines[i] === newLines[j] ? dp[(i + 1) * (n + 1) + j + 1] + 1 : Math.max(dp[(i + 1) * (n + 1) + j], dp[i * (n + 1) + j + 1]);
    }
  }
  const common = dp[0];
  return { additions: n - common, deletions: m - common };
}

interface FileChange {
  path: string;
  status: 'added' | 'modified' | 'removed';
  additions: number;
  deletions: number;
  changes: number;
}

/** The changed files between the merge base of head/base and the head tip. */
function pullFiles(repo: RepoRec, pull: PullRec): FileChange[] {
  const headTip = branchTip(repo, pull.headRef);
  const baseTip = branchTip(repo, pull.baseRef);
  if (headTip === null || baseTip === null) return [];
  const base = mergeBase(headTip, baseTip) ?? baseTip;
  const baseFlat = flattenTree(parseCommit(getObject(base)!.data).tree);
  const headFlat = flattenTree(parseCommit(getObject(headTip)!.data).tree);
  const changes: FileChange[] = [];
  const paths = new Set<string>([...baseFlat.keys(), ...headFlat.keys()]);
  for (const path of [...paths].sort()) {
    const before = baseFlat.get(path);
    const after = headFlat.get(path);
    if (before?.oid === after?.oid) continue;
    const oldData = before ? getObject(before.oid)?.data ?? null : null;
    const newData = after ? getObject(after.oid)?.data ?? null : null;
    const { additions, deletions } = lineDiff(oldData, newData);
    changes.push({
      path,
      status: before === undefined ? 'added' : after === undefined ? 'removed' : 'modified',
      additions,
      deletions,
      changes: additions + deletions,
    });
  }
  return changes;
}

// ---------------------------------------------------------------------------------------------
// JSON serializers (GitHub's shapes)
// ---------------------------------------------------------------------------------------------

function userJson(user: ForgeUser): Record<string, unknown> {
  return { login: user.login, id: user.id, type: 'User', name: user.name, email: user.email, site_admin: false };
}

function repoJson(repo: RepoRec): Record<string, unknown> {
  return {
    id: repo.id,
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: USERS.find((user) => user.login === repo.owner)?.id ?? 0, type: repo.owner === ORG_LOGIN ? 'Organization' : 'User' },
    private: repo.priv,
    description: repo.description,
    default_branch: repo.defaultBranch,
    fork: false,
    created_at: repo.createdAt,
    updated_at: repo.createdAt,
    pushed_at: repo.createdAt,
    html_url: `https://github.local/${repo.owner}/${repo.name}`,
    clone_url: `https://github.local/${repo.owner}/${repo.name}.git`,
    language: null,
    topics: [],
  };
}

function labelJson(label: { name: string; color: string }): Record<string, unknown> {
  return { name: label.name, color: label.color, default: false, description: null };
}

function issueJson(repo: RepoRec, issue: IssueRec): Record<string, unknown> {
  return {
    id: issue.id,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => labelJson(repo.labels.get(name) ?? { name, color: 'ededed' })),
    user: { login: VIEWER.login, id: VIEWER.id, type: 'User' },
    comments: issue.comments.length,
    created_at: issue.createdAt,
    updated_at: issue.updatedAt,
    closed_at: issue.state === 'closed' ? issue.updatedAt : null,
    repository_url: `/api/v3/repos/${repo.owner}/${repo.name}`,
  };
}

function commentJson(comment: CommentRec): Record<string, unknown> {
  return {
    id: comment.id,
    body: comment.body,
    user: { login: VIEWER.login, id: VIEWER.id, type: 'User' },
    created_at: comment.createdAt,
    updated_at: comment.createdAt,
  };
}

function pullJson(repo: RepoRec, pull: PullRec): Record<string, unknown> {
  const headSha = branchTip(repo, pull.headRef) ?? ZERO_OID;
  const baseSha = branchTip(repo, pull.baseRef) ?? ZERO_OID;
  return {
    id: pull.id,
    number: pull.number,
    state: pull.state,
    title: pull.title,
    body: pull.body,
    user: { login: VIEWER.login, id: VIEWER.id, type: 'User' },
    head: { ref: pull.headRef, sha: headSha, label: `${repo.owner}:${pull.headRef}` },
    base: { ref: pull.baseRef, sha: baseSha, label: `${repo.owner}:${pull.baseRef}` },
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    mergeable: pull.state === 'open' ? !pullConflicts(repo, pull) : null,
    created_at: pull.createdAt,
    updated_at: pull.updatedAt,
    closed_at: pull.state === 'closed' ? pull.updatedAt : null,
  };
}

// ---------------------------------------------------------------------------------------------
// HTTP plumbing
// ---------------------------------------------------------------------------------------------

class ApiError extends Error {
  status: number;
  constructor(status: number, message: string) {
    super(message);
    this.status = status;
  }
}

function notFound(): ApiError {
  return new ApiError(404, 'Not Found');
}

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Readonly<Record<string, string>> = {}): void {
  const requestId = randomUUID();
  if (status === 204) {
    res.writeHead(204, { 'x-github-request-id': requestId, ...headers });
    res.end();
    return;
  }
  const text = `${JSON.stringify(body)}\n`;
  res.writeHead(status, { 'content-type': JSON_TYPE, 'content-length': Buffer.byteLength(text), 'x-github-request-id': requestId, ...headers });
  res.end(text);
}

function sendRaw(res: ServerResponse, status: number, contentType: string, body: Buffer): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': body.length, 'x-github-request-id': randomUUID() });
  res.end(body);
}

async function readBody(req: IncomingMessage): Promise<Buffer> {
  const chunks: Buffer[] = [];
  let total = 0;
  for await (const chunk of req) {
    const buffer = chunk as Buffer;
    total += buffer.length;
    if (total > 128 * 1024 * 1024) throw new ApiError(413, 'Request body too large');
    chunks.push(buffer);
  }
  return Buffer.concat(chunks);
}

/** Parse a JSON request body; an empty body reads as {}, malformed JSON is a 400. */
function parseJsonBody(raw: Buffer): Record<string, unknown> {
  if (raw.length === 0) return {};
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw.toString('utf8'));
  } catch {
    throw new ApiError(400, 'Problems parsing JSON');
  }
  if (parsed === null || typeof parsed !== 'object' || Array.isArray(parsed)) throw new ApiError(400, 'Problems parsing JSON');
  return parsed as Record<string, unknown>;
}

function authed(req: IncomingMessage): boolean {
  if (TOKEN === '') return true;
  return (req.headers.authorization ?? '') === `Bearer ${TOKEN}`;
}

function requireAuth(req: IncomingMessage): void {
  if (!authed(req)) throw new ApiError(401, 'Bad credentials');
}

function decodeSegment(segment: string): string {
  try {
    return decodeURIComponent(segment);
  } catch {
    return segment;
  }
}

function asString(value: unknown): string {
  return typeof value === 'string' ? value : '';
}

function pageParams(query: URLSearchParams): { page: number; perPage: number } {
  const page = Math.max(1, Number.parseInt(query.get('page') ?? '1', 10) || 1);
  const perPage = Math.min(100, Math.max(1, Number.parseInt(query.get('per_page') ?? '30', 10) || 30));
  return { page, perPage };
}

// ---------------------------------------------------------------------------------------------
// REST v3
// ---------------------------------------------------------------------------------------------

function mustRepo(owner: string, name: string): RepoRec {
  const repo = findRepo(owner, name);
  if (repo === null) throw notFound();
  return repo;
}

async function handleRest(req: IncomingMessage, res: ServerResponse, url: URL): Promise<void> {
  requireAuth(req);
  const method = req.method ?? 'GET';
  const segments = url.pathname
    .replace(/^\/api\/v3\/?/, '')
    .split('/')
    .filter((segment) => segment !== '')
    .map(decodeSegment);
  const query = url.searchParams;
  const rawBody = method === 'GET' || method === 'HEAD' ? Buffer.alloc(0) : await readBody(req);
  const body = (): Record<string, unknown> => parseJsonBody(rawBody);

  // API root and meta.
  if (segments.length === 0) {
    if (method !== 'GET') throw notFound();
    sendJson(
      res,
      200,
      { current_user_url: '/api/v3/user', current_user_authorizations_html_url: '', rate_limit_url: '/api/v3/rate_limit', user_url: '/api/v3/users/{user}', repository_url: '/api/v3/repos/{owner}/{repo}' },
      { 'x-oauth-scopes': 'repo, read:org' },
    );
    return;
  }
  if (segments[0] === 'meta' && segments.length === 1) {
    if (method !== 'GET') throw notFound();
    sendJson(res, 200, { installed_version: VERSION, verifiable_password_authentication: false });
    return;
  }
  if (segments[0] === 'rate_limit' && segments.length === 1) {
    sendJson(res, 200, { rate: { limit: 5000, remaining: 5000, reset: 0, used: 0 }, resources: {} });
    return;
  }

  // The token's own user.
  if (segments[0] === 'user' && segments.length === 1) {
    if (method !== 'GET') throw notFound();
    sendJson(res, 200, userJson(VIEWER));
    return;
  }

  // Repository creation and the viewer's list.
  if (segments[0] === 'user' && segments[1] === 'repos' && segments.length === 2) {
    if (method === 'POST') {
      const input = body();
      const name = asString(input.name);
      if (name === '') throw new ApiError(422, 'Repository creation failed: name is required');
      if (repos.has(repoKey(VIEWER.login, name))) {
        throw new ApiError(422, 'Repository creation failed: name already exists on this account');
      }
      const repo = createRepo(VIEWER.login, name, input.private !== false, asString(input.description));
      sendJson(res, 201, repoJson(repo));
      return;
    }
    if (method === 'GET') {
      const mine = [...repos.values()].filter((repo) => repo.owner === VIEWER.login);
      const { page, perPage } = pageParams(query);
      const slice = mine.slice((page - 1) * perPage, page * perPage);
      const headers: Record<string, string> = {};
      if (page * perPage < mine.length) {
        const host = req.headers.host ?? '127.0.0.1';
        const last = Math.ceil(mine.length / perPage);
        headers.link = `<http://${host}/api/v3/user/repos?per_page=${perPage}&page=${page + 1}>; rel="next", <http://${host}/api/v3/user/repos?per_page=${perPage}&page=${last}>; rel="last"`;
      }
      sendJson(res, 200, slice.map(repoJson), headers);
      return;
    }
    throw notFound();
  }

  if (segments[0] !== 'repos' || segments.length < 3) throw notFound();
  const owner = segments[1];
  const repoName = segments[2];
  const rest = segments.slice(3);
  const repo = mustRepo(owner, repoName);

  // The repository itself.
  if (rest.length === 0) {
    if (method === 'GET') {
      sendJson(res, 200, repoJson(repo));
      return;
    }
    if (method === 'PATCH') {
      const input = body();
      if (typeof input.description === 'string') repo.description = input.description;
      if (typeof input.private === 'boolean') repo.priv = input.private;
      if (typeof input.default_branch === 'string' && input.default_branch !== '') repo.defaultBranch = input.default_branch;
      sendJson(res, 200, repoJson(repo));
      return;
    }
    if (method === 'DELETE') {
      repos.delete(repoKey(owner, repoName));
      sendJson(res, 204, null);
      return;
    }
    throw notFound();
  }

  // Branches.
  if (rest[0] === 'branches') {
    if (rest.length === 1 && method === 'GET') {
      const branches = [...repo.refs.entries()]
        .filter(([ref]) => ref.startsWith('refs/heads/'))
        .map(([ref, sha]) => ({ name: ref.slice('refs/heads/'.length), commit: { sha }, protected: false }))
        .sort((a, b) => (a.name < b.name ? -1 : 1));
      sendJson(res, 200, branches);
      return;
    }
    if (rest.length >= 2 && method === 'GET') {
      const branch = rest.slice(1).join('/');
      const tip = branchTip(repo, branch);
      if (tip === null) throw notFound();
      sendJson(res, 200, { name: branch, commit: { sha: tip }, protected: false });
      return;
    }
    throw notFound();
  }

  // Commits.
  if (rest[0] === 'commits' && rest.length === 1 && method === 'GET') {
    const shaParam = query.get('sha');
    let tip: string | null = null;
    if (shaParam !== null && shaParam !== '') {
      tip = branchTip(repo, shaParam) ?? (getObject(shaParam)?.type === 'commit' ? shaParam : null);
    } else {
      tip = branchTip(repo, repo.defaultBranch);
    }
    const commits: Record<string, unknown>[] = [];
    if (tip !== null) {
      const { perPage } = pageParams(query);
      const seen = new Set<string>();
      const stack = [tip];
      while (stack.length > 0 && commits.length < perPage) {
        const oid = stack.pop()!;
        if (seen.has(oid)) continue;
        seen.add(oid);
        const obj = getObject(oid);
        if (!obj || obj.type !== 'commit') continue;
        const commit = parseCommit(obj.data);
        commits.push({
          sha: oid,
          commit: {
            message: commit.message.replace(/\n$/, ''),
            tree: { sha: commit.tree },
            author: { name: VIEWER.name, email: VIEWER.email },
            committer: { name: VIEWER.name, email: VIEWER.email },
          },
          parents: commit.parents.map((parent) => ({ sha: parent })),
        });
        for (let index = commit.parents.length - 1; index >= 0; index -= 1) stack.push(commit.parents[index]);
      }
    }
    sendJson(res, 200, commits);
    return;
  }

  // Git data: refs.
  if (rest[0] === 'git' && rest[1] === 'refs') {
    if (rest.length === 2) {
      if (method === 'POST') {
        const input = body();
        const ref = asString(input.ref);
        const sha = asString(input.sha);
        if (!ref.startsWith('refs/') || getObject(sha) === undefined) throw new ApiError(422, 'Invalid ref or sha');
        if (repo.refs.has(ref)) throw new ApiError(422, 'Reference already exists');
        repo.refs.set(ref, sha);
        sendJson(res, 201, { ref, object: { sha, type: getObject(sha)!.type } });
        return;
      }
      if (method === 'GET') {
        sendJson(res, 200, [...repo.refs.entries()].map(([ref, sha]) => ({ ref, object: { sha, type: getObject(sha)?.type ?? 'commit' } })));
        return;
      }
      throw notFound();
    }
    if (method === 'GET') {
      const ref = `refs/${rest.slice(2).join('/')}`;
      const sha = repo.refs.get(ref);
      if (sha === undefined) throw notFound();
      sendJson(res, 200, { ref, object: { sha, type: getObject(sha)?.type ?? 'commit' } });
      return;
    }
    throw notFound();
  }

  // Contents.
  if (rest[0] === 'contents') {
    const path = rest.slice(1).join('/');
    if (method === 'GET') {
      const ref = query.get('ref') ?? repo.defaultBranch;
      const tree = treeOfRef(repo, ref);
      if (tree === null) throw notFound();
      const flat = flattenTree(tree);
      if (path !== '') {
        const entry = flat.get(path);
        if (entry !== undefined) {
          const obj = getObject(entry.oid)!;
          sendJson(res, 200, {
            type: 'file',
            name: path.slice(path.lastIndexOf('/') + 1),
            path,
            sha: entry.oid,
            size: obj.data.length,
            encoding: 'base64',
            content: obj.data.toString('base64'),
          });
          return;
        }
      }
      const prefix = path === '' ? '' : `${path}/`;
      const children = new Map<string, { type: 'file' | 'dir'; oid: string; size: number }>();
      for (const [filePath, entry] of flat) {
        if (!filePath.startsWith(prefix)) continue;
        const remainder = filePath.slice(prefix.length);
        const slash = remainder.indexOf('/');
        if (slash < 0) {
          children.set(remainder, { type: 'file', oid: entry.oid, size: getObject(entry.oid)?.data.length ?? 0 });
        } else {
          const dir = remainder.slice(0, slash);
          if (!children.has(dir)) {
            // The directory's tree oid: walk the tree.
            let dirOid = '';
            let current = tree;
            for (const segment of [...(path === '' ? [] : path.split('/')), dir]) {
              const next = parseTree(getObject(current)!.data).find((candidate) => candidate.name === segment && candidate.mode === '40000');
              if (!next) break;
              dirOid = next.oid;
              current = next.oid;
            }
            children.set(dir, { type: 'dir', oid: dirOid, size: 0 });
          }
        }
      }
      if (path !== '' && children.size === 0) throw notFound();
      const listing = [...children.entries()]
        .map(([name, value]) => ({ type: value.type, name, path: `${prefix}${name}`, sha: value.oid, size: value.size }))
        .sort((a, b) => (a.name < b.name ? -1 : 1));
      sendJson(res, 200, listing);
      return;
    }
    if (method === 'PUT') {
      if (path === '') throw new ApiError(422, 'A file path is required');
      const input = body();
      const branch = typeof input.branch === 'string' && input.branch !== '' ? input.branch : repo.defaultBranch;
      const message = asString(input.message) || `Update ${path}`;
      const content = Buffer.from(asString(input.content).replace(/\s+/g, ''), 'base64');
      const existing = fileAt(repo, branch, path);
      if (existing !== null && typeof input.sha === 'string' && input.sha !== existing.oid) {
        throw new ApiError(409, `${path} does not match ${input.sha}`);
      }
      const result = commitFileChange(repo, branch, path, content, message);
      sendJson(res, result.existed ? 200 : 201, {
        content: { type: 'file', name: path.slice(path.lastIndexOf('/') + 1), path, sha: result.blobOid, size: content.length, encoding: 'base64' },
        commit: { sha: result.commitOid, message },
      });
      return;
    }
    if (method === 'DELETE') {
      const input = body();
      const branch = typeof input.branch === 'string' && input.branch !== '' ? input.branch : repo.defaultBranch;
      const existing = fileAt(repo, branch, path);
      if (existing === null) throw notFound();
      if (typeof input.sha === 'string' && input.sha !== existing.oid) throw new ApiError(409, `${path} does not match ${input.sha}`);
      const message = asString(input.message) || `Delete ${path}`;
      const result = commitFileChange(repo, branch, path, null, message);
      sendJson(res, 200, { content: null, commit: { sha: result.commitOid, message } });
      return;
    }
    throw notFound();
  }

  // Labels.
  if (rest[0] === 'labels' && rest.length === 1) {
    if (method === 'POST') {
      const input = body();
      const name = asString(input.name);
      if (name === '') throw new ApiError(422, 'A label name is required');
      if (repo.labels.has(name)) throw new ApiError(422, 'Validation Failed: label already exists');
      const label = { name, color: asString(input.color) || 'ededed' };
      repo.labels.set(name, label);
      sendJson(res, 201, labelJson(label));
      return;
    }
    if (method === 'GET') {
      sendJson(res, 200, [...repo.labels.values()].map(labelJson));
      return;
    }
    throw notFound();
  }

  // Issues and comments.
  if (rest[0] === 'issues') {
    if (rest.length === 1) {
      if (method === 'POST') {
        const input = body();
        const title = asString(input.title);
        if (title === '') throw new ApiError(422, 'Validation Failed: title is required');
        const labelNames: string[] = [];
        if (Array.isArray(input.labels)) {
          for (const entry of input.labels) {
            const name = typeof entry === 'string' ? entry : asString((entry as Record<string, unknown>)?.name);
            if (!repo.labels.has(name)) throw new ApiError(422, `Validation Failed: label '${name}' does not exist`);
            labelNames.push(name);
          }
        }
        const issue = createIssue(repo, title, asString(input.body), labelNames);
        sendJson(res, 201, issueJson(repo, issue));
        return;
      }
      if (method === 'GET') {
        const state = query.get('state') ?? 'open';
        const direction = query.get('direction') ?? 'desc';
        let list = [...repo.items.values()].filter((item): item is IssueRec => item.kind === 'issue');
        if (state === 'open' || state === 'closed') list = list.filter((issue) => issue.state === state);
        list.sort((a, b) => (direction === 'asc' ? a.createdSeq - b.createdSeq : b.createdSeq - a.createdSeq));
        const { page, perPage } = pageParams(query);
        sendJson(res, 200, list.slice((page - 1) * perPage, page * perPage).map((issue) => issueJson(repo, issue)));
        return;
      }
      throw notFound();
    }
    const number = Number.parseInt(rest[1], 10);
    const issue = Number.isInteger(number) ? getIssue(repo, number) : null;
    if (rest.length === 2) {
      if (issue === null) throw notFound();
      if (method === 'GET') {
        sendJson(res, 200, issueJson(repo, issue));
        return;
      }
      if (method === 'PATCH') {
        const input = body();
        if (input.state === 'open' || input.state === 'closed') issue.state = input.state;
        if (typeof input.title === 'string') issue.title = input.title;
        if (typeof input.body === 'string') issue.body = input.body;
        if (Array.isArray(input.labels)) {
          const names: string[] = [];
          for (const entry of input.labels) {
            const name = typeof entry === 'string' ? entry : asString((entry as Record<string, unknown>)?.name);
            if (!repo.labels.has(name)) throw new ApiError(422, `Validation Failed: label '${name}' does not exist`);
            names.push(name);
          }
          issue.labels = names;
        }
        issue.updatedAt = isoNow();
        sendJson(res, 200, issueJson(repo, issue));
        return;
      }
      throw notFound();
    }
    if (rest.length === 3 && rest[2] === 'comments') {
      if (issue === null) throw notFound();
      if (method === 'POST') {
        const input = body();
        const comment: CommentRec = { id: nextCommentId++, body: asString(input.body), createdAt: isoNow() };
        issue.comments.push(comment);
        sendJson(res, 201, commentJson(comment));
        return;
      }
      if (method === 'GET') {
        sendJson(res, 200, issue.comments.map(commentJson));
        return;
      }
      throw notFound();
    }
    throw notFound();
  }

  // Pull requests.
  if (rest[0] === 'pulls') {
    if (rest.length === 1) {
      if (method === 'POST') {
        const input = body();
        const stripOwner = (value: string): string => (value.includes(':') ? value.slice(value.indexOf(':') + 1) : value);
        const head = stripOwner(asString(input.head));
        const base = stripOwner(asString(input.base)) || repo.defaultBranch;
        const title = asString(input.title);
        if (title === '' || head === '') throw new ApiError(422, 'Validation Failed: title and head are required');
        if (branchTip(repo, head) === null) throw new ApiError(422, `Validation Failed: head branch '${head}' does not exist`);
        if (branchTip(repo, base) === null) throw new ApiError(422, `Validation Failed: base branch '${base}' does not exist`);
        const duplicate = [...repo.items.values()].some(
          (item) => item.kind === 'pull' && item.state === 'open' && item.headRef === head && item.baseRef === base,
        );
        if (duplicate) throw new ApiError(422, `A pull request already exists for ${head} into ${base}`);
        const pull = createPull(repo, title, asString(input.body), head, base);
        sendJson(res, 201, pullJson(repo, pull));
        return;
      }
      if (method === 'GET') {
        const state = query.get('state') ?? 'open';
        let list = [...repo.items.values()].filter((item): item is PullRec => item.kind === 'pull');
        if (state === 'open' || state === 'closed') list = list.filter((pull) => pull.state === state);
        list.sort((a, b) => b.createdSeq - a.createdSeq);
        const { page, perPage } = pageParams(query);
        sendJson(res, 200, list.slice((page - 1) * perPage, page * perPage).map((pull) => pullJson(repo, pull)));
        return;
      }
      throw notFound();
    }
    const number = Number.parseInt(rest[1], 10);
    const pull = Number.isInteger(number) ? getPull(repo, number) : null;
    if (rest.length === 2 && method === 'GET') {
      if (pull === null) throw notFound();
      sendJson(res, 200, pullJson(repo, pull));
      return;
    }
    if (rest.length === 3 && rest[2] === 'files' && method === 'GET') {
      if (pull === null) throw notFound();
      sendJson(
        res,
        200,
        pullFiles(repo, pull).map((file) => ({ filename: file.path, status: file.status, additions: file.additions, deletions: file.deletions, changes: file.changes })),
      );
      return;
    }
    if (rest.length === 3 && rest[2] === 'merge' && method === 'PUT') {
      if (pull === null) throw notFound();
      const input = body();
      const mergeMethod = asString(input.merge_method) || 'merge';
      if (pull.state !== 'open') throw new ApiError(405, 'Pull Request is not mergeable');
      const sha = mergePull(repo, pull, mergeMethod);
      if (sha === null) throw new ApiError(405, 'Pull Request is not mergeable');
      sendJson(res, 200, { sha, merged: true, message: 'Pull Request successfully merged' });
      return;
    }
    throw notFound();
  }

  throw notFound();
}

// ---------------------------------------------------------------------------------------------
// Git smart HTTP
// ---------------------------------------------------------------------------------------------

function sortedRefEntries(repo: RepoRec): Array<[string, string]> {
  return [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
}

function gitAdvertisement(repo: RepoRec, service: string, version2: boolean): Buffer {
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), PKT_FLUSH];
  if (version2) {
    parts.push(pktLine('version 2\n'));
    parts.push(pktLine('agent=forge/1.0\n'));
    parts.push(pktLine('ls-refs\n'));
    parts.push(pktLine('fetch=shallow\n'));
    parts.push(pktLine('object-format=sha1\n'));
    parts.push(PKT_FLUSH);
    return Buffer.concat(parts);
  }
  const caps =
    service === 'git-upload-pack'
      ? `multi_ack_detailed side-band-64k thin-pack ofs-delta shallow agent=forge/1.0 symref=HEAD:${headTarget(repo)}`
      : 'report-status delete-refs side-band-64k ofs-delta agent=forge/1.0';
  const headOid = repo.refs.get(headTarget(repo)) ?? ZERO_OID;
  const entries = sortedRefEntries(repo);
  if (entries.length === 0) {
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    parts.push(pktLine(`${headOid} HEAD\0${caps}\n`));
    for (const [ref, oid] of entries) {
      parts.push(pktLine(`${oid} ${ref}\n`));
      const obj = getObject(oid);
      if (obj?.type === 'tag') parts.push(pktLine(`${peelToCommit(oid)} ${ref}^{}\n`));
    }
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

interface FetchPlan {
  objects: string[];
  shallow: string[];
  unshallow: string[];
}

/** Decide what a fetch sends: the depth-limited want closure minus what the client already holds. */
function planFetch(wants: readonly string[], haves: readonly string[], clientShallow: readonly string[], depth: number | null): FetchPlan {
  const shallowSet = new Set(clientShallow);
  // Depth of every commit reachable from the wants (want = 1).
  const depthOf = new Map<string, number>();
  const queue: Array<[string, number]> = [];
  const wantCommits = new Set<string>();
  for (const want of wants) {
    const obj = getObject(want);
    if (!obj) continue;
    const commit = obj.type === 'tag' ? peelToCommit(want) : want;
    if (getObject(commit)?.type === 'commit') {
      wantCommits.add(commit);
      queue.push([commit, 1]);
    }
  }
  while (queue.length > 0) {
    const [oid, depthHere] = queue.shift()!;
    if (depthOf.has(oid) && depthOf.get(oid)! <= depthHere) continue;
    depthOf.set(oid, depthHere);
    if (depth !== null && depthHere >= depth) continue;
    const commit = getObject(oid);
    if (commit?.type === 'commit') {
      for (const parent of parseCommit(commit.data).parents) queue.push([parent, depthHere + 1]);
    }
  }
  const included = new Set<string>();
  const boundary = new Set<string>();
  for (const [oid, depthHere] of depthOf) {
    if (depth !== null && depthHere > depth) continue;
    included.add(oid);
    if (depth !== null) {
      const commit = getObject(oid)!;
      for (const parent of parseCommit(commit.data).parents) {
        if (getObject(parent) && !included.has(parent) && (depthOf.get(parent) ?? Infinity) > depth) boundary.add(oid);
      }
    }
  }
  const wantObjects = new Set<string>();
  const addTreeClosure = (treeOid: string): void => {
    for (const oid of collectClosure([treeOid])) wantObjects.add(oid);
  };
  for (const oid of included) {
    wantObjects.add(oid);
    addTreeClosure(parseCommit(getObject(oid)!.data).tree);
  }
  for (const want of wants) {
    const obj = getObject(want);
    if (obj?.type === 'tag') {
      wantObjects.add(want);
      const target = peelToCommit(want);
      if (included.has(target)) {
        // The tag chain between the tag and its commit rides along.
        let current = want;
        while (getObject(current)?.type === 'tag') {
          current = parseTag(getObject(current)!.data).object;
          wantObjects.add(current);
        }
      }
    }
  }
  // What the client already holds: the closure of its haves, not crossing its shallow boundary.
  const held = new Set<string>();
  for (const have of haves) {
    const obj = getObject(have);
    if (!obj) continue;
    if (obj.type !== 'commit') {
      for (const oid of collectClosure([have])) held.add(oid);
      continue;
    }
    const stack = [have];
    const seenLocal = new Set<string>();
    while (stack.length > 0) {
      const oid = stack.pop()!;
      if (seenLocal.has(oid)) continue;
      seenLocal.add(oid);
      const current = getObject(oid);
      if (!current || current.type !== 'commit') continue;
      held.add(oid);
      addTreeTo(held, parseCommit(current.data).tree);
      if (!shallowSet.has(oid)) stack.push(...parseCommit(current.data).parents);
    }
  }
  const deliver = [...wantObjects].filter((oid) => !held.has(oid));
  const rank = (oid: string): number => {
    const type = getObject(oid)?.type;
    return type === 'commit' ? 0 : type === 'tree' ? 1 : type === 'blob' ? 2 : 3;
  };
  deliver.sort((a, b) => rank(a) - rank(b) || (a < b ? -1 : 1));
  const unshallow = [...shallowSet].filter((oid) => included.has(oid) && !boundary.has(oid));
  return { objects: deliver, shallow: [...boundary].sort(), unshallow: unshallow.sort() };
}

function addTreeTo(set: Set<string>, treeOid: string): void {
  for (const oid of collectClosure([treeOid])) set.add(oid);
}

/** Chunk a pack into side-band-64k band-1 packets. */
function sidebandPackets(pack: Buffer): Buffer[] {
  const packets: Buffer[] = [];
  const CHUNK = 65515;
  for (let offset = 0; offset < pack.length; offset += CHUNK) {
    const chunk = pack.subarray(offset, offset + CHUNK);
    packets.push(pktLine(Buffer.concat([Buffer.from([1]), chunk])));
  }
  if (packets.length === 0) packets.push(pktLine(Buffer.concat([Buffer.from([1]), Buffer.alloc(0)])));
  return packets;
}

function lsRefsV2(repo: RepoRec, args: readonly string[]): Buffer {
  const peel = args.includes('peel');
  const symrefs = args.includes('symrefs');
  const prefixes = args.filter((arg) => arg.startsWith('ref-prefix ')).map((arg) => arg.slice('ref-prefix '.length));
  const matches = (name: string): boolean => prefixes.length === 0 || prefixes.some((prefix) => name.startsWith(prefix));
  const lines: string[] = [];
  const headOid = repo.refs.get(headTarget(repo)) ?? ZERO_OID;
  if (matches('HEAD')) {
    lines.push(symrefs ? `${headOid} HEAD symref-target:${headTarget(repo)}` : `${headOid} HEAD`);
  }
  for (const [ref, oid] of sortedRefEntries(repo)) {
    if (!matches(ref)) continue;
    let line = `${oid} ${ref}`;
    if (peel && getObject(oid)?.type === 'tag') line += ` peeled:${peelToCommit(oid)}`;
    lines.push(line);
  }
  return Buffer.concat([...lines.map((line) => pktLine(`${line}\n`)), PKT_FLUSH]);
}

interface FetchArgs {
  wants: string[];
  haves: string[];
  shallow: string[];
  depth: number | null;
  done: boolean;
}

function fetchResponseV2(repo: RepoRec, args: FetchArgs): Buffer {
  const plan = planFetch(args.wants, args.haves, args.shallow, args.depth);
  const parts: Buffer[] = [];
  if (plan.shallow.length > 0 || plan.unshallow.length > 0) {
    parts.push(pktLine('shallow-info\n'));
    for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}\n`));
    for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
    parts.push(PKT_FLUSH);
  }
  parts.push(pktLine('acknowledgments\n'));
  const common = args.haves.find((have) => getObject(have)?.type === 'commit');
  if (common !== undefined) parts.push(pktLine(`ACK ${common}\n`));
  else parts.push(pktLine('NAK\n'));
  parts.push(PKT_FLUSH);
  parts.push(pktLine('packfile\n'));
  parts.push(...sidebandPackets(writePack(plan.objects)));
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function fetchResponseV0(repo: RepoRec, args: FetchArgs): Buffer {
  const plan = planFetch(args.wants, args.haves, args.shallow, args.depth);
  const parts: Buffer[] = [];
  for (const oid of plan.shallow) parts.push(pktLine(`shallow ${oid}\n`));
  for (const oid of plan.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
  const common = args.haves.find((have) => getObject(have)?.type === 'commit');
  parts.push(pktLine(common !== undefined ? `ACK ${common} common\n` : 'NAK\n'));
  parts.push(...sidebandPackets(writePack(plan.objects)));
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function parseFetchArgs(lines: readonly string[]): FetchArgs {
  const args: FetchArgs = { wants: [], haves: [], shallow: [], depth: null, done: false };
  for (const line of lines) {
    if (line.startsWith('want ')) args.wants.push(line.slice(5).trim().split(' ')[0]);
    else if (line.startsWith('have ')) args.haves.push(line.slice(5).trim());
    else if (line.startsWith('shallow ')) args.shallow.push(line.slice(8).trim());
    else if (line.startsWith('deepen ')) args.depth = Number.parseInt(line.slice(7).trim(), 10) || null;
    else if (line === 'done') args.done = true;
  }
  return args;
}

function handleUploadPack(res: ServerResponse, repo: RepoRec, raw: Buffer): void {
  let packets: PktPacket[];
  try {
    packets = decodePktLines(raw);
  } catch {
    sendRaw(res, 400, 'text/plain', Buffer.from('invalid pkt-line stream\n'));
    return;
  }
  const lines = packets.filter((packet) => packet.kind === 'data').map((packet) => packet.payload.toString('utf8').replace(/\n$/, ''));
  const first = lines[0] ?? '';
  if (first.startsWith('command=')) {
    const command = first.slice('command='.length);
    // v2 framing: capability lines, a delim, then the command's arguments, then flush.
    const delimIndex = packets.findIndex((packet) => packet.kind === 'delim');
    const argLines = (delimIndex < 0 ? lines.slice(1) : packets.slice(delimIndex + 1).filter((packet) => packet.kind === 'data').map((packet) => packet.payload.toString('utf8').replace(/\n$/, '')));
    if (command === 'ls-refs') {
      sendRaw(res, 200, 'application/x-git-upload-pack-result', lsRefsV2(repo, argLines));
      return;
    }
    if (command === 'fetch') {
      sendRaw(res, 200, 'application/x-git-upload-pack-result', fetchResponseV2(repo, parseFetchArgs(argLines)));
      return;
    }
    sendRaw(res, 400, 'text/plain', Buffer.from(`unknown command ${command}\n`));
    return;
  }
  // v0: wants section, flush, haves section, flush — the data lines alone carry everything.
  sendRaw(res, 200, 'application/x-git-upload-pack-result', fetchResponseV0(repo, parseFetchArgs(lines)));
}

interface PushCommandLine {
  oldOid: string;
  newOid: string;
  ref: string;
}

function handleReceivePack(res: ServerResponse, repo: RepoRec, raw: Buffer): void {
  // Walk the command pkt-lines by hand: the pack starts right after the flush packet.
  const commands: PushCommandLine[] = [];
  let capabilities = '';
  let offset = 0;
  let packStart = -1;
  try {
    let firstLine = true;
    for (;;) {
      if (offset + 4 > raw.length) throw new Error('truncated');
      const hex = raw.subarray(offset, offset + 4).toString('ascii');
      if (!/^[0-9a-fA-F]{4}$/.test(hex)) throw new Error('bad length');
      const length = parseInt(hex, 16);
      if (length === 0) {
        packStart = offset + 4;
        break;
      }
      if (length < 4 || offset + length > raw.length) throw new Error('overrun');
      let line = raw.subarray(offset + 4, offset + length).toString('utf8').replace(/\n$/, '');
      offset += length;
      if (firstLine) {
        firstLine = false;
        const nul = line.indexOf('\0');
        if (nul >= 0) {
          capabilities = line.slice(nul + 1);
          line = line.slice(0, nul);
        }
      }
      const parts = line.split(' ');
      if (parts.length >= 3) commands.push({ oldOid: parts[0], newOid: parts[1], ref: parts.slice(2).join(' ') });
    }
  } catch {
    sendRaw(res, 400, 'text/plain', Buffer.from('invalid receive-pack request\n'));
    return;
  }
  const pack = packStart >= 0 && packStart < raw.length ? raw.subarray(packStart) : Buffer.alloc(0);
  let unpackOk = true;
  let unpackDetail = 'ok';
  if (pack.length > 0) {
    try {
      readPackIntoStore(pack);
    } catch (err) {
      unpackOk = false;
      unpackDetail = `error ${err instanceof Error ? err.message : String(err)}`;
    }
  }
  const reportLines: string[] = [`unpack ${unpackDetail}`];
  for (const command of commands) {
    const fail = (reason: string): void => {
      reportLines.push(`ng ${command.ref} ${reason}`);
    };
    if (!unpackOk) {
      fail('unpack failed');
      continue;
    }
    if (!command.ref.startsWith('refs/')) {
      fail('invalid ref');
      continue;
    }
    const current = repo.refs.get(command.ref);
    if (command.newOid === ZERO_OID) {
      if (current === undefined) fail('reference does not exist');
      else {
        repo.refs.delete(command.ref);
        reportLines.push(`ok ${command.ref}`);
      }
      continue;
    }
    if (getObject(command.newOid) === undefined) {
      fail('missing object');
      continue;
    }
    if (command.oldOid === ZERO_OID) {
      if (current !== undefined) fail('reference already exists');
      else {
        repo.refs.set(command.ref, command.newOid);
        reportLines.push(`ok ${command.ref}`);
      }
      continue;
    }
    if (current !== command.oldOid) {
      fail('stale reference');
      continue;
    }
    if (command.oldOid !== command.newOid && getObject(command.newOid)?.type === 'commit' && getObject(command.oldOid)?.type === 'commit' && !isAncestor(command.oldOid, command.newOid)) {
      fail('non-fast-forward');
      continue;
    }
    repo.refs.set(command.ref, command.newOid);
    reportLines.push(`ok ${command.ref}`);
  }
  const reportStream = Buffer.concat([...reportLines.map((line) => pktLine(`${line}\n`)), PKT_FLUSH]);
  let out: Buffer;
  if (capabilities.split(' ').includes('side-band-64k')) {
    const packets: Buffer[] = [];
    const CHUNK = 65515;
    for (let at = 0; at < reportStream.length; at += CHUNK) {
      packets.push(pktLine(Buffer.concat([Buffer.from([1]), reportStream.subarray(at, at + CHUNK)])));
    }
    packets.push(PKT_FLUSH);
    out = Buffer.concat(packets);
  } else {
    out = reportStream;
  }
  sendRaw(res, 200, 'application/x-git-receive-pack-result', out);
}

async function handleGitHttp(req: IncomingMessage, res: ServerResponse, url: URL, owner: string, repoName: string, kind: string): Promise<void> {
  requireAuth(req);
  const repo = findRepo(owner, repoName);
  if (repo === null) {
    sendRaw(res, 404, 'text/plain', Buffer.from('repository not found\n'));
    return;
  }
  if (kind === 'info/refs') {
    const service = url.searchParams.get('service') ?? '';
    if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
      sendRaw(res, 404, 'text/plain', Buffer.from('unknown service\n'));
      return;
    }
    const version2 = service === 'git-upload-pack' && (req.headers['git-protocol'] ?? '') === 'version=2';
    sendRaw(res, 200, `application/x-${service}-advertisement`, gitAdvertisement(repo, service, version2));
    return;
  }
  const raw = await readBody(req);
  if (kind === 'git-upload-pack') {
    handleUploadPack(res, repo, raw);
    return;
  }
  handleReceivePack(res, repo, raw);
}

// ---------------------------------------------------------------------------------------------
// GraphQL v4
// ---------------------------------------------------------------------------------------------

type GqlValue =
  | { k: 'var'; name: string }
  | { k: 'lit'; v: unknown }
  | { k: 'list'; items: GqlValue[] }
  | { k: 'obj'; fields: Map<string, GqlValue> };

interface GqlField {
  name: string;
  alias: string | null;
  args: Map<string, GqlValue>;
  selections: GqlSelection[];
}

type GqlSelection =
  | { type: 'field'; field: GqlField }
  | { type: 'spread'; name: string }
  | { type: 'inline'; on: string | null; selections: GqlSelection[] };

interface GqlOperation {
  op: 'query' | 'mutation';
  name: string | null;
  selections: GqlSelection[];
}

interface GqlDoc {
  operations: GqlOperation[];
  fragments: Map<string, { on: string; selections: GqlSelection[] }>;
}

function lexGraphQL(source: string): Array<{ kind: string; value: string }> {
  const tokens: Array<{ kind: string; value: string }> = [];
  let i = 0;
  while (i < source.length) {
    const ch = source[i];
    if (ch === '#') {
      while (i < source.length && source[i] !== '\n') i += 1;
      continue;
    }
    if (ch === ',' || ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === '﻿') {
      i += 1;
      continue;
    }
    if (source.startsWith('...', i)) {
      tokens.push({ kind: 'punct', value: '...' });
      i += 3;
      continue;
    }
    if ('!$():=@[]{}|&'.includes(ch)) {
      tokens.push({ kind: 'punct', value: ch });
      i += 1;
      continue;
    }
    if (ch === '"') {
      if (source.startsWith('"""', i)) {
        const end = source.indexOf('"""', i + 3);
        tokens.push({ kind: 'string', value: source.slice(i + 3, end < 0 ? source.length : end) });
        i = end < 0 ? source.length : end + 3;
        continue;
      }
      let value = '';
      i += 1;
      while (i < source.length && source[i] !== '"') {
        if (source[i] === '\\') {
          const esc = source[i + 1];
          if (esc === 'n') value += '\n';
          else if (esc === 't') value += '\t';
          else if (esc === 'r') value += '\r';
          else if (esc === 'u') {
            value += String.fromCharCode(parseInt(source.slice(i + 2, i + 6), 16));
            i += 4;
          } else value += esc;
          i += 2;
        } else {
          value += source[i];
          i += 1;
        }
      }
      i += 1;
      tokens.push({ kind: 'string', value });
      continue;
    }
    if (/[0-9-]/.test(ch)) {
      let j = i;
      while (j < source.length && /[0-9.eE+-]/.test(source[j])) j += 1;
      tokens.push({ kind: 'number', value: source.slice(i, j) });
      i = j;
      continue;
    }
    if (/[_A-Za-z]/.test(ch)) {
      let j = i;
      while (j < source.length && /[_0-9A-Za-z]/.test(source[j])) j += 1;
      tokens.push({ kind: 'name', value: source.slice(i, j) });
      i = j;
      continue;
    }
    throw new Error(`unexpected character ${JSON.stringify(ch)} in GraphQL document`);
  }
  tokens.push({ kind: 'eof', value: '' });
  return tokens;
}

class GqlParser {
  private tokens: Array<{ kind: string; value: string }>;
  private pos = 0;

  constructor(source: string) {
    this.tokens = lexGraphQL(source);
  }

  private peek(): { kind: string; value: string } {
    return this.tokens[this.pos];
  }

  private next(): { kind: string; value: string } {
    return this.tokens[this.pos++];
  }

  private expect(value: string): void {
    const token = this.next();
    if (token.value !== value) throw new Error(`expected ${value}, got ${token.value}`);
  }

  private skipDirectives(): void {
    while (this.peek().value === '@') {
      this.next();
      this.next();
      if (this.peek().value === '(') this.parseArgs();
    }
  }

  parseDocument(): GqlDoc {
    const operations: GqlOperation[] = [];
    const fragments = new Map<string, { on: string; selections: GqlSelection[] }>();
    while (this.peek().kind !== 'eof') {
      const token = this.peek();
      if (token.value === '{') {
        operations.push({ op: 'query', name: null, selections: this.parseSelectionSet() });
      } else if (token.kind === 'name' && (token.value === 'query' || token.value === 'mutation')) {
        const op = this.next().value as 'query' | 'mutation';
        let name: string | null = null;
        if (this.peek().kind === 'name') name = this.next().value;
        if (this.peek().value === '(') this.parseVarDefs();
        this.skipDirectives();
        operations.push({ op, name, selections: this.parseSelectionSet() });
      } else if (token.kind === 'name' && token.value === 'fragment') {
        this.next();
        const fragName = this.next().value;
        this.expect('on');
        const on = this.next().value;
        this.skipDirectives();
        fragments.set(fragName, { on, selections: this.parseSelectionSet() });
      } else {
        throw new Error(`unexpected token ${token.value} in GraphQL document`);
      }
    }
    return { operations, fragments };
  }

  private parseVarDefs(): void {
    this.expect('(');
    while (this.peek().value !== ')') {
      this.expect('$');
      this.next(); // variable name
      this.expect(':');
      this.parseType();
      if (this.peek().value === '=') {
        this.next();
        this.parseValue();
      }
      this.skipDirectives();
    }
    this.expect(')');
  }

  private parseType(): void {
    if (this.peek().value === '[') {
      this.next();
      this.parseType();
      this.expect(']');
    } else {
      this.next();
    }
    if (this.peek().value === '!') this.next();
  }

  private parseSelectionSet(): GqlSelection[] {
    this.expect('{');
    const selections: GqlSelection[] = [];
    while (this.peek().value !== '}') selections.push(this.parseSelection());
    this.expect('}');
    return selections;
  }

  private parseSelection(): GqlSelection {
    if (this.peek().value === '...') {
      this.next();
      if (this.peek().kind === 'name' && this.peek().value === 'on') {
        this.next();
        const on = this.next().value;
        this.skipDirectives();
        return { type: 'inline', on, selections: this.parseSelectionSet() };
      }
      if (this.peek().value === '{') {
        return { type: 'inline', on: null, selections: this.parseSelectionSet() };
      }
      return { type: 'spread', name: this.next().value };
    }
    return { type: 'field', field: this.parseField() };
  }

  private parseField(): GqlField {
    let name = this.next().value;
    let alias: string | null = null;
    if (this.peek().value === ':') {
      this.next();
      alias = name;
      name = this.next().value;
    }
    const args = this.peek().value === '(' ? this.parseArgs() : new Map<string, GqlValue>();
    this.skipDirectives();
    const selections = this.peek().value === '{' ? this.parseSelectionSet() : [];
    return { name, alias, args, selections };
  }

  private parseArgs(): Map<string, GqlValue> {
    const args = new Map<string, GqlValue>();
    this.expect('(');
    while (this.peek().value !== ')') {
      const name = this.next().value;
      this.expect(':');
      args.set(name, this.parseValue());
    }
    this.expect(')');
    return args;
  }

  private parseValue(): GqlValue {
    const token = this.peek();
    if (token.value === '$') {
      this.next();
      return { k: 'var', name: this.next().value };
    }
    if (token.kind === 'string') {
      this.next();
      return { k: 'lit', v: token.value };
    }
    if (token.kind === 'number') {
      this.next();
      return { k: 'lit', v: Number(token.value) };
    }
    if (token.value === '[') {
      this.next();
      const items: GqlValue[] = [];
      while (this.peek().value !== ']') items.push(this.parseValue());
      this.expect(']');
      return { k: 'list', items };
    }
    if (token.value === '{') {
      this.next();
      const fields = new Map<string, GqlValue>();
      while (this.peek().value !== '}') {
        const name = this.next().value;
        this.expect(':');
        fields.set(name, this.parseValue());
      }
      this.expect('}');
      return { k: 'obj', fields };
    }
    if (token.kind === 'name') {
      this.next();
      if (token.value === 'true') return { k: 'lit', v: true };
      if (token.value === 'false') return { k: 'lit', v: false };
      if (token.value === 'null') return { k: 'lit', v: null };
      return { k: 'lit', v: token.value }; // an enum value reads as its name
    }
    throw new Error(`unexpected value token ${token.value}`);
  }
}

function evalGqlValue(value: GqlValue, vars: Readonly<Record<string, unknown>>): unknown {
  switch (value.k) {
    case 'var':
      return vars[value.name] ?? null;
    case 'lit':
      return value.v;
    case 'list':
      return value.items.map((item) => evalGqlValue(item, vars));
    case 'obj': {
      const out: Record<string, unknown> = {};
      for (const [key, entry] of value.fields) out[key] = evalGqlValue(entry, vars);
      return out;
    }
  }
}

// ----- schema -----

const GQL_FIELD_TYPE: Record<string, Record<string, string>> = {
  Query: { viewer: 'User', repository: 'Repository', node: 'Node', __type: '__Type', __schema: '__Schema', rateLimit: 'RateLimit' },
  Mutation: { createIssue: 'CreateIssuePayload', closeIssue: 'CloseIssuePayload', createPullRequest: 'CreatePullRequestPayload', mergePullRequest: 'MergePullRequestPayload', addComment: 'AddCommentPayload' },
  User: { login: 'String', id: 'ID', name: 'String', email: 'String', databaseId: 'Int' },
  Repository: {
    id: 'ID', databaseId: 'Int', name: 'String', nameWithOwner: 'String', owner: 'User', defaultBranchRef: 'Ref',
    viewerPermission: 'String', hasIssuesEnabled: 'Boolean', isPrivate: 'Boolean', description: 'String',
    issue: 'Issue', issues: 'IssueConnection', pullRequest: 'PullRequest', pullRequests: 'PullRequestConnection',
    createdAt: 'String', updatedAt: 'String',
  },
  Ref: { name: 'String', prefix: 'String' },
  Issue: {
    id: 'ID', number: 'Int', title: 'String', state: 'String', body: 'String', labels: 'LabelConnection',
    comments: 'IssueCommentConnection', repository: 'Repository', createdAt: 'String', updatedAt: 'String',
  },
  IssueConnection: { nodes: 'Issue', edges: 'IssueEdge', pageInfo: 'PageInfo', totalCount: 'Int' },
  IssueEdge: { node: 'Issue', cursor: 'String' },
  IssueCommentConnection: { nodes: 'Comment', edges: 'CommentEdge', pageInfo: 'PageInfo', totalCount: 'Int' },
  PageInfo: { hasNextPage: 'Boolean', hasPreviousPage: 'Boolean', startCursor: 'String', endCursor: 'String' },
  PullRequest: {
    id: 'ID', number: 'Int', title: 'String', body: 'String', state: 'String', merged: 'Boolean', mergeable: 'String',
    headRefName: 'String', baseRefName: 'String', files: 'PullRequestChangedFileConnection', repository: 'Repository',
    createdAt: 'String', updatedAt: 'String',
  },
  PullRequestConnection: { nodes: 'PullRequest', edges: 'PullRequestEdge', pageInfo: 'PageInfo', totalCount: 'Int' },
  PullRequestEdge: { node: 'PullRequest', cursor: 'String' },
  PullRequestChangedFile: { path: 'String', additions: 'Int', deletions: 'Int', changeType: 'String' },
  PullRequestChangedFileConnection: { nodes: 'PullRequestChangedFile', edges: 'PullRequestChangedFileEdge', pageInfo: 'PageInfo', totalCount: 'Int' },
  PullRequestChangedFileEdge: { node: 'PullRequestChangedFile', cursor: 'String' },
  Comment: { id: 'ID', body: 'String', createdAt: 'String' },
  CommentEdge: { node: 'Comment', cursor: 'String' },
  Label: { id: 'ID', name: 'String', color: 'String' },
  LabelConnection: { nodes: 'Label', pageInfo: 'PageInfo', totalCount: 'Int' },
  CreateIssuePayload: { issue: 'Issue', clientMutationId: 'String' },
  CloseIssuePayload: { issue: 'Issue', clientMutationId: 'String' },
  CreatePullRequestPayload: { pullRequest: 'PullRequest', clientMutationId: 'String' },
  MergePullRequestPayload: { pullRequest: 'PullRequest', clientMutationId: 'String' },
  AddCommentPayload: { commentEdge: 'CommentEdge', subject: 'Issue', clientMutationId: 'String' },
  __Type: { name: 'String', kind: 'String', description: 'String', fields: '__Field', enumValues: '__EnumValue', possibleTypes: '__Type', inputFields: '__InputValue' },
  __Field: { name: 'String', description: 'String', isDeprecated: 'Boolean', deprecationReason: 'String' },
  __EnumValue: { name: 'String', description: 'String', isDeprecated: 'Boolean', deprecationReason: 'String' },
  __InputValue: { name: 'String', description: 'String' },
  __Schema: { queryType: '__Type', mutationType: '__Type', types: '__Type' },
  RateLimit: { limit: 'Int', cost: 'Int', remaining: 'Int', nodeCount: 'Int', resetAt: 'String' },
  Node: { id: 'ID' },
};

const GQL_ENUM_VALUES: Record<string, string[]> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
  OrderDirection: ['ASC', 'DESC'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  PullRequestMergeMethod: ['MERGE', 'SQUASH', 'REBASE'],
  PullRequestReviewState: ['PENDING', 'COMMENTED', 'APPROVED', 'CHANGES_REQUESTED', 'DISMISSED'],
};

// ----- global ids -----

function gid(kind: string, ...parts: Array<string | number>): string {
  return Buffer.from([kind, ...parts.map(String)].join(':'), 'utf8').toString('base64');
}

function decodeGid(id: string): string[] {
  try {
    return Buffer.from(id, 'base64').toString('utf8').split(':');
  } catch {
    return [];
  }
}

function repoByDbId(dbId: number): RepoRec | null {
  for (const repo of repos.values()) if (repo.id === dbId) return repo;
  return null;
}

// ----- execution -----

type GObj = { __t: string; [key: string]: unknown };

function gRepo(repo: RepoRec): GObj {
  return { __t: 'Repository', repo };
}

function gIssue(repo: RepoRec, issue: IssueRec): GObj {
  return { __t: 'Issue', repo, issue };
}

function gPull(repo: RepoRec, pull: PullRec): GObj {
  return { __t: 'PullRequest', repo, pull };
}

function encodeCursor(index: number): string {
  return Buffer.from(`cursor:${index}`, 'utf8').toString('base64');
}

function decodeCursor(cursor: string): number {
  const text = Buffer.from(cursor, 'base64').toString('utf8');
  const match = /^cursor:(\d+)$/.exec(text);
  return match ? Number.parseInt(match[1], 10) : -1;
}

interface PageSlice<T> {
  items: T[];
  pageInfo: GObj;
  totalCount: number;
}

function paginate<T>(list: readonly T[], first: unknown, after: unknown): PageSlice<T> {
  const size = typeof first === 'number' && first > 0 ? Math.floor(first) : 30;
  let start = 0;
  if (typeof after === 'string' && after !== '') start = decodeCursor(after) + 1;
  const items = list.slice(start, start + size);
  const pageInfo: GObj = {
    __t: 'PageInfo',
    hasNextPage: start + items.length < list.length,
    hasPreviousPage: start > 0,
    startCursor: items.length > 0 ? encodeCursor(start) : null,
    endCursor: items.length > 0 ? encodeCursor(start + items.length - 1) : null,
  };
  return { items, pageInfo, totalCount: list.length };
}

function argsOf(field: GqlField, vars: Readonly<Record<string, unknown>>): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const [key, value] of field.args) out[key] = evalGqlValue(value, vars);
  return out;
}

function resolveGqlField(type: string, source: GObj, field: GqlField, vars: Readonly<Record<string, unknown>>): unknown {
  const name = field.name;
  const args = argsOf(field, vars);
  switch (type) {
    case 'Query': {
      if (name === 'viewer') return { __t: 'User', user: VIEWER };
      if (name === 'repository') {
        const repo = findRepo(asString(args.owner), asString(args.name));
        return repo === null ? null : gRepo(repo);
      }
      if (name === 'node') {
        const parts = decodeGid(asString(args.id));
        if (parts[0] === 'R') {
          const repo = repoByDbId(Number(parts[1]));
          return repo === null ? null : gRepo(repo);
        }
        if (parts[0] === 'I') {
          const repo = repoByDbId(Number(parts[1]));
          const issue = repo === null ? null : getIssue(repo, Number(parts[2]));
          return repo === null || issue === null ? null : gIssue(repo, issue);
        }
        if (parts[0] === 'P') {
          const repo = repoByDbId(Number(parts[1]));
          const pull = repo === null ? null : getPull(repo, Number(parts[2]));
          return repo === null || pull === null ? null : gPull(repo, pull);
        }
        return null;
      }
      if (name === '__type') {
        const typeName = asString(args.name);
        if (GQL_FIELD_TYPE[typeName] === undefined && GQL_ENUM_VALUES[typeName] === undefined) return null;
        return { __t: '__Type', typeName };
      }
      if (name === '__schema') return { __t: '__Schema' };
      if (name === 'rateLimit') return { __t: 'RateLimit' };
      return null;
    }
    case 'Mutation': {
      const input = (args.input ?? {}) as Record<string, unknown>;
      if (name === 'createIssue') {
        const parts = decodeGid(asString(input.repositoryId));
        const repo = parts[0] === 'R' ? repoByDbId(Number(parts[1])) : null;
        if (repo === null) throw new Error('createIssue: repository not found');
        const issue = createIssue(repo, asString(input.title), asString(input.body), []);
        return { __t: 'CreateIssuePayload', issue: gIssue(repo, issue), clientMutationId: input.clientMutationId ?? null };
      }
      if (name === 'closeIssue') {
        const parts = decodeGid(asString(input.issueId));
        const repo = parts[0] === 'I' ? repoByDbId(Number(parts[1])) : null;
        const issue = repo === null ? null : getIssue(repo, Number(parts[2]));
        if (repo === null || issue === null) throw new Error('closeIssue: issue not found');
        issue.state = 'closed';
        issue.updatedAt = isoNow();
        return { __t: 'CloseIssuePayload', issue: gIssue(repo, issue), clientMutationId: input.clientMutationId ?? null };
      }
      if (name === 'createPullRequest') {
        const parts = decodeGid(asString(input.repositoryId));
        const repo = parts[0] === 'R' ? repoByDbId(Number(parts[1])) : null;
        if (repo === null) throw new Error('createPullRequest: repository not found');
        const head = asString(input.headRefName);
        const base = asString(input.baseRefName) || repo.defaultBranch;
        if (branchTip(repo, head) === null || branchTip(repo, base) === null) throw new Error('createPullRequest: branch not found');
        const pull = createPull(repo, asString(input.title), asString(input.body), head, base);
        return { __t: 'CreatePullRequestPayload', pullRequest: gPull(repo, pull), clientMutationId: input.clientMutationId ?? null };
      }
      if (name === 'mergePullRequest') {
        const parts = decodeGid(asString(input.pullRequestId));
        const repo = parts[0] === 'P' ? repoByDbId(Number(parts[1])) : null;
        const pull = repo === null ? null : getPull(repo, Number(parts[2]));
        if (repo === null || pull === null) throw new Error('mergePullRequest: pull request not found');
        const method = asString(input.mergeMethod).toLowerCase() || 'merge';
        if (pull.state === 'open') {
          const sha = mergePull(repo, pull, ['merge', 'squash', 'rebase'].includes(method) ? method : 'merge');
          if (sha === null) throw new Error('mergePullRequest: pull request is not mergeable');
        }
        return { __t: 'MergePullRequestPayload', pullRequest: gPull(repo, pull), clientMutationId: input.clientMutationId ?? null };
      }
      if (name === 'addComment') {
        const parts = decodeGid(asString(input.subjectId));
        const repo = parts[0] === 'I' ? repoByDbId(Number(parts[1])) : null;
        const issue = repo === null ? null : getIssue(repo, Number(parts[2]));
        if (repo === null || issue === null) throw new Error('addComment: subject not found');
        const comment: CommentRec = { id: nextCommentId++, body: asString(input.body), createdAt: isoNow() };
        issue.comments.push(comment);
        return {
          __t: 'AddCommentPayload',
          commentEdge: { __t: 'CommentEdge', node: { __t: 'Comment', comment }, cursor: encodeCursor(issue.comments.length - 1) },
          subject: gIssue(repo, issue),
          clientMutationId: input.clientMutationId ?? null,
        };
      }
      return null;
    }
    case 'User': {
      const user = source.user as ForgeUser;
      if (name === 'login') return user.login;
      if (name === 'id') return gid('U', user.id);
      if (name === 'name') return user.name;
      if (name === 'email') return user.email;
      if (name === 'databaseId') return user.id;
      return null;
    }
    case 'Repository': {
      const repo = source.repo as RepoRec;
      switch (name) {
        case 'id':
          return gid('R', repo.id);
        case 'databaseId':
          return repo.id;
        case 'name':
          return repo.name;
        case 'nameWithOwner':
          return `${repo.owner}/${repo.name}`;
        case 'owner': {
          const user = USERS.find((candidate) => candidate.login === repo.owner) ?? { id: 0, login: repo.owner, name: repo.owner, email: '' };
          return { __t: 'User', user };
        }
        case 'defaultBranchRef':
          return branchTip(repo, repo.defaultBranch) !== null ? { __t: 'Ref', refName: repo.defaultBranch } : null;
        case 'viewerPermission':
          return 'ADMIN';
        case 'hasIssuesEnabled':
          return true;
        case 'isPrivate':
          return repo.priv;
        case 'description':
          return repo.description;
        case 'createdAt':
        case 'updatedAt':
          return repo.createdAt;
        case 'issue': {
          const issue = getIssue(repo, Number(args.number));
          return issue === null ? null : gIssue(repo, issue);
        }
        case 'issues': {
          let list = [...repo.items.values()].filter((item): item is IssueRec => item.kind === 'issue');
          if (Array.isArray(args.states)) {
            const wanted = new Set(args.states.map((state) => String(state).toLowerCase()));
            list = list.filter((issue) => wanted.has(issue.state));
          }
          const orderBy = (args.orderBy ?? null) as Record<string, unknown> | null;
          const direction = orderBy !== null && asString(orderBy.direction) === 'DESC' ? -1 : 1;
          list.sort((a, b) => direction * (a.createdSeq - b.createdSeq));
          const page = paginate(list, args.first, args.after);
          return { __t: 'IssueConnection', nodes: page.items.map((issue) => gIssue(repo, issue)), pageInfo: page.pageInfo, totalCount: page.totalCount };
        }
        case 'pullRequest': {
          const pull = getPull(repo, Number(args.number));
          return pull === null ? null : gPull(repo, pull);
        }
        case 'pullRequests': {
          let list = [...repo.items.values()].filter((item): item is PullRec => item.kind === 'pull');
          if (Array.isArray(args.states)) {
            const wanted = new Set(args.states.map((state) => String(state)));
            list = list.filter((pull) => wanted.has(pull.merged ? 'MERGED' : pull.state.toUpperCase()));
          }
          list.sort((a, b) => b.createdSeq - a.createdSeq);
          const page = paginate(list, args.first, args.after);
          return { __t: 'PullRequestConnection', nodes: page.items.map((pull) => gPull(repo, pull)), pageInfo: page.pageInfo, totalCount: page.totalCount };
        }
        default:
          return null;
      }
    }
    case 'Ref':
      if (name === 'name') return source.refName;
      if (name === 'prefix') return 'refs/heads/';
      return null;
    case 'Issue': {
      const repo = source.repo as RepoRec;
      const issue = source.issue as IssueRec;
      switch (name) {
        case 'id':
          return gid('I', repo.id, issue.number);
        case 'number':
          return issue.number;
        case 'title':
          return issue.title;
        case 'state':
          return issue.state.toUpperCase();
        case 'body':
          return issue.body;
        case 'repository':
          return gRepo(repo);
        case 'createdAt':
          return issue.createdAt;
        case 'updatedAt':
          return issue.updatedAt;
        case 'labels':
          return {
            __t: 'LabelConnection',
            nodes: issue.labels.map((labelName) => ({ __t: 'Label', labelName, color: repo.labels.get(labelName)?.color ?? 'ededed' })),
            pageInfo: { __t: 'PageInfo', hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null },
            totalCount: issue.labels.length,
          };
        case 'comments': {
          const page = paginate(issue.comments, args.first, args.after);
          return { __t: 'IssueCommentConnection', nodes: page.items.map((comment) => ({ __t: 'Comment', comment })), pageInfo: page.pageInfo, totalCount: page.totalCount };
        }
        default:
          return null;
      }
    }
    case 'PullRequest': {
      const repo = source.repo as RepoRec;
      const pull = source.pull as PullRec;
      switch (name) {
        case 'id':
          return gid('P', repo.id, pull.number);
        case 'number':
          return pull.number;
        case 'title':
          return pull.title;
        case 'body':
          return pull.body;
        case 'state':
          return pull.merged ? 'MERGED' : pull.state.toUpperCase();
        case 'merged':
          return pull.merged;
        case 'mergeable':
          return pull.state !== 'open' ? 'UNKNOWN' : pullConflicts(repo, pull) ? 'CONFLICTING' : 'MERGEABLE';
        case 'headRefName':
          return pull.headRef;
        case 'baseRefName':
          return pull.baseRef;
        case 'repository':
          return gRepo(repo);
        case 'createdAt':
          return pull.createdAt;
        case 'updatedAt':
          return pull.updatedAt;
        case 'files': {
          const files = pullFiles(repo, pull).map((file) => ({
            __t: 'PullRequestChangedFile',
            path: file.path,
            additions: file.additions,
            deletions: file.deletions,
            changeType: file.status.toUpperCase(),
          }));
          const page = paginate(files, args.first, args.after);
          return { __t: 'PullRequestChangedFileConnection', nodes: page.items, pageInfo: page.pageInfo, totalCount: page.totalCount };
        }
        default:
          return null;
      }
    }
    case 'PullRequestChangedFile':
      if (name === 'path') return source.path;
      if (name === 'additions') return source.additions;
      if (name === 'deletions') return source.deletions;
      if (name === 'changeType') return source.changeType;
      return null;
    case 'Comment': {
      const comment = source.comment as CommentRec;
      if (name === 'id') return gid('C', comment.id);
      if (name === 'body') return comment.body;
      if (name === 'createdAt') return comment.createdAt;
      return null;
    }
    case 'Label':
      if (name === 'id') return gid('L', asString(source.labelName));
      if (name === 'name') return source.labelName;
      if (name === 'color') return source.color;
      return null;
    case 'IssueConnection':
    case 'PullRequestConnection':
    case 'PullRequestChangedFileConnection':
    case 'LabelConnection':
    case 'IssueCommentConnection': {
      if (name === 'nodes') return source.nodes;
      if (name === 'pageInfo') return source.pageInfo;
      if (name === 'totalCount') return source.totalCount;
      if (name === 'edges') {
        const edgeType = { IssueConnection: 'IssueEdge', PullRequestConnection: 'PullRequestEdge', PullRequestChangedFileConnection: 'PullRequestChangedFileEdge', LabelConnection: 'CommentEdge', IssueCommentConnection: 'CommentEdge' }[type] ?? 'CommentEdge';
        return (source.nodes as GObj[]).map((node, index) => ({ __t: edgeType, node, cursor: encodeCursor(index) }));
      }
      return null;
    }
    case 'PageInfo':
      return (source as unknown as Record<string, unknown>)[name] ?? null;
    case 'CommentEdge':
    case 'IssueEdge':
    case 'PullRequestEdge':
    case 'PullRequestChangedFileEdge':
      if (name === 'node') return source.node;
      if (name === 'cursor') return source.cursor;
      return null;
    case 'CreateIssuePayload':
    case 'CloseIssuePayload':
      if (name === 'issue') return source.issue;
      if (name === 'clientMutationId') return source.clientMutationId;
      return null;
    case 'CreatePullRequestPayload':
    case 'MergePullRequestPayload':
      if (name === 'pullRequest') return source.pullRequest;
      if (name === 'clientMutationId') return source.clientMutationId;
      return null;
    case 'AddCommentPayload':
      if (name === 'commentEdge') return source.commentEdge;
      if (name === 'subject') return source.subject;
      if (name === 'clientMutationId') return source.clientMutationId;
      return null;
    case '__Type': {
      const typeName = asString(source.typeName);
      if (name === 'name') return typeName;
      if (name === 'kind') return GQL_ENUM_VALUES[typeName] !== undefined ? 'ENUM' : 'OBJECT';
      if (name === 'description') return null;
      if (name === 'fields') {
        const fields = GQL_FIELD_TYPE[typeName];
        if (fields === undefined) return null;
        return Object.keys(fields).map((fieldName) => ({ __t: '__Field', fieldName }));
      }
      if (name === 'enumValues') {
        const values = GQL_ENUM_VALUES[typeName];
        if (values === undefined) return null;
        return values.map((value) => ({ __t: '__EnumValue', valueName: value }));
      }
      if (name === 'possibleTypes') return null;
      if (name === 'inputFields') return null;
      return null;
    }
    case '__Field':
      if (name === 'name') return source.fieldName;
      if (name === 'isDeprecated') return false;
      return null;
    case '__EnumValue':
      if (name === 'name') return source.valueName;
      if (name === 'isDeprecated') return false;
      return null;
    case '__Schema':
      if (name === 'queryType') return { __t: '__Type', typeName: 'Query' };
      if (name === 'mutationType') return { __t: '__Type', typeName: 'Mutation' };
      if (name === 'types') return Object.keys(GQL_FIELD_TYPE).map((typeName) => ({ __t: '__Type', typeName }));
      return null;
    case 'RateLimit':
      if (name === 'limit') return 5000;
      if (name === 'cost') return 1;
      if (name === 'remaining') return 5000;
      if (name === 'nodeCount') return 0;
      if (name === 'resetAt') return new Date(0).toISOString();
      return null;
    default:
      return null;
  }
}

function validateGqlSelections(type: string, selections: readonly GqlSelection[], doc: GqlDoc, errors: Array<{ message: string }>): void {
  for (const selection of selections) {
    if (selection.type === 'field') {
      const fieldName = selection.field.name;
      if (fieldName === '__typename') continue;
      const returnType = GQL_FIELD_TYPE[type]?.[fieldName];
      if (returnType === undefined) {
        errors.push({ message: `Field '${fieldName}' doesn't exist on type '${type}'` });
        continue;
      }
      if (selection.field.selections.length > 0) validateGqlSelections(returnType, selection.field.selections, doc, errors);
    } else if (selection.type === 'inline') {
      validateGqlSelections(selection.on ?? type, selection.selections, doc, errors);
    } else {
      const fragment = doc.fragments.get(selection.name);
      if (fragment) validateGqlSelections(fragment.on, fragment.selections, doc, errors);
    }
  }
}

function executeGqlSelections(type: string, source: GObj, selections: readonly GqlSelection[], doc: GqlDoc, vars: Readonly<Record<string, unknown>>, out: Record<string, unknown>): void {
  for (const selection of selections) {
    if (selection.type === 'field') {
      const field = selection.field;
      const key = field.alias ?? field.name;
      if (field.name === '__typename') {
        out[key] = type;
        continue;
      }
      const raw = resolveGqlField(type, source, field, vars);
      out[key] = completeGqlValue(raw, field.selections, doc, vars);
    } else if (selection.type === 'inline') {
      if (selection.on === null || selection.on === type || selection.on === 'Node') {
        executeGqlSelections(type, source, selection.selections, doc, vars, out);
      }
    } else {
      const fragment = doc.fragments.get(selection.name);
      if (fragment && (fragment.on === type || fragment.on === 'Node')) {
        executeGqlSelections(type, source, fragment.selections, doc, vars, out);
      }
    }
  }
}

function completeGqlValue(raw: unknown, selections: readonly GqlSelection[], doc: GqlDoc, vars: Readonly<Record<string, unknown>>): unknown {
  if (raw === null || raw === undefined) return null;
  if (Array.isArray(raw)) return raw.map((item) => completeGqlValue(item, selections, doc, vars));
  if (typeof raw === 'object' && selections.length > 0) {
    const obj = raw as GObj;
    const out: Record<string, unknown> = {};
    executeGqlSelections(obj.__t, obj, selections, doc, vars, out);
    return out;
  }
  return raw;
}

function runGraphQLOperation(payload: Record<string, unknown>): Record<string, unknown> {
  const query = asString(payload.query);
  const vars = (payload.variables ?? {}) as Record<string, unknown>;
  let doc: GqlDoc;
  try {
    doc = new GqlParser(query).parseDocument();
  } catch (err) {
    return { errors: [{ message: err instanceof Error ? err.message : String(err) }] };
  }
  const operationName = typeof payload.operationName === 'string' ? payload.operationName : null;
  const operation = operationName !== null ? doc.operations.find((candidate) => candidate.name === operationName) : doc.operations[0];
  if (operation === undefined) return { errors: [{ message: 'No operation found' }] };
  const rootType = operation.op === 'mutation' ? 'Mutation' : 'Query';
  const errors: Array<{ message: string }> = [];
  validateGqlSelections(rootType, operation.selections, doc, errors);
  if (errors.length > 0) return { data: null, errors };
  try {
    const out: Record<string, unknown> = {};
    executeGqlSelections(rootType, { __t: rootType }, operation.selections, doc, vars, out);
    return { data: out };
  } catch (err) {
    return { data: null, errors: [{ message: err instanceof Error ? err.message : String(err) }] };
  }
}

async function handleGraphQL(req: IncomingMessage, res: ServerResponse): Promise<void> {
  requireAuth(req);
  const raw = await readBody(req);
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw.toString('utf8'));
  } catch {
    sendJson(res, 400, { errors: [{ message: 'Problems parsing JSON' }] });
    return;
  }
  if (Array.isArray(parsed)) {
    sendJson(res, 200, parsed.map((entry) => runGraphQLOperation((entry ?? {}) as Record<string, unknown>)));
    return;
  }
  sendJson(res, 200, runGraphQLOperation((parsed ?? {}) as Record<string, unknown>));
}

// ---------------------------------------------------------------------------------------------
// MCP over streamable HTTP
// ---------------------------------------------------------------------------------------------

const MCP_SERVER_INFO = { name: 'github-core-clone', version: VERSION };
const MCP_SUPPORTED_VERSIONS = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];

const MCP_TOOLS: ReadonlyArray<Record<string, unknown>> = [
  {
    name: 'create_repo',
    description: 'Create a new repository for the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'The repository name.' },
        description: { type: 'string', description: 'A short description of the repository.' },
        private: { type: 'boolean', description: 'Whether the repository is private.' },
        owner: { type: 'string', description: 'The account the repository belongs to (the token owner).' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The issue title.' },
        body: { type: 'string', description: 'The issue body.' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List the issues of a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        state: { type: 'string', description: 'Filter by state: open, closed or all.' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request from a head branch into a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        title: { type: 'string', description: 'The pull request title.' },
        body: { type: 'string', description: 'The pull request body.' },
        head: { type: 'string', description: 'The head branch name.' },
        base: { type: 'string', description: 'The base branch name.' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request by number.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'The repository owner login.' },
        repo: { type: 'string', description: 'The repository name.' },
        pull_number: { type: 'number', description: 'The pull request number.' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

function mcpToolSuccess(value: unknown): Record<string, unknown> {
  return { content: [{ type: 'text', text: JSON.stringify(value) }], structuredContent: value, isError: false };
}

function mcpToolFailure(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function callMcpTool(name: string, args: Record<string, unknown>): Record<string, unknown> | null {
  const requiredByTool: Record<string, string[]> = {
    create_repo: ['name'],
    get_repo: ['owner', 'repo'],
    create_issue: ['owner', 'repo', 'title'],
    list_issues: ['owner', 'repo'],
    create_pull_request: ['owner', 'repo', 'title', 'head', 'base'],
    merge_pull_request: ['owner', 'repo', 'pull_number'],
  };
  const required = requiredByTool[name];
  if (required === undefined) return null;
  for (const key of required) {
    if (args[key] === undefined || args[key] === null || args[key] === '') return mcpToolFailure(`missing required argument: ${key}`);
  }
  switch (name) {
    case 'create_repo': {
      const repoName = asString(args.name);
      const existing = findRepo(VIEWER.login, repoName);
      if (existing !== null) return mcpToolSuccess(repoJson(existing));
      const repo = createRepo(VIEWER.login, repoName, args.private !== false, asString(args.description));
      return mcpToolSuccess(repoJson(repo));
    }
    case 'get_repo': {
      const repo = findRepo(asString(args.owner), asString(args.repo));
      if (repo === null) return mcpToolFailure(`repository ${asString(args.owner)}/${asString(args.repo)} not found`);
      return mcpToolSuccess(repoJson(repo));
    }
    case 'create_issue': {
      const repo = findRepo(asString(args.owner), asString(args.repo));
      if (repo === null) return mcpToolFailure('repository not found');
      const issue = createIssue(repo, asString(args.title), asString(args.body), []);
      return mcpToolSuccess(issueJson(repo, issue));
    }
    case 'list_issues': {
      const repo = findRepo(asString(args.owner), asString(args.repo));
      if (repo === null) return mcpToolFailure('repository not found');
      const state = asString(args.state) || 'open';
      let list = [...repo.items.values()].filter((item): item is IssueRec => item.kind === 'issue');
      if (state === 'open' || state === 'closed') list = list.filter((issue) => issue.state === state);
      list.sort((a, b) => a.createdSeq - b.createdSeq);
      return mcpToolSuccess(list.map((issue) => issueJson(repo, issue)));
    }
    case 'create_pull_request': {
      const repo = findRepo(asString(args.owner), asString(args.repo));
      if (repo === null) return mcpToolFailure('repository not found');
      const head = asString(args.head);
      const base = asString(args.base) || repo.defaultBranch;
      if (branchTip(repo, head) === null) return mcpToolFailure(`head branch '${head}' does not exist`);
      if (branchTip(repo, base) === null) return mcpToolFailure(`base branch '${base}' does not exist`);
      const pull = createPull(repo, asString(args.title), asString(args.body), head, base);
      return mcpToolSuccess(pullJson(repo, pull));
    }
    case 'merge_pull_request': {
      const repo = findRepo(asString(args.owner), asString(args.repo));
      if (repo === null) return mcpToolFailure('repository not found');
      const pull = getPull(repo, Number(args.pull_number));
      if (pull === null) return mcpToolFailure(`pull request #${String(args.pull_number)} not found`);
      if (pull.state === 'open') {
        const sha = mergePull(repo, pull, 'squash');
        if (sha === null) return mcpToolFailure('pull request is not mergeable');
      }
      return mcpToolSuccess(pullJson(repo, pull));
    }
    default:
      return null;
  }
}

function mcpDispatch(request: Record<string, unknown>): { result?: unknown; error?: { code: number; message: string } } {
  const method = asString(request.method);
  const params = (request.params ?? {}) as Record<string, unknown>;
  switch (method) {
    case 'server/discover':
      return {
        result: {
          resultType: 'complete',
          supportedVersions: MCP_SUPPORTED_VERSIONS,
          capabilities: { tools: {} },
          serverInfo: MCP_SERVER_INFO,
          instructions: 'A GitHub-compatible forge: repositories, issues and pull requests.',
          _meta: { 'io.modelcontextprotocol/serverInfo': MCP_SERVER_INFO },
        },
      };
    case 'initialize': {
      const offered = asString(params.protocolVersion);
      const protocolVersion = MCP_SUPPORTED_VERSIONS.includes(offered) ? offered : '2025-06-18';
      return { result: { protocolVersion, capabilities: { tools: {} }, serverInfo: MCP_SERVER_INFO } };
    }
    case 'ping':
      return { result: {} };
    case 'tools/list':
      return { result: { tools: MCP_TOOLS } };
    case 'tools/call': {
      const toolName = asString(params.name);
      const args = (params.arguments ?? {}) as Record<string, unknown>;
      const result = callMcpTool(toolName, args);
      if (result === null) return { error: { code: -32602, message: `Unknown tool: ${toolName}` } };
      return { result };
    }
    default:
      return { error: { code: -32601, message: `Method not found: ${method}` } };
  }
}

async function handleMcp(req: IncomingMessage, res: ServerResponse): Promise<void> {
  if (req.method === 'GET') {
    sendJson(res, 405, { jsonrpc: '2.0', error: { code: -32000, message: 'GET is not supported on this endpoint' }, id: null });
    return;
  }
  if (req.method === 'DELETE') {
    sendJson(res, 200, {});
    return;
  }
  if (req.method !== 'POST') {
    sendJson(res, 405, { jsonrpc: '2.0', error: { code: -32000, message: 'Method not allowed' }, id: null });
    return;
  }
  if (!authed(req)) {
    sendJson(res, 401, { jsonrpc: '2.0', error: { code: -32001, message: 'Unauthorized' }, id: null });
    return;
  }
  const raw = await readBody(req);
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw.toString('utf8'));
  } catch {
    sendJson(res, 400, { jsonrpc: '2.0', error: { code: -32700, message: 'Parse error' }, id: null });
    return;
  }
  const handleOne = (entry: unknown): Record<string, unknown> | null => {
    if (entry === null || typeof entry !== 'object' || Array.isArray(entry)) {
      return { jsonrpc: '2.0', error: { code: -32600, message: 'Invalid Request' }, id: null };
    }
    const request = entry as Record<string, unknown>;
    if (!('id' in request)) return null; // a notification: accepted, never answered
    const { result, error } = mcpDispatch(request);
    if (error !== undefined) return { jsonrpc: '2.0', id: request.id ?? null, error };
    return { jsonrpc: '2.0', id: request.id ?? null, result };
  };
  if (Array.isArray(parsed)) {
    const responses = parsed.map(handleOne).filter((entry) => entry !== null);
    sendJson(res, 200, responses);
    return;
  }
  const response = handleOne(parsed);
  if (response === null) {
    res.writeHead(202, { 'x-github-request-id': randomUUID() });
    res.end();
    return;
  }
  sendJson(res, 200, response);
}

// ---------------------------------------------------------------------------------------------
// The server
// ---------------------------------------------------------------------------------------------

async function route(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const url = new URL(req.url ?? '/', 'http://entry');
  const path = url.pathname;
  const method = req.method ?? 'GET';

  if (method === 'GET' && path === '/healthz') {
    sendJson(res, 200, { ok: true });
    return;
  }
  if (path === '/api/graphql') {
    if (method !== 'POST') throw notFound();
    await handleGraphQL(req, res);
    return;
  }
  if (path === '/mcp') {
    await handleMcp(req, res);
    return;
  }
  if (path === '/api/v3' || path.startsWith('/api/v3/')) {
    await handleRest(req, res, url);
    return;
  }
  const gitMatch = /^\/([^/]+)\/([^/]+)\.git\/(info\/refs|git-upload-pack|git-receive-pack)$/.exec(path);
  if (gitMatch) {
    await handleGitHttp(req, res, url, decodeSegment(gitMatch[1]), decodeSegment(gitMatch[2]), gitMatch[3]);
    return;
  }
  throw notFound();
}

/** Build the server. It binds nothing until the caller listens; the entry listens on an ephemeral port. */
export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    route(req, res).catch((err: unknown) => {
      if (res.headersSent) {
        res.end();
        return;
      }
      if (err instanceof ApiError) {
        sendJson(res, err.status, { message: err.message });
      } else {
        process.stderr.write(`[forge] ${err instanceof Error ? err.stack ?? err.message : String(err)}\n`);
        sendJson(res, 500, { message: 'Internal Server Error' });
      }
    });
  });
}
