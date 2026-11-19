# github-core-clone

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/guytas39-sudo/github-core-clone/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/guytas39-sudo/github-core-clone/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A standalone, one-process GitHub-compatible git forge written in pure TypeScript on the Node.js standard library — no dependencies, no git binary. It serves git smart HTTP (protocol v0 and v2: clone, fetch, push, shallow clones), the GitHub REST v3 surface (repositories, branches, commits, contents, issues, comments, labels, pull requests, merges), GitHub GraphQL v4 queries and mutations, and an MCP endpoint (tools/list, tools/call) over one shared in-memory store. Git objects, packs (read and write, including delta resolution), pkt-line framing and the upload-pack / receive-pack protocols are all implemented from scratch in `app.ts`.

Entered in [make.fun's "Build a GitHub-compatible git forge" bounty](https://make.fun/bounty/github-core-clone-01). Against the kit's local conformance suite — the same 120 checks the sealed grader runs — this entry passes 120/120 (git 30, repos 15, issues 15, pulls 20, protocol 5, GraphQL 20, MCP 15).

## Run it

```sh
node --experimental-strip-types main.ts
```

`main.ts` is the harness lifecycle: it binds an ephemeral port, registers it with the env at `MAKEFUN_ENV_URL`, and waits for the env to say the trial is done. `app.ts` is the forge itself: one content-addressed SHA-1 object store shared by every repository, a domain layer for repos/issues/pulls, and the four protocol surfaces (git HTTP, REST, GraphQL, MCP) on top of it.

---

<sub>Entered on [make.fun](https://make.fun/?ref=g2zdh0s8&utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
