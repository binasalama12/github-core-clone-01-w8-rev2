[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/binasalama12/github-core-clone-01-w8-rev2/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/binasalama12/github-core-clone-01-w8-rev2/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

# Unit-of-work forge

A GitHub-compatible git forge for the make.fun `github-core-clone-01`
competition, implemented from scratch in TypeScript on the Node 22 standard
library — no dependencies, no build step.

## Architecture

The code is split in two files:

- `main.ts` — entry lifecycle only: reads `MAKEFUN_ENV_URL`, builds the app,
  listens on port 0, registers with the environment, polls `/done`, closes.
- `app.ts` — everything else, organized around two ideas:
  - a **Repository aggregate** that owns the object map, ref map, issues,
    pull requests, labels and the per-repository pack cache;
  - a **unit of work**: every mutating git write (push ingest, contents
    commit, pull-request squash merge) stages new objects and ref intents
    privately, then publishes them atomically only if the aggregate's
    `version` counter still matches the snapshot taken when the unit of work
    opened. A mismatch raises `StaleUnitError` instead of writing through.

## Surfaces

- **REST** under `/api/v3`: user, repositories, labels, issues and comments,
  pull requests (files, merge), contents, git refs, branches and commits.
- **Git smart HTTP**: `info/refs` with protocol v0 and v2, `git-upload-pack`
  (wants/haves, shallow/deepen, side-band-64k, cached pack generation) and
  `git-receive-pack` (delta-resolving pack ingest, fast-forward enforcement,
  report-status).
- **GraphQL** at `/api/graphql`: queries, connections with cursor paging,
  mutations, node lookup and the introspection the clients exercise.
- **MCP** at `/mcp`: `server/discover`, legacy `initialize`, and six tools
  (`create_repo`, `get_repo`, `create_issue`, `list_issues`,
  `create_pull_request`, `merge_pull_request`).

Authentication is `Authorization: Bearer <token>` with the token taken from
`MAKEFUN_SHOP_TOKEN`; an empty configured token accepts any caller.

## Performance notes

- Pack ingest inflates each object with a single `inflateSync(..., { info:
  true })` call and trusts the engine's consumed-byte count.
- Fast-forward checks are early-exit depth-first walks, never full ancestor
  sets.
- Every stored object is hashed exactly once, at staging time.
- Identical pack requests are served from a per-repository cache keyed by the
  sorted object set.

## Running

```sh
MAKEFUN_ENV_URL=http://localhost:PORT MAKEFUN_SHOP_TOKEN=secret node main.ts
```

A standalone health check is available at `GET /healthz`.
