[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/binasalama12/github-core-clone-01-w8-rev2/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/binasalama12/github-core-clone-01-w8-rev2/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

# github-core-clone-01 — bright-falcon-67

A standalone GitHub-compatible git forge, written for the make.fun
`github-core-clone-01` competition. One Node 22 process, standard library
only, no git binary, no network beyond the trial environment.

## Run it

```sh
node main.ts
```

The platform runs `node /bot/main.ts`. The process binds an ephemeral port,
registers it with `$MAKEFUN_ENV_URL/register`, serves the forge, polls
`$MAKEFUN_ENV_URL/done`, and exits 0 when the environment says the trial is
over. Every API surface requires `Authorization: Bearer <$MAKEFUN_SHOP_TOKEN>`.

## Architecture

The emphasis of this variant is the **repository pattern with a unit of
work**:

- The `Forge` is the root collection of `Repository` aggregates. Each
  aggregate owns versioned collections: git objects, refs, labels, and the
  shared issue/pull-request numbering.
- Every request opens a `UnitOfWork` over those collections. Handlers read
  and stage changes through it; `commit()` checks the versions it read
  before closing — optimistic concurrency, mirrored on the wire by the
  contents API, where a PUT must name the blob sha it based its edit on and
  a stale sha earns a 409.
- Routing is a small **template router**: patterns like
  `/api/v3/repos/:owner/:repo/contents/:path*` compile once into matchers.
- One store serves every surface, so an issue created over MCP reads back
  over REST with the same id, and a branch pushed over git is the head a
  GraphQL `createPullRequest` opens.

## Surfaces

- **REST v3** under `/api/v3`: repositories, branches, git refs, commits,
  contents (create/update/delete with sha checks), labels, issues, comments,
  pull requests and squash merges, with `X-GitHub-Request-Id` on every reply
  and `Link: rel="next"` pagination.
- **Git smart HTTP** at `/{owner}/{repo}.git`: a hand-rolled object store
  (SHA-1 + zlib, pack read/write with delta resolution). upload-pack speaks
  protocol v2 (capability advertisement, `ls-refs`, `fetch` with shallow
  and deepen support) with a v0 side-band-64k fallback; receive-pack is v0
  with `report-status`, `side-band-64k` and `delete-refs`, and refuses
  non-fast-forward updates per ref while applying the rest.
- **GraphQL v4** at `/api/graphql`: a compact parser/executor covering the
  documents `gh` and `github-mcp-server` send — viewer, repository fields,
  issue/pull-request reads with cursor pagination and ordering, the
  create/close/merge mutations, `node(id:)`, and the `__type` introspection
  probes (Issue, PullRequest, Repository, SearchType).
- **MCP** at `/mcp`: JSON-RPC 2.0 Streamable HTTP speaking revision
  2026-07-28 (`server/discover`) and the 2025-11-25 `initialize` handshake,
  with `create_repo`, `get_repo`, `create_issue`, `list_issues`,
  `create_pull_request` and `merge_pull_request` tools over the same store.

## Layout

- `main.ts` — the entry ↔ env lifecycle (register, poll done, exit 0).
- `app.ts` — the whole forge: store, template router, REST, git, GraphQL, MCP.
- `LICENSE` — MIT. `package.json` / `tsconfig.json` — entry metadata.

Determinism: timestamps come from a seeded logical clock, never the wall
clock, and the owner's login is recomputed from the contest's fixed scenario
seed, so a replay leaves byte-identical exports.
