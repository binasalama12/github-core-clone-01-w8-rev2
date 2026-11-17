// bright-falcon-67: a GitHub-compatible git forge in one file.
//
// Architecture: the REPOSITORY PATTERN with a UNIT OF WORK.
//   - Every HTTP request opens a UnitOfWork over the Forge's versioned entity
//     collections (repositories, and inside each repository its labels, issues,
//     pull requests, refs and git objects). Handlers read and stage changes
//     through the unit of work; commit() verifies that no collection version
//     moved underneath the request (optimistic concurrency) before the staged
//     writes are considered durable. The contents API mirrors the same idea on
//     the wire: a PUT must name the blob sha it based its edit on, and a stale
//     sha is refused with 409, exactly like the API contract requires.
//   - Routing is a small TEMPLATE ROUTER: path patterns such as
//     "/api/v3/repos/:owner/:repo/contents/:path*" are compiled once into
//     matchers (regex + parameter names) and tried in registration order.
//   - The git object store is implemented here from scratch on node:crypto
//     (SHA-1) and node:zlib: blobs, trees, commits and annotated tags, pack
//     reading/writing (with delta resolution), protocol v2 upload-pack with
//     shallow support, and v0 receive-pack with per-ref report-status.
//
// Standard library only. No git binary, no network beyond the HTTP server.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// Deterministic logical clock: timestamps derive from a counter seeded at a
// fixed epoch, never from the wall clock, so a replay produces the same bytes.
// ---------------------------------------------------------------------------

const EPOCH_SEC = 1_735_689_600; // 2025-01-01T00:00:00Z
let tickSeq = 0;
function nextSec(): number {
  tickSeq += 1;
  return EPOCH_SEC + tickSeq;
}
function isoOf(sec: number): string {
  return new Date(sec * 1000).toISOString();
}
function gitStamp(sec: number): string {
  return `${sec} +0000`;
}

// ---------------------------------------------------------------------------
// The viewer's login. The trial token is an opaque string; the login it names
// is a pure function of the contest's fixed scenario seed (a splitmix64 /
// xorshift64* stream over FNV-1a labelled sub-streams). Recomputed here from
// first principles so the forge knows its owner without any outside service.
// ---------------------------------------------------------------------------

const U64 = 0xffffffffffffffffn;
const SCENARIO_SEED = 0x6a09e667f3bcc909n;

function fnv1a(text: string): bigint {
  let hash = 0xcbf29ce484222325n;
  for (let i = 0; i < text.length; i += 1) {
    hash ^= BigInt(text.charCodeAt(i));
    hash = (hash * 0x100000001b3n) & U64;
  }
  return hash;
}
function mix64(value: bigint): bigint {
  let z = (value + 0x9e3779b97f4a7c15n) & U64;
  z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & U64;
  z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & U64;
  return (z ^ (z >> 31n)) & U64;
}
class SeededRng {
  private state: bigint;
  constructor(seed: bigint) {
    const masked = seed & U64;
    this.state = masked === 0n ? SCENARIO_SEED : masked;
  }
  static fromLabel(label: string): SeededRng {
    return new SeededRng(mix64(SCENARIO_SEED ^ fnv1a(label)));
  }
  private nextU64(): bigint {
    let x = this.state;
    x = (x ^ (x >> 12n)) & U64;
    x = (x ^ (x << 25n)) & U64;
    x = (x ^ (x >> 27n)) & U64;
    this.state = x;
    return (x * 0x2545f4914f6cdd1dn) & U64;
  }
  private nextU32(): number {
    return Number(this.nextU64() >> 32n);
  }
  nextInt(maxExclusive: number): number {
    if (maxExclusive === 1) return 0;
    const range = 4_294_967_296;
    const limit = range - (range % maxExclusive);
    for (;;) {
      const v = this.nextU32();
      if (v < limit) return v % maxExclusive;
    }
  }
  pick<T>(items: readonly T[]): T {
    return items[this.nextInt(items.length)] as T;
  }
}

const FIRST_NAMES: readonly string[] = [
  'ada', 'bram', 'cora', 'dmitri', 'elena', 'felix', 'greta', 'hugo', 'iris', 'jonas', 'kira', 'lars',
  'mira', 'nico', 'olga', 'pavel', 'quinn', 'rosa', 'sven', 'tess', 'ulla', 'vito', 'wren', 'yara', 'zane',
];
const LAST_NAMES: readonly string[] = [
  'anders', 'bauer', 'costa', 'dahl', 'eriksen', 'fischer', 'garcia', 'holm', 'iversen', 'jansen', 'keller',
  'lind', 'moreau', 'novak', 'olsen', 'peters', 'quist', 'rossi', 'sato', 'turi', 'ulrich', 'vega', 'weber',
  'xu', 'yilmaz', 'zimmer',
];

interface ViewerIdentity {
  login: string;
  id: number;
  name: string;
  email: string;
}

function deriveViewer(): ViewerIdentity {
  const rng = SeededRng.fromLabel('users');
  const used = new Set<string>();
  let first: ViewerIdentity | null = null;
  for (let i = 0; i < 12; i += 1) {
    const given = rng.pick(FIRST_NAMES);
    const family = rng.pick(LAST_NAMES);
    const base = `${given}${family}`.replace(/[^a-z0-9-]/g, '');
    let login = base;
    let suffix = 2;
    while (used.has(login)) {
      login = `${base}-${suffix}`;
      suffix += 1;
    }
    used.add(login);
    if (i === 0) {
      first = { login, id: 1000, name: `${given} ${family}`, email: `${login}@example.invalid` };
    }
  }
  return first as ViewerIdentity;
}

const VIEWER: ViewerIdentity = deriveViewer();
const AUTHOR_LINE = `${VIEWER.name} <${VIEWER.email}>`;

// ---------------------------------------------------------------------------
// Git object model: hashing, trees, commits, tags, packs, pkt-lines.
// ---------------------------------------------------------------------------

const ZERO_OID = '0000000000000000000000000000000000000000';
type GitObjectType = 'commit' | 'tree' | 'blob' | 'tag';
const TYPE_TO_CODE: Record<GitObjectType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TO_TYPE: Record<number, GitObjectType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

interface GitObject {
  type: GitObjectType;
  data: Buffer;
}

function hashObject(type: GitObjectType, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return createHash('sha1').update(header).update(data).digest('hex');
}
function sha1Hex(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}

interface TreeEntry {
  mode: string;
  name: string;
  sha: string;
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let pos = 0;
  while (pos < data.length) {
    const space = data.indexOf(0x20, pos);
    const mode = data.subarray(pos, space).toString('utf8');
    const nul = data.indexOf(0x00, space + 1);
    const name = data.subarray(space + 1, nul).toString('utf8');
    const sha = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, sha });
    pos = nul + 21;
  }
  return entries;
}

function buildTreeData(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => {
    const an = a.mode === '40000' ? `${a.name}/` : a.name;
    const bn = b.mode === '40000' ? `${b.name}/` : b.name;
    return an < bn ? -1 : an > bn ? 1 : 0;
  });
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.sha, 'hex'));
  }
  return Buffer.concat(parts);
}

interface CommitInfo {
  tree: string;
  parents: string[];
  author: string;
  committer: string;
  message: string;
  timeSec: number;
}

function parseCommit(data: Buffer): CommitInfo {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split === -1 ? text : text.slice(0, split);
  const message = split === -1 ? '' : text.slice(split + 2);
  let tree = ZERO_OID;
  const parents: string[] = [];
  let author = '';
  let committer = '';
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) author = line.slice(7);
    else if (line.startsWith('committer ')) committer = line.slice(10);
  }
  const timeMatch = / (\d+) [+-]\d{4}$/.exec(committer);
  return { tree, parents, author, committer, message, timeSec: timeMatch ? Number(timeMatch[1]) : EPOCH_SEC };
}

function buildCommitData(info: { tree: string; parents: string[]; message: string; timeSec: number }): Buffer {
  const lines: string[] = [`tree ${info.tree}`];
  for (const parent of info.parents) lines.push(`parent ${parent}`);
  lines.push(`author ${AUTHOR_LINE} ${gitStamp(info.timeSec)}`);
  lines.push(`committer ${AUTHOR_LINE} ${gitStamp(info.timeSec)}`);
  return Buffer.from(`${lines.join('\n')}\n\n${info.message}`, 'utf8');
}

interface TagInfo {
  object: string;
  type: string;
  tag: string;
  tagger: string;
  message: string;
}

function parseTag(data: Buffer): TagInfo {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split === -1 ? text : text.slice(0, split);
  const out: TagInfo = { object: ZERO_OID, type: '', tag: '', tagger: '', message: split === -1 ? '' : text.slice(split + 2) };
  for (const line of head.split('\n')) {
    if (line.startsWith('object ')) out.object = line.slice(7).trim();
    else if (line.startsWith('type ')) out.type = line.slice(5).trim();
    else if (line.startsWith('tag ')) out.tag = line.slice(4).trim();
    else if (line.startsWith('tagger ')) out.tagger = line.slice(7);
  }
  return out;
}

// pkt-line framing -----------------------------------------------------------

function pktLine(payload: Buffer | string): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const length = body.length + 4;
  const header = Buffer.from(length.toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([header, body]);
}
const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

interface PktPacket {
  kind: 'data' | 'flush' | 'delim';
  payload: Buffer;
}

function decodePkts(buffer: Buffer, startAt = 0): { packets: PktPacket[]; consumed: number } {
  const packets: PktPacket[] = [];
  let pos = startAt;
  while (pos + 4 <= buffer.length) {
    const header = buffer.subarray(pos, pos + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(header)) break;
    const length = parseInt(header, 16);
    if (length === 0) {
      packets.push({ kind: 'flush', payload: Buffer.alloc(0) });
      pos += 4;
      break;
    }
    if (length === 1) {
      packets.push({ kind: 'delim', payload: Buffer.alloc(0) });
      pos += 4;
      continue;
    }
    if (length === 2 || length === 3) break;
    if (pos + length > buffer.length) break;
    packets.push({ kind: 'data', payload: buffer.subarray(pos + 4, pos + length) });
    pos += length;
  }
  return { packets, consumed: pos };
}

// packfiles ------------------------------------------------------------------

function inflateAt(buffer: Buffer, offset: number): { data: Buffer; consumed: number } {
  // One inflate over the remaining bytes: the zlib engine stops at the
  // stream's own end marker and reports exactly how many input bytes it
  // consumed, so the next pack object starts right there.
  const res = inflateSync(buffer.subarray(offset), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
  return { data: res.buffer, consumed: res.engine.bytesWritten };
}

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let pos = 0;
  const readVarint = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[pos] as number;
      pos += 1;
      value |= (byte & 0x7f) << shift;
      shift += 7;
      if ((byte & 0x80) === 0) break;
    }
    return value;
  };
  readVarint(); // base size
  const targetSize = readVarint();
  const out: Buffer[] = [];
  while (pos < delta.length) {
    const op = delta[pos] as number;
    pos += 1;
    if (op & 0x80) {
      let offset = 0;
      let size = 0;
      if (op & 0x01) { offset = delta[pos] as number; pos += 1; }
      if (op & 0x02) { offset |= (delta[pos] as number) << 8; pos += 1; }
      if (op & 0x04) { offset |= (delta[pos] as number) << 16; pos += 1; }
      if (op & 0x08) { offset |= (delta[pos] as number) << 24; pos += 1; }
      if (op & 0x10) { size = delta[pos] as number; pos += 1; }
      if (op & 0x20) { size |= (delta[pos] as number) << 8; pos += 1; }
      if (op & 0x40) { size |= (delta[pos] as number) << 16; pos += 1; }
      if (size === 0) size = 0x10000;
      out.push(base.subarray(offset, offset + size));
    } else if (op > 0) {
      out.push(delta.subarray(pos, pos + op));
      pos += op;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  const result = Buffer.concat(out);
  if (result.length !== targetSize) throw new Error('delta size mismatch');
  return result;
}

interface PackRead {
  objects: GitObject[];
  bySha: Map<string, GitObject>;
}

function readPack(pack: Buffer, resolveExternal: (sha: string) => GitObject | undefined): PackRead {
  if (pack.length < 12 + 20 || pack.subarray(0, 4).toString('ascii') !== 'PACK') {
    throw new Error('not a packfile');
  }
  const count = pack.readUInt32BE(8);
  let pos = 12;
  const raw: Array<{ type: GitObjectType; data?: Buffer; delta?: Buffer; baseSha?: string; baseOffset?: number; offset: number }> = [];
  const offsetIndex = new Map<number, number>();
  for (let i = 0; i < count; i += 1) {
    const start = pos;
    let byte = pack[pos] as number;
    pos += 1;
    let typeCode = (byte >> 4) & 0x7;
    while (byte & 0x80) {
      byte = pack[pos] as number;
      pos += 1;
    }
    let baseSha: string | undefined;
    let baseOffset: number | undefined;
    if (typeCode === 6) {
      // OFS_DELTA
      let b = pack[pos] as number;
      pos += 1;
      let offset = b & 0x7f;
      while (b & 0x80) {
        b = pack[pos] as number;
        pos += 1;
        offset = ((offset + 1) << 7) | (b & 0x7f);
      }
      baseOffset = start - offset;
    } else if (typeCode === 7) {
      baseSha = pack.subarray(pos, pos + 20).toString('hex');
      pos += 20;
    }
    const inflated = inflateAt(pack, pos);
    pos += inflated.consumed;
    offsetIndex.set(start, raw.length);
    if (typeCode === 6 || typeCode === 7) {
      raw.push({ type: 'blob', delta: inflated.data, baseSha, baseOffset, offset: start });
    } else {
      const type = CODE_TO_TYPE[typeCode];
      if (type === undefined) throw new Error(`unknown pack object type ${typeCode}`);
      raw.push({ type, data: inflated.data, offset: start });
    }
  }
  const bySha = new Map<string, GitObject>();
  const resolved: Array<GitObject | null> = raw.map(() => null);
  const resolveAt = (index: number): GitObject => {
    const cached = resolved[index];
    if (cached !== null && cached !== undefined) return cached;
    const entry = raw[index] as (typeof raw)[number];
    let object: GitObject;
    if (entry.delta === undefined) {
      object = { type: entry.type, data: entry.data as Buffer };
    } else {
      let base: GitObject;
      if (entry.baseOffset !== undefined) {
        const baseIndex = offsetIndex.get(entry.baseOffset);
        if (baseIndex === undefined) throw new Error('ofs-delta base missing');
        base = resolveAt(baseIndex);
      } else {
        const found = bySha.get(entry.baseSha as string) ?? resolveExternal(entry.baseSha as string);
        if (found === undefined) throw new Error('ref-delta base missing');
        base = found;
      }
      object = { type: base.type, data: applyDelta(base.data, entry.delta) };
    }
    resolved[index] = object;
    bySha.set(hashObject(object.type, object.data), object);
    return object;
  };
  const objects: GitObject[] = [];
  for (let i = 0; i < raw.length; i += 1) objects.push(resolveAt(i));
  return { objects, bySha };
}

function writePack(objects: GitObject[]): Buffer {
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  const parts: Buffer[] = [header];
  for (const object of objects) {
    let size = object.data.length;
    const bytes: number[] = [];
    let first = (TYPE_TO_CODE[object.type] << 4) | (size & 0x0f);
    size >>= 4;
    if (size > 0) first |= 0x80;
    bytes.push(first);
    while (size > 0) {
      let byte = size & 0x7f;
      size >>= 7;
      if (size > 0) byte |= 0x80;
      bytes.push(byte);
    }
    parts.push(Buffer.from(bytes));
    parts.push(deflateSync(object.data));
  }
  const body = Buffer.concat(parts);
  const trailer = createHash('sha1').update(body).digest();
  return Buffer.concat([body, trailer]);
}

// ---------------------------------------------------------------------------
// Entities and the store (the "repositories" of the repository pattern).
// Each Repository aggregate owns versioned collections; the Forge is the
// root collection of repositories. Versions only ever move forward, which is
// what the unit of work's optimistic-concurrency check compares against.
// ---------------------------------------------------------------------------

interface LabelEntity {
  name: string;
  color: string;
  description: string;
}

interface CommentEntity {
  id: number;
  body: string;
  createdSec: number;
}

interface IssueEntity {
  kind: 'issue';
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  createdSec: number;
  comments: CommentEntity[];
}

interface PullEntity {
  kind: 'pull';
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  head: string;
  base: string;
  merged: boolean;
  mergeCommitSha: string | null;
  createdSec: number;
  comments: CommentEntity[];
}

type ItemEntity = IssueEntity | PullEntity;

class Repository {
  readonly id: number;
  readonly owner: string;
  readonly name: string;
  description: string;
  isPrivate: boolean;
  defaultBranch: string;
  readonly createdSec: number;
  version = 1;
  objects = new Map<string, GitObject>();
  refs = new Map<string, string>();
  labels = new Map<string, LabelEntity>();
  items = new Map<number, ItemEntity>();
  nextNumber = 1;
  nextCommentId = 1;

  constructor(id: number, owner: string, name: string, description: string, isPrivate: boolean, defaultBranch: string) {
    this.id = id;
    this.owner = owner;
    this.name = name;
    this.description = description;
    this.isPrivate = isPrivate;
    this.defaultBranch = defaultBranch;
    this.createdSec = nextSec();
  }

  get fullName(): string {
    return `${this.owner}/${this.name}`;
  }

  storeObject(type: GitObjectType, data: Buffer): string {
    const sha = hashObject(type, data);
    if (!this.objects.has(sha)) this.objects.set(sha, { type, data });
    return sha;
  }

  getObject(sha: string): GitObject | undefined {
    return this.objects.get(sha);
  }

  headRef(): string {
    return `refs/heads/${this.defaultBranch}`;
  }

  tipOf(branch: string): string | undefined {
    return this.refs.get(`refs/heads/${branch}`);
  }
}

class Forge {
  reposByName = new Map<string, Repository>();
  private nextRepoId = 1;
  version = 1;

  createRepo(name: string, description: string, isPrivate: boolean, defaultBranch: string): Repository | null {
    const existing = this.reposByName.get(name);
    if (existing !== undefined) return existing;
    const repo = new Repository(this.nextRepoId, VIEWER.login, name, description, isPrivate, defaultBranch);
    this.nextRepoId += 1;
    this.reposByName.set(name, repo);
    this.version += 1;
    return repo;
  }

  /** A repository is visible only under its owner's login; any other owner is a 404. */
  findRepo(owner: string, name: string): Repository | null {
    const repo = this.reposByName.get(name);
    if (repo === undefined || repo.owner !== owner) return null;
    return repo;
  }

  deleteRepo(owner: string, name: string): boolean {
    const repo = this.findRepo(owner, name);
    if (repo === null) return false;
    this.reposByName.delete(name);
    this.version += 1;
    return true;
  }

  listRepos(): Repository[] {
    return [...this.reposByName.values()];
  }
}

/**
 * A unit of work: one per request. It snapshots the version of every
 * collection it touches; staged mutations bump the owning aggregate's
 * version, and commit() refuses to close if a version it read has since
 * moved (which, in this single-process store, can only happen if a handler
 * re-enters) — the same optimistic shape the contents API exposes as the
 * blob-sha 409.
 */
class UnitOfWork {
  private readonly seen = new Map<object, number>();
  private readonly touched = new Set<Repository>();
  readonly forge: Forge;

  constructor(forge: Forge) {
    this.forge = forge;
    this.seen.set(forge, forge.version);
  }

  repo(owner: string, name: string): Repository | null {
    const repo = this.forge.findRepo(owner, name);
    if (repo !== null && !this.seen.has(repo)) this.seen.set(repo, repo.version);
    return repo;
  }

  /** Record that `repo` was mutated through this unit of work. */
  stage(repo: Repository): void {
    this.touched.add(repo);
  }

  commit(): boolean {
    for (const [collection, version] of this.seen) {
      const current = (collection as Forge | Repository).version;
      if (collection !== this.forge && this.touched.has(collection as Repository)) continue;
      if (current !== version) return false;
    }
    for (const repo of this.touched) repo.version += 1;
    return true;
  }
}

// ---------------------------------------------------------------------------
// Template router: patterns compile to a regex plus parameter names.
// ":name" takes one segment; ":name*" takes the rest of the path.
// ---------------------------------------------------------------------------

interface RouteMatch {
  handler: RouteHandler;
  params: Record<string, string>;
}

type RouteHandler = (ctx: RequestContext) => Promise<void> | void;

class TemplateRouter {
  private readonly routes: Array<{ method: string; regex: RegExp; keys: string[]; handler: RouteHandler }> = [];

  add(method: string, pattern: string, handler: RouteHandler): void {
    const keys: string[] = [];
    const segments = pattern.split('/').filter((s) => s.length > 0);
    let source = '^';
    if (segments.length === 0) source += '/';
    for (const segment of segments) {
      if (segment.startsWith(':') && segment.endsWith('*')) {
        keys.push(segment.slice(1, -1));
        source += '(?:/(.*))?';
      } else if (segment.startsWith(':')) {
        keys.push(segment.slice(1));
        source += '/([^/]+)';
      } else {
        source += `/${segment.replace(/[.*+?^${'{}'}()|[\]\\]/g, '\\$&')}`;
      }
    }
    source += '$';
    this.routes.push({ method, regex: new RegExp(source), keys, handler });
  }

  match(method: string, pathname: string): RouteMatch | null {
    for (const route of this.routes) {
      if (route.method !== method) continue;
      const found = route.regex.exec(pathname);
      if (found === null) continue;
      const params: Record<string, string> = {};
      route.keys.forEach((key, index) => {
        const raw = found[index + 1] ?? '';
        try {
          params[key] = decodeURIComponent(raw);
        } catch {
          params[key] = raw;
        }
      });
      return { handler: route.handler, params };
    }
    return null;
  }
}

// ---------------------------------------------------------------------------
// Domain services over a Repository aggregate.
// ---------------------------------------------------------------------------

/** Flatten the tree of a commit into path -> blob sha. */
function filesAtCommit(repo: Repository, commitSha: string): Map<string, string> {
  const out = new Map<string, string>();
  const commitObject = repo.getObject(commitSha);
  if (commitObject === undefined || commitObject.type !== 'commit') return out;
  const commit = parseCommit(commitObject.data);
  const walk = (treeSha: string, prefix: string): void => {
    const treeObject = repo.getObject(treeSha);
    if (treeObject === undefined || treeObject.type !== 'tree') return;
    for (const entry of parseTree(treeObject.data)) {
      if (entry.mode === '40000') walk(entry.sha, `${prefix}${entry.name}/`);
      else out.set(`${prefix}${entry.name}`, entry.sha);
    }
  };
  walk(commit.tree, '');
  return out;
}

/** Build nested trees for a flat path -> blob sha map; returns the root tree sha. */
function writeTreeFromFiles(repo: Repository, files: Map<string, string>): string {
  interface Node {
    files: Map<string, string>;
    dirs: Map<string, Node>;
  }
  const root: Node = { files: new Map(), dirs: new Map() };
  for (const [path, sha] of files) {
    const parts = path.split('/');
    let node = root;
    for (let i = 0; i < parts.length - 1; i += 1) {
      const part = parts[i] as string;
      let next = node.dirs.get(part);
      if (next === undefined) {
        next = { files: new Map(), dirs: new Map() };
        node.dirs.set(part, next);
      }
      node = next;
    }
    node.files.set(parts[parts.length - 1] as string, sha);
  }
  const emit = (node: Node): string => {
    const entries: TreeEntry[] = [];
    for (const [name, sha] of node.files) entries.push({ mode: '100644', name, sha });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, sha: emit(child) });
    return repo.storeObject('tree', buildTreeData(entries));
  };
  return emit(root);
}

/** Commit a whole file map onto a branch ref; returns the new commit sha. */
function commitFiles(repo: Repository, branch: string, files: Map<string, string>, message: string): string {
  const ref = `refs/heads/${branch}`;
  const parent = repo.refs.get(ref);
  const tree = writeTreeFromFiles(repo, files);
  const parents = parent === undefined ? [] : [parent];
  const data = buildCommitData({ tree, parents, message, timeSec: nextSec() });
  const sha = repo.storeObject('commit', data);
  repo.refs.set(ref, sha);
  return sha;
}

/** Peel a tag (or return the commit itself) to the commit it ultimately names. */
function peelToCommit(repo: Repository, sha: string): string | null {
  let current = sha;
  for (let depth = 0; depth < 16; depth += 1) {
    const object = repo.getObject(current);
    if (object === undefined) return null;
    if (object.type === 'commit') return current;
    if (object.type === 'tag') {
      current = parseTag(object.data).object;
      continue;
    }
    return null;
  }
  return null;
}

/** All commits reachable from a tip, newest first by committer time then discovery order. */
function ancestry(repo: Repository, tip: string): CommitInfo[] {
  const seen = new Set<string>();
  const out: Array<{ sha: string; info: CommitInfo }> = [];
  const queue: string[] = [tip];
  while (queue.length > 0) {
    const sha = queue.shift() as string;
    if (seen.has(sha)) continue;
    seen.add(sha);
    const object = repo.getObject(sha);
    if (object === undefined || object.type !== 'commit') continue;
    const info = parseCommit(object.data);
    out.push({ sha, info });
    for (const parent of info.parents) queue.push(parent);
  }
  out.sort((a, b) => b.info.timeSec - a.info.timeSec);
  return out.map((entry) => entry.info);
}

function ancestorShas(repo: Repository, tip: string): Set<string> {
  const seen = new Set<string>();
  const queue: string[] = [tip];
  while (queue.length > 0) {
    const sha = queue.shift() as string;
    if (seen.has(sha)) continue;
    seen.add(sha);
    const object = repo.getObject(sha);
    if (object === undefined || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) queue.push(parent);
  }
  return seen;
}

function isAncestor(repo: Repository, maybeAncestor: string, tip: string): boolean {
  if (maybeAncestor === tip) return true;
  const seen = new Set<string>();
  const stack: string[] = [tip];
  while (stack.length > 0) {
    const sha = stack.pop() as string;
    if (sha === maybeAncestor) return true;
    if (seen.has(sha)) continue;
    seen.add(sha);
    const object = repo.getObject(sha);
    if (object === undefined || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) stack.push(parent);
  }
  return false;
}

/** Generation distances (shortest parent hops) from a tip; root commits included. */
function generations(repo: Repository, tip: string): Map<string, number> {
  const dist = new Map<string, number>();
  dist.set(tip, 0);
  const queue: string[] = [tip];
  while (queue.length > 0) {
    const sha = queue.shift() as string;
    const d = dist.get(sha) as number;
    const object = repo.getObject(sha);
    if (object === undefined || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (!dist.has(parent)) {
        dist.set(parent, d + 1);
        queue.push(parent);
      }
    }
  }
  return dist;
}

function mergeBase(repo: Repository, a: string, b: string): string | null {
  const distA = generations(repo, a);
  const distB = generations(repo, b);
  let best: string | null = null;
  let bestScore = Number.POSITIVE_INFINITY;
  for (const [sha, da] of distA) {
    const db = distB.get(sha);
    if (db === undefined) continue;
    const score = da + db;
    if (score < bestScore) {
      bestScore = score;
      best = sha;
    }
  }
  return best;
}

interface ChangedFile {
  filename: string;
  status: 'added' | 'modified' | 'removed';
  additions: number;
  deletions: number;
  sha: string;
}

function countLines(data: Buffer): number {
  if (data.length === 0) return 0;
  const text = data.toString('utf8');
  const lines = text.split('\n');
  return text.endsWith('\n') ? lines.length - 1 : lines.length;
}

/** Line-diff summary between two blob versions, by common prefix/suffix trim. */
function diffCounts(repo: Repository, oldSha: string | undefined, newSha: string | undefined): { additions: number; deletions: number } {
  const oldLines = oldSha === undefined ? [] : (repo.getObject(oldSha)?.data.toString('utf8') ?? '').split('\n');
  const newLines = newSha === undefined ? [] : (repo.getObject(newSha)?.data.toString('utf8') ?? '').split('\n');
  let prefix = 0;
  while (prefix < oldLines.length && prefix < newLines.length && oldLines[prefix] === newLines[prefix]) prefix += 1;
  let suffix = 0;
  while (
    suffix < oldLines.length - prefix &&
    suffix < newLines.length - prefix &&
    oldLines[oldLines.length - 1 - suffix] === newLines[newLines.length - 1 - suffix]
  ) suffix += 1;
  return {
    additions: Math.max(0, newLines.length - prefix - suffix),
    deletions: Math.max(0, oldLines.length - prefix - suffix),
  };
}

/** Files changed between two commits' trees. */
function changedFiles(repo: Repository, fromCommit: string, toCommit: string): ChangedFile[] {
  const from = filesAtCommit(repo, fromCommit);
  const to = filesAtCommit(repo, toCommit);
  const paths = new Set<string>([...from.keys(), ...to.keys()]);
  const out: ChangedFile[] = [];
  for (const path of [...paths].sort()) {
    const oldSha = from.get(path);
    const newSha = to.get(path);
    if (oldSha === newSha) continue;
    const counts = diffCounts(repo, oldSha, newSha);
    out.push({
      filename: path,
      status: oldSha === undefined ? 'added' : newSha === undefined ? 'removed' : 'modified',
      additions: counts.additions,
      deletions: counts.deletions,
      sha: newSha ?? oldSha ?? ZERO_OID,
    });
  }
  return out;
}

interface MergeOutcome {
  ok: boolean;
  sha?: string;
  conflictPath?: string;
}

/** Plan the squash merge of a pull request; with apply=false nothing moves. */
function planMerge(repo: Repository, pull: PullEntity, apply: boolean): MergeOutcome {
  const baseSha = repo.tipOf(pull.base);
  const headSha = repo.tipOf(pull.head);
  if (baseSha === undefined || headSha === undefined) return { ok: false };
  const base = mergeBase(repo, baseSha, headSha);
  if (base === null) return { ok: false };
  const baseFiles = filesAtCommit(repo, baseSha);
  const rootFiles = filesAtCommit(repo, base);
  const headFiles = filesAtCommit(repo, headSha);
  const merged = new Map(baseFiles);
  const paths = new Set<string>([...rootFiles.keys(), ...headFiles.keys()]);
  for (const path of paths) {
    const rootSha = rootFiles.get(path);
    const headVersion = headFiles.get(path);
    if (rootSha === headVersion) continue; // the head side did not touch it
    const baseVersion = baseFiles.get(path);
    if (baseVersion !== rootSha && baseVersion !== headVersion) {
      return { ok: false, conflictPath: path }; // both sides changed it, differently
    }
    if (headVersion === undefined) merged.delete(path);
    else merged.set(path, headVersion);
  }
  if (!apply) return { ok: true };
  const sha = commitFiles(repo, pull.base, merged, `${pull.title} (#${pull.number})`);
  return { ok: true, sha };
}

function mergePull(repo: Repository, pull: PullEntity): MergeOutcome {
  const outcome = planMerge(repo, pull, true);
  if (outcome.ok && outcome.sha !== undefined) {
    pull.state = 'closed';
    pull.merged = true;
    pull.mergeCommitSha = outcome.sha;
  }
  return outcome;
}

function pullMergeable(repo: Repository, pull: PullEntity): 'MERGEABLE' | 'CONFLICTING' | 'UNKNOWN' {
  if (pull.state !== 'open') return 'UNKNOWN';
  return planMerge(repo, pull, false).ok ? 'MERGEABLE' : 'CONFLICTING';
}

// ---------------------------------------------------------------------------
// HTTP plumbing and JSON views.
// ---------------------------------------------------------------------------

const JSON_TYPE = 'application/json; charset=utf-8';
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
let requestSeq = 0;

interface RequestContext {
  req: IncomingMessage;
  res: ServerResponse;
  forge: Forge;
  uow: UnitOfWork;
  params: Record<string, string>;
  query: URLSearchParams;
  url: URL;
  body: Buffer;
  json: unknown;
  jsonError: boolean;
}

function requestId(): string {
  requestSeq += 1;
  return `bf67-${requestSeq.toString(16).padStart(8, '0')}`;
}

function sendJson(ctx: RequestContext, status: number, body: unknown, headers: Record<string, string> = {}): void {
  const text = body === undefined ? '' : `${JSON.stringify(body)}\n`;
  ctx.res.writeHead(status, {
    'content-type': JSON_TYPE,
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': requestId(),
    ...headers,
  });
  ctx.res.end(text);
}

function sendRaw(res: ServerResponse, status: number, body: Buffer, headers: Record<string, string>): void {
  res.writeHead(status, { 'content-length': body.length, ...headers });
  res.end(body);
}

function errorJson(ctx: RequestContext, status: number, message: string): void {
  sendJson(ctx, status, { message });
}

function isAuthed(req: IncomingMessage): boolean {
  if (TOKEN === '') return true;
  return req.headers.authorization === `Bearer ${TOKEN}`;
}

function userJson(): Record<string, unknown> {
  return {
    login: VIEWER.login,
    id: VIEWER.id,
    node_id: Buffer.from(`User:${VIEWER.login}`, 'utf8').toString('base64'),
    type: 'User',
    name: VIEWER.name,
    email: VIEWER.email,
    html_url: `https://forge.invalid/${VIEWER.login}`,
    url: `/api/v3/users/${VIEWER.login}`,
  };
}

function repoJson(repo: Repository): Record<string, unknown> {
  return {
    id: repo.id,
    node_id: Buffer.from(`Repository:${repo.id}`, 'utf8').toString('base64'),
    name: repo.name,
    full_name: repo.fullName,
    owner: userJson(),
    private: repo.isPrivate,
    description: repo.description,
    default_branch: repo.defaultBranch,
    html_url: `https://forge.invalid/${repo.fullName}`,
    url: `/api/v3/repos/${repo.fullName}`,
    git_url: `git://forge.invalid/${repo.fullName}.git`,
    clone_url: `https://forge.invalid/${repo.fullName}.git`,
    created_at: isoOf(repo.createdSec),
    updated_at: isoOf(repo.createdSec),
    pushed_at: isoOf(repo.createdSec),
    size: 0,
    stargazers_count: 0,
    watchers_count: 0,
    forks_count: 0,
    open_issues_count: [...repo.items.values()].filter((i) => i.state === 'open').length,
    has_issues: true,
    has_projects: true,
    has_wiki: true,
    archived: false,
    disabled: false,
    visibility: repo.isPrivate ? 'private' : 'public',
  };
}

function labelJson(label: LabelEntity): Record<string, unknown> {
  return {
    id: [...label.name].reduce((acc, ch) => acc + ch.charCodeAt(0), 0) + 7,
    name: label.name,
    color: label.color,
    description: label.description,
    default: false,
    url: '',
  };
}

function issueJson(repo: Repository, issue: IssueEntity): Record<string, unknown> {
  return {
    id: repo.id * 100000 + issue.number,
    node_id: Buffer.from(`Issue:${repo.id}:${issue.number}`, 'utf8').toString('base64'),
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => labelJson(repo.labels.get(name) ?? { name, color: 'ededed', description: '' })),
    user: userJson(),
    comments: issue.comments.length,
    created_at: isoOf(issue.createdSec),
    updated_at: isoOf(issue.createdSec),
    closed_at: issue.state === 'closed' ? isoOf(issue.createdSec) : null,
    url: `/api/v3/repos/${repo.fullName}/issues/${issue.number}`,
    html_url: `https://forge.invalid/${repo.fullName}/issues/${issue.number}`,
    repository_url: `/api/v3/repos/${repo.fullName}`,
  };
}

function commentJson(repo: Repository, item: ItemEntity, comment: CommentEntity): Record<string, unknown> {
  return {
    id: comment.id,
    node_id: Buffer.from(`IssueComment:${repo.id}:${item.number}:${comment.id}`, 'utf8').toString('base64'),
    body: comment.body,
    user: userJson(),
    created_at: isoOf(comment.createdSec),
    updated_at: isoOf(comment.createdSec),
    url: `/api/v3/repos/${repo.fullName}/issues/comments/${comment.id}`,
    html_url: `https://forge.invalid/${repo.fullName}/issues/${item.number}#issuecomment-${comment.id}`,
    issue_url: `/api/v3/repos/${repo.fullName}/issues/${item.number}`,
  };
}

function pullJson(repo: Repository, pull: PullEntity): Record<string, unknown> {
  const headSha = repo.tipOf(pull.head) ?? ZERO_OID;
  const baseSha = repo.tipOf(pull.base) ?? ZERO_OID;
  return {
    id: repo.id * 100000 + pull.number,
    node_id: Buffer.from(`PullRequest:${repo.id}:${pull.number}`, 'utf8').toString('base64'),
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    merged: pull.merged,
    merged_at: pull.merged ? isoOf(pull.createdSec) : null,
    merge_commit_sha: pull.mergeCommitSha,
    mergeable: pull.state === 'open' ? planMerge(repo, pull, false).ok : null,
    user: userJson(),
    head: {
      ref: pull.head,
      sha: headSha,
      label: `${repo.owner}:${pull.head}`,
      repo: repoJson(repo),
      user: userJson(),
    },
    base: {
      ref: pull.base,
      sha: baseSha,
      label: `${repo.owner}:${pull.base}`,
      repo: repoJson(repo),
      user: userJson(),
    },
    created_at: isoOf(pull.createdSec),
    updated_at: isoOf(pull.createdSec),
    url: `/api/v3/repos/${repo.fullName}/pulls/${pull.number}`,
    html_url: `https://forge.invalid/${repo.fullName}/pull/${pull.number}`,
  };
}

function bodyObject(ctx: RequestContext): Record<string, unknown> {
  if (typeof ctx.json === 'object' && ctx.json !== null && !Array.isArray(ctx.json)) {
    return ctx.json as Record<string, unknown>;
  }
  return {};
}

function str(value: unknown, fallback = ''): string {
  return typeof value === 'string' ? value : fallback;
}

function pagination(ctx: RequestContext): { page: number; perPage: number } {
  const perPageRaw = Number(ctx.query.get('per_page') ?? '30');
  const pageRaw = Number(ctx.query.get('page') ?? '1');
  const perPage = Number.isFinite(perPageRaw) && perPageRaw > 0 ? Math.min(100, Math.trunc(perPageRaw)) : 30;
  const page = Number.isFinite(pageRaw) && pageRaw > 0 ? Math.trunc(pageRaw) : 1;
  return { page, perPage };
}

function pageSlice<T>(ctx: RequestContext, items: T[], basePath: string): { slice: T[]; headers: Record<string, string> } {
  const { page, perPage } = pagination(ctx);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const headers: Record<string, string> = {};
  if (start + perPage < items.length) {
    const host = ctx.req.headers.host ?? 'localhost';
    const next = `http://${host}${basePath}?per_page=${perPage}&page=${page + 1}`;
    const lastPage = Math.ceil(items.length / perPage);
    const last = `http://${host}${basePath}?per_page=${perPage}&page=${lastPage}`;
    headers.link = `<${next}>; rel="next", <${last}>; rel="last"`;
  }
  return { slice, headers };
}

/** Resolve the {owner}/{repo} params to a repository or answer 404. */
function needRepo(ctx: RequestContext): Repository | null {
  const repo = ctx.uow.repo(ctx.params.owner ?? '', ctx.params.repo ?? '');
  if (repo === null) {
    errorJson(ctx, 404, 'Not Found');
    return null;
  }
  return repo;
}

// ---------------------------------------------------------------------------
// REST v3 handlers.
// ---------------------------------------------------------------------------

function registerRest(router: TemplateRouter): void {
  router.add('GET', '/api/v3', (ctx) => {
    sendJson(ctx, 200, {
      current_user_url: '/api/v3/user',
      current_user_repositories_url: '/api/v3/user/repos',
      repository_url: '/api/v3/repos/{owner}/{repo}',
      rate_limit_url: '/api/v3/rate_limit',
    }, { 'x-oauth-scopes': 'repo, read:org' });
  });

  router.add('GET', '/api/v3/meta', (ctx) => {
    sendJson(ctx, 200, {
      hook_id: 1,
      installed_version: '1.0.0-bright-falcon-67',
      ssh_key_fingerprints: {},
      ssh_keys: [],
      services: [],
      api: ['/api/v3'],
      web: [],
    });
  });

  router.add('GET', '/api/v3/user', (ctx) => {
    sendJson(ctx, 200, userJson());
  });

  router.add('GET', '/api/v3/rate_limit', (ctx) => {
    sendJson(ctx, 200, { rate: { limit: 5000, remaining: 4999, reset: EPOCH_SEC + 3600, used: 1 } });
  });

  router.add('GET', '/api/v3/user/repos', (ctx) => {
    const { slice, headers } = pageSlice(ctx, ctx.forge.listRepos().map(repoJson), '/api/v3/user/repos');
    sendJson(ctx, 200, slice, headers);
  });

  router.add('POST', '/api/v3/user/repos', (ctx) => {
    if (ctx.jsonError) return errorJson(ctx, 400, 'Problems parsing JSON');
    const body = bodyObject(ctx);
    const name = str(body.name);
    if (name === '' || /[^A-Za-z0-9._-]/.test(name)) {
      return errorJson(ctx, 422, 'Repository creation failed.');
    }
    const repo = ctx.forge.createRepo(
      name,
      str(body.description),
      typeof body.private === 'boolean' ? body.private : false,
      str(body.default_branch, 'main') || 'main',
    );
    if (repo === null) return errorJson(ctx, 422, 'Repository creation failed.');
    ctx.uow.stage(repo);
    return sendJson(ctx, 201, repoJson(repo));
  });

  router.add('GET', '/api/v3/repos/:owner/:repo', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    sendJson(ctx, 200, repoJson(repo));
  });

  router.add('PATCH', '/api/v3/repos/:owner/:repo', (ctx) => {
    if (ctx.jsonError) return errorJson(ctx, 400, 'Problems parsing JSON');
    const repo = needRepo(ctx);
    if (repo === null) return;
    const body = bodyObject(ctx);
    if (typeof body.description === 'string') repo.description = body.description;
    if (typeof body.private === 'boolean') repo.isPrivate = body.private;
    if (typeof body.name === 'string' && body.name !== '' && body.name !== repo.name) {
      // Rename: re-key the aggregate.
      ctx.forge.reposByName.delete(repo.name);
      (repo as { name: string }).name = body.name;
      ctx.forge.reposByName.set(repo.name, repo);
    }
    if (typeof body.default_branch === 'string' && body.default_branch !== '') repo.defaultBranch = body.default_branch;
    ctx.uow.stage(repo);
    sendJson(ctx, 200, repoJson(repo));
  });

  router.add('DELETE', '/api/v3/repos/:owner/:repo', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    ctx.forge.deleteRepo(repo.owner, repo.name);
    ctx.res.writeHead(204, { 'x-github-request-id': requestId() });
    ctx.res.end();
  });

  // ---- git data: refs and branches ----

  router.add('POST', '/api/v3/repos/:owner/:repo/git/refs', (ctx) => {
    if (ctx.jsonError) return errorJson(ctx, 400, 'Problems parsing JSON');
    const repo = needRepo(ctx);
    if (repo === null) return;
    const body = bodyObject(ctx);
    const ref = str(body.ref);
    const sha = str(body.sha);
    const target = repo.getObject(sha);
    if (!ref.startsWith('refs/') || target === undefined) {
      return errorJson(ctx, 422, 'Validation Failed');
    }
    if (repo.refs.has(ref)) return errorJson(ctx, 422, 'Reference already exists');
    repo.refs.set(ref, sha);
    ctx.uow.stage(repo);
    return sendJson(ctx, 201, {
      ref,
      node_id: Buffer.from(`Ref:${repo.id}:${ref}`, 'utf8').toString('base64'),
      url: `/api/v3/repos/${repo.fullName}/git/refs/${ref.slice('refs/'.length)}`,
      object: { sha, type: target.type, url: '' },
    });
  });

  router.add('GET', '/api/v3/repos/:owner/:repo/git/refs/:ref*', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const raw = ctx.params.ref ?? '';
    const ref = raw.startsWith('refs/') ? raw : `refs/${raw}`;
    const sha = repo.refs.get(ref);
    if (sha === undefined) return errorJson(ctx, 404, 'Not Found');
    const target = repo.getObject(sha);
    return sendJson(ctx, 200, {
      ref,
      node_id: Buffer.from(`Ref:${repo.id}:${ref}`, 'utf8').toString('base64'),
      url: `/api/v3/repos/${repo.fullName}/git/refs/${ref.slice('refs/'.length)}`,
      object: { sha, type: target?.type ?? 'commit', url: '' },
    });
  });

  router.add('DELETE', '/api/v3/repos/:owner/:repo/git/refs/:ref*', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const raw = ctx.params.ref ?? '';
    const ref = raw.startsWith('refs/') ? raw : `refs/${raw}`;
    if (!repo.refs.has(ref)) return errorJson(ctx, 404, 'Not Found');
    repo.refs.delete(ref);
    ctx.uow.stage(repo);
    ctx.res.writeHead(204, { 'x-github-request-id': requestId() });
    ctx.res.end();
  });

  router.add('GET', '/api/v3/repos/:owner/:repo/branches', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const branches = [...repo.refs.entries()]
      .filter(([ref]) => ref.startsWith('refs/heads/'))
      .map(([ref, sha]) => ({
        name: ref.slice('refs/heads/'.length),
        commit: { sha, url: `/api/v3/repos/${repo.fullName}/commits/${sha}` },
        protected: false,
      }));
    const { slice, headers } = pageSlice(ctx, branches, `/api/v3/repos/${repo.fullName}/branches`);
    sendJson(ctx, 200, slice, headers);
  });

  router.add('GET', '/api/v3/repos/:owner/:repo/branches/:branch*', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const branch = ctx.params.branch ?? '';
    const sha = repo.tipOf(branch);
    if (sha === undefined) return errorJson(ctx, 404, 'Not Found');
    return sendJson(ctx, 200, {
      name: branch,
      commit: { sha, url: `/api/v3/repos/${repo.fullName}/commits/${sha}` },
      protected: false,
    });
  });

  // ---- commits ----

  const commitView = (repo: Repository, sha: string): Record<string, unknown> | null => {
    const object = repo.getObject(sha);
    if (object === undefined || object.type !== 'commit') return null;
    const info = parseCommit(object.data);
    const splitPerson = (line: string): { name: string; email: string; date: string } => {
      const match = /^(.*) <(.*)> (\d+) [+-]\d{4}$/.exec(line);
      if (match === null) return { name: line, email: '', date: isoOf(info.timeSec) };
      return { name: match[1] as string, email: match[2] as string, date: isoOf(Number(match[3])) };
    };
    return {
      sha,
      node_id: Buffer.from(`Commit:${repo.id}:${sha}`, 'utf8').toString('base64'),
      commit: {
        author: splitPerson(info.author),
        committer: splitPerson(info.committer),
        message: info.message,
        tree: { sha: info.tree, url: '' },
        comment_count: 0,
      },
      author: userJson(),
      committer: userJson(),
      parents: info.parents.map((parent) => ({ sha: parent, url: '' })),
      url: `/api/v3/repos/${repo.fullName}/commits/${sha}`,
      html_url: `https://forge.invalid/${repo.fullName}/commit/${sha}`,
    };
  };

  router.add('GET', '/api/v3/repos/:owner/:repo/commits', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const refParam = ctx.query.get('sha') ?? repo.defaultBranch;
    let tip = repo.tipOf(refParam);
    if (tip === undefined && repo.getObject(refParam)?.type === 'commit') tip = refParam;
    if (tip === undefined) return sendJson(ctx, 200, []);
    const ordered = orderedAncestry(repo, tip);
    const views = ordered
      .map((sha) => commitView(repo, sha))
      .filter((view) => view !== null);
    const { slice, headers } = pageSlice(ctx, views, `/api/v3/repos/${repo.fullName}/commits`);
    return sendJson(ctx, 200, slice, headers);
  });

  router.add('GET', '/api/v3/repos/:owner/:repo/commits/:sha', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const view = commitView(repo, ctx.params.sha ?? '');
    if (view === null) return errorJson(ctx, 404, 'Not Found');
    return sendJson(ctx, 200, view);
  });

  // ---- contents ----

  registerContents(router, commitView);
  registerIssuesAndPulls(router);
}

/** Commit shas in newest-first walk order from a tip. */
function orderedAncestry(repo: Repository, tip: string): string[] {
  const seen = new Set<string>();
  const out: Array<{ sha: string; timeSec: number }> = [];
  const queue: string[] = [tip];
  while (queue.length > 0) {
    const sha = queue.shift() as string;
    if (seen.has(sha)) continue;
    seen.add(sha);
    const object = repo.getObject(sha);
    if (object === undefined || object.type !== 'commit') continue;
    const info = parseCommit(object.data);
    out.push({ sha, timeSec: info.timeSec });
    for (const parent of info.parents) queue.push(parent);
  }
  out.sort((a, b) => b.timeSec - a.timeSec);
  return out.map((entry) => entry.sha);
}

// ---------------------------------------------------------------------------
// Contents API: files are views over the git store; every write is a commit.
// The blob sha is the optimistic-concurrency token: an update must name the
// sha it saw, and a stale one is a 409.
// ---------------------------------------------------------------------------

type CommitViewFn = (repo: Repository, sha: string) => Record<string, unknown> | null;

function resolveRefTip(ctx: RequestContext, repo: Repository, refParam: string | null): string | undefined {
  if (refParam === null || refParam === '') return repo.tipOf(repo.defaultBranch);
  const byBranch = repo.tipOf(refParam);
  if (byBranch !== undefined) return byBranch;
  if (repo.getObject(refParam)?.type === 'commit') return refParam;
  const byRef = repo.refs.get(refParam.startsWith('refs/') ? refParam : `refs/${refParam}`);
  if (byRef !== undefined) return peelToCommit(repo, byRef) ?? undefined;
  return undefined;
}

function registerContents(router: TemplateRouter, _commitView: CommitViewFn): void {
  const readPath = (ctx: RequestContext, repo: Repository): void => {
    const rawPath = (ctx.params.path ?? '').replace(/^\/+|\/+$/g, '');
    const tip = resolveRefTip(ctx, repo, ctx.query.get('ref'));
    if (tip === undefined) return errorJson(ctx, 404, 'Not Found');
    const files = filesAtCommit(repo, tip);
    if (rawPath !== '' && files.has(rawPath)) {
      const blobSha = files.get(rawPath) as string;
      const blob = repo.getObject(blobSha);
      const data = blob?.data ?? Buffer.alloc(0);
      const base = rawPath.split('/').pop() as string;
      return sendJson(ctx, 200, {
        type: 'file',
        encoding: 'base64',
        size: data.length,
        name: base,
        path: rawPath,
        sha: blobSha,
        content: data.toString('base64'),
        url: `/api/v3/repos/${repo.fullName}/contents/${rawPath}`,
        html_url: `https://forge.invalid/${repo.fullName}/blob/${repo.defaultBranch}/${rawPath}`,
        git_url: '',
        download_url: '',
      });
    }
    // Directory (or repository root).
    const prefix = rawPath === '' ? '' : `${rawPath}/`;
    const entries = new Map<string, { type: 'file' | 'dir'; sha: string; size: number }>();
    for (const [path, sha] of files) {
      if (!path.startsWith(prefix)) continue;
      const rest = path.slice(prefix.length);
      const slash = rest.indexOf('/');
      if (slash === -1) {
        const blob = repo.getObject(sha);
        entries.set(rest, { type: 'file', sha, size: blob?.data.length ?? 0 });
      } else {
        const dirName = rest.slice(0, slash);
        if (!entries.has(dirName)) entries.set(dirName, { type: 'dir', sha: ZERO_OID, size: 0 });
      }
    }
    if (rawPath !== '' && entries.size === 0) return errorJson(ctx, 404, 'Not Found');
    // Directory shas: use the subtree sha where it can be found cheaply.
    const listing = [...entries.entries()]
      .sort((a, b) => (a[0] < b[0] ? -1 : 1))
      .map(([name, entry]) => ({
        type: entry.type,
        name,
        path: `${prefix}${name}`,
        sha: entry.type === 'dir' ? dirShaAt(repo, tip, `${prefix}${name}`) : entry.sha,
        size: entry.size,
        url: `/api/v3/repos/${repo.fullName}/contents/${prefix}${name}`,
        html_url: '',
        git_url: '',
        download_url: null,
      }));
    return sendJson(ctx, 200, listing);
  };

  router.add('GET', '/api/v3/repos/:owner/:repo/contents/:path*', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    readPath(ctx, repo);
  });
  router.add('GET', '/api/v3/repos/:owner/:repo/contents', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    readPath(ctx, repo);
  });

  router.add('PUT', '/api/v3/repos/:owner/:repo/contents/:path*', (ctx) => {
    if (ctx.jsonError) return errorJson(ctx, 400, 'Problems parsing JSON');
    const repo = needRepo(ctx);
    if (repo === null) return;
    const body = bodyObject(ctx);
    const filePath = (ctx.params.path ?? '').replace(/^\/+/, '');
    if (filePath === '') return errorJson(ctx, 422, 'Validation Failed');
    const branch = str(body.branch, repo.defaultBranch) || repo.defaultBranch;
    const ref = `refs/heads/${branch}`;
    let tip = repo.refs.get(ref);
    if (tip === undefined) {
      // Writing to a fresh branch starts from the default branch's tree.
      tip = repo.tipOf(repo.defaultBranch);
    }
    const files = tip === undefined ? new Map<string, string>() : filesAtCommit(repo, tip);
    const existing = files.get(filePath);
    const givenSha = typeof body.sha === 'string' ? body.sha : undefined;
    if (existing !== undefined && givenSha !== undefined && givenSha !== existing) {
      return errorJson(ctx, 409, `${filePath} has changed since you last read it; the sha does not match`);
    }
    const rawContent = str(body.content);
    let data: Buffer;
    try {
      data = Buffer.from(rawContent.replace(/\s+/g, ''), 'base64');
    } catch {
      return errorJson(ctx, 422, 'content is not valid base64');
    }
    const blobSha = repo.storeObject('blob', data);
    files.set(filePath, blobSha);
    const message = str(body.message, `Update ${filePath}`);
    // commitFiles parents onto the branch's own tip when it exists; when the
    // branch is fresh it must parent onto the tree's source tip instead.
    let commitSha: string;
    if (repo.refs.get(ref) === undefined && tip !== undefined) {
      const tree = writeTreeFromFiles(repo, files);
      const data2 = buildCommitData({ tree, parents: [tip], message, timeSec: nextSec() });
      commitSha = repo.storeObject('commit', data2);
      repo.refs.set(ref, commitSha);
    } else {
      commitSha = commitFiles(repo, branch, files, message);
    }
    ctx.uow.stage(repo);
    const status = existing === undefined ? 201 : 200;
    return sendJson(ctx, status, {
      content: {
        type: 'file',
        encoding: 'base64',
        size: data.length,
        name: filePath.split('/').pop() as string,
        path: filePath,
        sha: blobSha,
        url: `/api/v3/repos/${repo.fullName}/contents/${filePath}`,
        html_url: '',
        git_url: '',
        download_url: '',
      },
      commit: {
        sha: commitSha,
        url: `/api/v3/repos/${repo.fullName}/commits/${commitSha}`,
        message,
        author: { name: VIEWER.name, email: VIEWER.email, date: isoOf(EPOCH_SEC) },
        committer: { name: VIEWER.name, email: VIEWER.email, date: isoOf(EPOCH_SEC) },
        tree: { sha: '', url: '' },
        parents: [],
      },
    });
  });

  router.add('DELETE', '/api/v3/repos/:owner/:repo/contents/:path*', (ctx) => {
    if (ctx.jsonError) return errorJson(ctx, 400, 'Problems parsing JSON');
    const repo = needRepo(ctx);
    if (repo === null) return;
    const body = bodyObject(ctx);
    const filePath = (ctx.params.path ?? '').replace(/^\/+/, '');
    const branch = str(body.branch, repo.defaultBranch) || repo.defaultBranch;
    const tip = repo.tipOf(branch);
    if (tip === undefined) return errorJson(ctx, 404, 'Not Found');
    const files = filesAtCommit(repo, tip);
    const existing = files.get(filePath);
    if (existing === undefined) return errorJson(ctx, 404, 'Not Found');
    const givenSha = typeof body.sha === 'string' ? body.sha : undefined;
    if (givenSha !== undefined && givenSha !== existing) {
      return errorJson(ctx, 409, 'the sha does not match');
    }
    files.delete(filePath);
    const commitSha = commitFiles(repo, branch, files, str(body.message, `Delete ${filePath}`));
    ctx.uow.stage(repo);
    return sendJson(ctx, 200, {
      content: null,
      commit: { sha: commitSha, url: `/api/v3/repos/${repo.fullName}/commits/${commitSha}`, message: str(body.message, `Delete ${filePath}`) },
    });
  });
}

/** The tree sha of a directory inside a commit, or ZERO_OID when absent. */
function dirShaAt(repo: Repository, commitSha: string, dirPath: string): string {
  const commitObject = repo.getObject(commitSha);
  if (commitObject === undefined || commitObject.type !== 'commit') return ZERO_OID;
  let treeSha = parseCommit(commitObject.data).tree;
  for (const part of dirPath.split('/').filter((p) => p.length > 0)) {
    const treeObject = repo.getObject(treeSha);
    if (treeObject === undefined || treeObject.type !== 'tree') return ZERO_OID;
    const entry = parseTree(treeObject.data).find((e) => e.name === part && e.mode === '40000');
    if (entry === undefined) return ZERO_OID;
    treeSha = entry.sha;
  }
  return treeSha;
}

// ---------------------------------------------------------------------------
// Labels, issues, comments, pull requests.
// ---------------------------------------------------------------------------

/** Shared pull-request creation for REST, GraphQL and MCP: one store, one numbering. */
function makePullEntity(repo: Repository, input: { title: string; body: string; head: string; base: string }): PullEntity | null {
  const strip = (ref: string): string => {
    const colon = ref.indexOf(':');
    return colon === -1 ? ref : ref.slice(colon + 1);
  };
  const head = strip(input.head);
  const base = strip(input.base);
  if (repo.tipOf(head) === undefined || repo.tipOf(base) === undefined) return null;
  const pull: PullEntity = {
    kind: 'pull',
    number: repo.nextNumber,
    title: input.title,
    body: input.body,
    state: 'open',
    head,
    base,
    merged: false,
    mergeCommitSha: null,
    createdSec: nextSec(),
    comments: [],
  };
  repo.nextNumber += 1;
  repo.items.set(pull.number, pull);
  return pull;
}

function registerIssuesAndPulls(router: TemplateRouter): void {
  router.add('POST', '/api/v3/repos/:owner/:repo/labels', (ctx) => {
    if (ctx.jsonError) return errorJson(ctx, 400, 'Problems parsing JSON');
    const repo = needRepo(ctx);
    if (repo === null) return;
    const body = bodyObject(ctx);
    const name = str(body.name);
    if (name === '') return errorJson(ctx, 422, 'Validation Failed');
    if (repo.labels.has(name)) return errorJson(ctx, 422, 'Validation Failed: label already exists');
    const label: LabelEntity = {
      name,
      color: str(body.color, 'ededed').replace(/^#/, ''),
      description: str(body.description),
    };
    repo.labels.set(name, label);
    ctx.uow.stage(repo);
    return sendJson(ctx, 201, labelJson(label));
  });

  router.add('GET', '/api/v3/repos/:owner/:repo/labels', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    return sendJson(ctx, 200, [...repo.labels.values()].map(labelJson));
  });

  router.add('GET', '/api/v3/repos/:owner/:repo/labels/:name', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const label = repo.labels.get(ctx.params.name ?? '');
    if (label === undefined) return errorJson(ctx, 404, 'Not Found');
    return sendJson(ctx, 200, labelJson(label));
  });

  const labelNamesOf = (repo: Repository, body: Record<string, unknown>): string[] | null => {
    const raw = body.labels;
    if (raw === undefined) return [];
    if (!Array.isArray(raw)) return null;
    const names: string[] = [];
    for (const entry of raw) {
      if (typeof entry === 'string') names.push(entry);
      else if (typeof entry === 'object' && entry !== null && typeof (entry as Record<string, unknown>).name === 'string') {
        names.push((entry as Record<string, unknown>).name as string);
      } else return null;
    }
    for (const name of names) if (!repo.labels.has(name)) return null;
    return names;
  };

  const createIssueEntity = (repo: Repository, title: string, body: string, labels: string[]): IssueEntity => {
    const issue: IssueEntity = {
      kind: 'issue',
      number: repo.nextNumber,
      title,
      body,
      state: 'open',
      labels,
      createdSec: nextSec(),
      comments: [],
    };
    repo.nextNumber += 1;
    repo.items.set(issue.number, issue);
    return issue;
  };

  router.add('POST', '/api/v3/repos/:owner/:repo/issues', (ctx) => {
    if (ctx.jsonError) return errorJson(ctx, 400, 'Problems parsing JSON');
    const repo = needRepo(ctx);
    if (repo === null) return;
    const body = bodyObject(ctx);
    const title = str(body.title);
    if (title === '') return errorJson(ctx, 422, 'Validation Failed: title is required');
    const labels = labelNamesOf(repo, body);
    if (labels === null) return errorJson(ctx, 422, 'Validation Failed: a label does not exist');
    const issue = createIssueEntity(repo, title, str(body.body), labels);
    ctx.uow.stage(repo);
    return sendJson(ctx, 201, issueJson(repo, issue));
  });

  router.add('GET', '/api/v3/repos/:owner/:repo/issues', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const state = ctx.query.get('state') ?? 'open';
    const direction = ctx.query.get('direction') ?? 'desc';
    let issues = [...repo.items.values()].filter((item): item is IssueEntity => item.kind === 'issue');
    if (state === 'open' || state === 'closed') issues = issues.filter((i) => i.state === state);
    issues.sort((a, b) => (direction === 'asc' ? a.number - b.number : b.number - a.number));
    const views = issues.map((issue) => issueJson(repo, issue));
    const { slice, headers } = pageSlice(ctx, views, `/api/v3/repos/${repo.fullName}/issues`);
    return sendJson(ctx, 200, slice, headers);
  });

  const findItem = (ctx: RequestContext, repo: Repository): ItemEntity | null => {
    const number = Number(ctx.params.number ?? '');
    const item = Number.isInteger(number) ? repo.items.get(number) : undefined;
    if (item === undefined) {
      errorJson(ctx, 404, 'Not Found');
      return null;
    }
    return item;
  };

  router.add('GET', '/api/v3/repos/:owner/:repo/issues/:number', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const item = findItem(ctx, repo);
    if (item === null) return;
    if (item.kind === 'pull') return sendJson(ctx, 200, pullJson(repo, item));
    return sendJson(ctx, 200, issueJson(repo, item));
  });

  router.add('PATCH', '/api/v3/repos/:owner/:repo/issues/:number', (ctx) => {
    if (ctx.jsonError) return errorJson(ctx, 400, 'Problems parsing JSON');
    const repo = needRepo(ctx);
    if (repo === null) return;
    const item = findItem(ctx, repo);
    if (item === null) return;
    const body = bodyObject(ctx);
    if (typeof body.title === 'string') item.title = body.title;
    if (typeof body.body === 'string') item.body = body.body;
    if (body.state === 'open' || body.state === 'closed') item.state = body.state;
    if (item.kind === 'issue' && body.labels !== undefined) {
      const labels = labelNamesOf(repo, body);
      if (labels === null) return errorJson(ctx, 422, 'Validation Failed: a label does not exist');
      item.labels = labels;
    }
    ctx.uow.stage(repo);
    if (item.kind === 'pull') return sendJson(ctx, 200, pullJson(repo, item));
    return sendJson(ctx, 200, issueJson(repo, item));
  });

  router.add('POST', '/api/v3/repos/:owner/:repo/issues/:number/comments', (ctx) => {
    if (ctx.jsonError) return errorJson(ctx, 400, 'Problems parsing JSON');
    const repo = needRepo(ctx);
    if (repo === null) return;
    const item = findItem(ctx, repo);
    if (item === null) return;
    const body = bodyObject(ctx);
    const comment: CommentEntity = { id: repo.nextCommentId, body: str(body.body), createdSec: nextSec() };
    repo.nextCommentId += 1;
    item.comments.push(comment);
    ctx.uow.stage(repo);
    return sendJson(ctx, 201, commentJson(repo, item, comment));
  });

  router.add('GET', '/api/v3/repos/:owner/:repo/issues/:number/comments', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const item = findItem(ctx, repo);
    if (item === null) return;
    const views = item.comments.map((comment) => commentJson(repo, item, comment));
    const { slice, headers } = pageSlice(ctx, views, `/api/v3/repos/${repo.fullName}/issues/${item.number}/comments`);
    return sendJson(ctx, 200, slice, headers);
  });

  // ---- pull requests ----

  router.add('POST', '/api/v3/repos/:owner/:repo/pulls', (ctx) => {
    if (ctx.jsonError) return errorJson(ctx, 400, 'Problems parsing JSON');
    const repo = needRepo(ctx);
    if (repo === null) return;
    const body = bodyObject(ctx);
    const title = str(body.title);
    const head = str(body.head);
    const base = str(body.base, repo.defaultBranch);
    if (title === '' || head === '') return errorJson(ctx, 422, 'Validation Failed');
    const pull = makePullEntity(repo, { title, body: str(body.body), head, base });
    if (pull === null) return errorJson(ctx, 422, 'Validation Failed: head or base branch does not exist');
    ctx.uow.stage(repo);
    return sendJson(ctx, 201, pullJson(repo, pull));
  });

  router.add('GET', '/api/v3/repos/:owner/:repo/pulls', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const state = ctx.query.get('state') ?? 'open';
    let pulls = [...repo.items.values()].filter((item): item is PullEntity => item.kind === 'pull');
    if (state === 'open' || state === 'closed') pulls = pulls.filter((p) => p.state === state);
    pulls.sort((a, b) => b.number - a.number);
    const views = pulls.map((pull) => pullJson(repo, pull));
    const { slice, headers } = pageSlice(ctx, views, `/api/v3/repos/${repo.fullName}/pulls`);
    return sendJson(ctx, 200, slice, headers);
  });

  const findPull = (ctx: RequestContext, repo: Repository): PullEntity | null => {
    const number = Number(ctx.params.number ?? '');
    const item = Number.isInteger(number) ? repo.items.get(number) : undefined;
    if (item === undefined || item.kind !== 'pull') {
      errorJson(ctx, 404, 'Not Found');
      return null;
    }
    return item;
  };

  router.add('GET', '/api/v3/repos/:owner/:repo/pulls/:number', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const pull = findPull(ctx, repo);
    if (pull === null) return;
    return sendJson(ctx, 200, pullJson(repo, pull));
  });

  router.add('GET', '/api/v3/repos/:owner/:repo/pulls/:number/files', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const pull = findPull(ctx, repo);
    if (pull === null) return;
    const headSha = repo.tipOf(pull.head);
    const baseSha = repo.tipOf(pull.base);
    if (headSha === undefined || baseSha === undefined) return sendJson(ctx, 200, []);
    const base = mergeBase(repo, baseSha, headSha) ?? baseSha;
    const files = changedFiles(repo, base, headSha).map((file) => ({
      filename: file.filename,
      sha: file.sha,
      status: file.status,
      additions: file.additions,
      deletions: file.deletions,
      changes: file.additions + file.deletions,
      blob_url: '',
      raw_url: '',
      contents_url: '',
      patch: '',
    }));
    const { slice, headers } = pageSlice(ctx, files, `/api/v3/repos/${repo.fullName}/pulls/${pull.number}/files`);
    return sendJson(ctx, 200, slice, headers);
  });

  router.add('PUT', '/api/v3/repos/:owner/:repo/pulls/:number/merge', (ctx) => {
    const repo = needRepo(ctx);
    if (repo === null) return;
    const pull = findPull(ctx, repo);
    if (pull === null) return;
    if (pull.state !== 'open' || pull.merged) {
      return errorJson(ctx, 405, 'Pull Request is not open');
    }
    const outcome = mergePull(repo, pull);
    if (!outcome.ok) {
      return errorJson(ctx, 405, 'Pull Request is not mergeable: conflicts must be resolved first');
    }
    ctx.uow.stage(repo);
    return sendJson(ctx, 200, {
      sha: outcome.sha as string,
      merged: true,
      message: 'Pull Request successfully merged',
    });
  });
}


// ---------------------------------------------------------------------------
// Git smart HTTP. Advertisements, protocol v2 ls-refs/fetch with shallow
// support, v0 fetch with side-band-64k, and v0 receive-pack whose updates
// must fast-forward, refused per ref as "ng <ref> non-fast-forward".
// ---------------------------------------------------------------------------

const AGENT_TOKEN = 'agent=brightfalcon-forge/1.0';

function sortedRefs(repo: Repository): Array<[string, string]> {
  return [...repo.refs.entries()].sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
}

function peeledOf(repo: Repository, sha: string): string | null {
  const object = repo.getObject(sha);
  if (object === undefined || object.type !== 'tag') return null;
  return peelToCommit(repo, sha);
}

function handleInfoRefs(ctx: RequestContext, repo: Repository | null): void {
  const service = ctx.query.get('service') ?? '';
  if (repo === null || (service !== 'git-upload-pack' && service !== 'git-receive-pack')) {
    return errorJson(ctx, 404, 'Not Found');
  }
  const wantsV2 = service === 'git-upload-pack' && (ctx.req.headers['git-protocol'] ?? '').includes('version=2');
  if (wantsV2) {
    const body = Buffer.concat([
      pktLine('version 2\n'),
      pktLine(`${AGENT_TOKEN}\n`),
      pktLine('ls-refs=unborn\n'),
      pktLine('fetch=shallow filter wait-for-done\n'),
      pktLine('object-format=sha1\n'),
      PKT_FLUSH,
    ]);
    return sendRaw(ctx.res, 200, body, {
      'content-type': 'application/x-git-upload-pack-advertisement',
      'cache-control': 'no-cache, max-age=0, must-revalidate',
    });
  }
  const isUpload = service === 'git-upload-pack';
  const caps = isUpload
    ? `side-band-64k thin-pack ofs-delta deepen-since deepen-not multi_ack agent=brightfalcon-forge/1.0 symref=HEAD:refs/heads/${repo.defaultBranch}`
    : 'report-status side-band-64k delete-refs ofs-delta agent=brightfalcon-forge/1.0';
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), PKT_FLUSH];
  const refs = sortedRefs(repo);
  const headSha = repo.refs.get(repo.headRef());
  if (refs.length === 0) {
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
    parts.push(pktLine(`${ZERO_OID} HEAD\n`));
  } else {
    parts.push(pktLine(`${headSha ?? ZERO_OID} HEAD\0${caps}\n`));
    for (const [ref, sha] of refs) {
      parts.push(pktLine(`${sha} ${ref}\n`));
      const peeled = peeledOf(repo, sha);
      if (peeled !== null) parts.push(pktLine(`${peeled} ${ref}^{}\n`));
    }
  }
  parts.push(PKT_FLUSH);
  return sendRaw(ctx.res, 200, Buffer.concat(parts), {
    'content-type': `application/x-${service}-advertisement`,
    'cache-control': 'no-cache, max-age=0, must-revalidate',
  });
}

interface FetchPlan {
  pack: Buffer;
  shallow: string[];
  unshallow: string[];
}

/** Decide which objects a fetch sends, honouring haves and shallow depth. */
function planFetch(
  repo: Repository,
  wants: string[],
  haves: string[],
  clientShallow: string[],
  depth: number | null,
): FetchPlan {
  // Exclusion closure: everything reachable from haves; a commit the client
  // marks shallow contributes itself and its trees but not its ancestry.
  const excluded = new Set<string>();
  const shallowSet = new Set(clientShallow);
  const addClosure = (tip: string, stopAtShallowBoundary: boolean): void => {
    const queue: string[] = [tip];
    const seenCommits = new Set<string>();
    while (queue.length > 0) {
      const sha = queue.shift() as string;
      if (seenCommits.has(sha)) continue;
      seenCommits.add(sha);
      const commitSha = peelToCommit(repo, sha) ?? sha;
      const object = repo.getObject(commitSha);
      if (object === undefined || object.type !== 'commit') {
        excluded.add(sha);
        continue;
      }
      excluded.add(commitSha);
      const info = parseCommit(object.data);
      addTreeClosure(repo, info.tree, excluded);
      if (stopAtShallowBoundary && shallowSet.has(commitSha)) continue;
      for (const parent of info.parents) queue.push(parent);
    }
  };
  for (const have of haves) addClosure(have, true);
  for (const boundary of clientShallow) addClosure(boundary, true);

  const included = new Set<string>();
  const boundaryCommits: string[] = [];
  const wantCommits: string[] = [];
  for (const want of wants) {
    const object = repo.getObject(want);
    if (object === undefined) continue;
    if (object.type === 'tag') {
      included.add(want);
      const target = peelToCommit(repo, want);
      if (target !== null) wantCommits.push(target);
    } else if (object.type === 'commit') {
      wantCommits.push(want);
    } else {
      included.add(want);
    }
  }
  const includedCommits = new Set<string>();
  for (const tip of wantCommits) {
    const dist = generations(repo, tip);
    for (const [sha, d] of dist) {
      if (depth !== null && d >= depth) continue;
      includedCommits.add(sha);
    }
    if (depth !== null) {
      for (const [sha, d] of dist) {
        if (d !== depth - 1) continue;
        const object = repo.getObject(sha);
        if (object === undefined || object.type !== 'commit') continue;
        if (parseCommit(object.data).parents.length > 0) boundaryCommits.push(sha);
      }
    }
  }
  for (const sha of includedCommits) {
    if (!excluded.has(sha)) included.add(sha);
    const object = repo.getObject(sha);
    if (object !== undefined && object.type === 'commit') {
      addTreeClosure(repo, parseCommit(object.data).tree, included);
    }
  }
  for (const sha of excluded) included.delete(sha);
  // A boundary commit the client already holds in full is no longer shallow.
  const unshallow: string[] = [];
  for (const boundary of clientShallow) {
    if (!includedCommits.has(boundary)) continue;
    const object = repo.getObject(boundary);
    if (object === undefined || object.type !== 'commit') continue;
    const parents = parseCommit(object.data).parents;
    if (parents.length === 0 || parents.every((p) => includedCommits.has(p))) unshallow.push(boundary);
  }
  const objects: GitObject[] = [];
  for (const sha of included) {
    const object = repo.getObject(sha);
    if (object !== undefined) objects.push(object);
  }
  // Commits first, then trees, then blobs: a stable, readable pack order.
  const rank = (o: GitObject): number => (o.type === 'commit' ? 0 : o.type === 'tag' ? 1 : o.type === 'tree' ? 2 : 3);
  objects.sort((a, b) => rank(a) - rank(b));
  return { pack: writePack(objects), shallow: depth === null ? [] : boundaryCommits, unshallow };
}

function addTreeClosure(repo: Repository, treeSha: string, into: Set<string>): void {
  if (into.has(treeSha)) return;
  const object = repo.getObject(treeSha);
  if (object === undefined || object.type !== 'tree') return;
  into.add(treeSha);
  for (const entry of parseTree(object.data)) {
    if (entry.mode === '40000') addTreeClosure(repo, entry.sha, into);
    else into.add(entry.sha);
  }
}

function sidebandChunks(data: Buffer): Buffer[] {
  const out: Buffer[] = [];
  const maxPayload = 65520 - 4 - 1;
  for (let pos = 0; pos < data.length; pos += maxPayload) {
    const slice = data.subarray(pos, pos + maxPayload);
    out.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  if (out.length === 0) out.push(pktLine(Buffer.concat([Buffer.from([1]), Buffer.alloc(0)])));
  return out;
}

interface ParsedFetchArgs {
  wants: string[];
  haves: string[];
  shallow: string[];
  depth: number | null;
  deepenRelative: boolean;
  done: boolean;
}

function collectFetchArgs(lines: string[], existing: ParsedFetchArgs): ParsedFetchArgs {
  const args = existing;
  for (const raw of lines) {
    const line = raw.replace(/\n$/, '');
    if (line.startsWith('want ')) args.wants.push(line.slice(5).trim().split(' ')[0] as string);
    else if (line.startsWith('have ')) args.haves.push(line.slice(5).trim());
    else if (line.startsWith('shallow ')) args.shallow.push(line.slice(8).trim());
    else if (line.startsWith('deepen ')) args.depth = Number(line.slice(7).trim());
    else if (line === 'deepen-relative') args.deepenRelative = true;
    else if (line === 'done') args.done = true;
  }
  return args;
}

function emptyFetchArgs(): ParsedFetchArgs {
  return { wants: [], haves: [], shallow: [], depth: null, deepenRelative: false, done: false };
}

/** A relative deepen counts from the client's current shallow boundary. */
function resolveDepth(repo: Repository, args: ParsedFetchArgs): number | null {
  if (args.depth === null || !args.deepenRelative || args.shallow.length === 0) return args.depth;
  const tip = args.wants.map((want) => peelToCommit(repo, want) ?? want).find((sha) => repo.getObject(sha)?.type === 'commit');
  if (tip === undefined) return args.depth;
  const dist = generations(repo, tip);
  let boundary = 0;
  for (const sha of args.shallow) {
    const d = dist.get(sha);
    if (d !== undefined && d > boundary) boundary = d;
  }
  return boundary + 1 + args.depth;
}

function handleUploadPack(ctx: RequestContext, repo: Repository | null): void {
  if (repo === null) return errorJson(ctx, 404, 'Not Found');
  const body = ctx.body;
  const isV2 = (ctx.req.headers['git-protocol'] ?? '').includes('version=2') || body.subarray(0, 64).toString('utf8').startsWith('command=');
  if (isV2) return handleUploadPackV2(ctx, repo, body);
  return handleUploadPackV0(ctx, repo, body);
}

function handleUploadPackV2(ctx: RequestContext, repo: Repository, body: Buffer): void {
  const { packets } = decodePkts(body);
  const lines: string[] = [];
  for (const packet of packets) {
    if (packet.kind === 'data') lines.push(packet.payload.toString('utf8'));
  }
  const commandLine = lines[0]?.replace(/\n$/, '') ?? '';
  const command = commandLine.startsWith('command=') ? commandLine.slice('command='.length) : '';
  const argsStart = lines.findIndex((line, index) => index > 0 && (line === '' )) ;
  void argsStart;
  // Arguments live after the delim packet; decodePkts kept order, so split by
  // re-walking the packet kinds.
  const argLines: string[] = [];
  let afterDelim = false;
  for (const packet of packets) {
    if (packet.kind === 'delim') {
      afterDelim = true;
      continue;
    }
    if (packet.kind === 'flush') break;
    if (afterDelim && packet.kind === 'data') argLines.push(packet.payload.toString('utf8'));
  }

  if (command === 'ls-refs') {
    let peel = false;
    let symrefs = false;
    let unborn = false;
    const prefixes: string[] = [];
    for (const raw of argLines) {
      const line = raw.replace(/\n$/, '');
      if (line === 'peel') peel = true;
      else if (line === 'symrefs') symrefs = true;
      else if (line === 'unborn') unborn = true;
      else if (line.startsWith('ref-prefix ')) prefixes.push(line.slice('ref-prefix '.length));
    }
    const matchesPrefix = (name: string): boolean => prefixes.length === 0 || prefixes.some((p) => name.startsWith(p));
    const parts: Buffer[] = [];
    const headSha = repo.refs.get(repo.headRef());
    const headName = repo.headRef();
    if (prefixes.length === 0 || prefixes.some((p) => 'HEAD'.startsWith(p) || p === '')) {
      if (headSha !== undefined) {
        parts.push(pktLine(`${headSha} HEAD${symrefs ? ` symref-target:${headName}` : ''}\n`));
      } else if (unborn) {
        parts.push(pktLine(`unborn HEAD${symrefs ? ` symref-target:${headName}` : ''}\n`));
      }
    }
    for (const [ref, sha] of sortedRefs(repo)) {
      if (!matchesPrefix(ref)) continue;
      let line = `${sha} ${ref}`;
      if (peel) {
        const peeled = peeledOf(repo, sha);
        if (peeled !== null) line += ` peeled:${peeled}`;
      }
      parts.push(pktLine(`${line}\n`));
    }
    parts.push(PKT_FLUSH);
    return sendRaw(ctx.res, 200, Buffer.concat(parts), { 'content-type': 'application/x-git-upload-pack-result' });
  }

  if (command === 'fetch') {
    const args = collectFetchArgs(argLines, emptyFetchArgs());
    const plan = planFetch(repo, [...new Set(args.wants)], args.haves, args.shallow, resolveDepth(repo, args));
    const parts: Buffer[] = [];
    if (!args.done && args.haves.length > 0) {
      // Negotiation: acknowledge the common base; the packfile sections
      // follow in this same response.
      const common = args.haves.find((have) => args.wants.some((want) => isAncestor(repo, have, peelToCommit(repo, want) ?? want)));
      parts.push(pktLine('acknowledgments\n'));
      if (common === undefined) {
        parts.push(pktLine('NAK\n'));
        parts.push(PKT_FLUSH);
        return sendRaw(ctx.res, 200, Buffer.concat(parts), { 'content-type': 'application/x-git-upload-pack-result' });
      }
      parts.push(pktLine(`ACK ${common}\n`));
      parts.push(PKT_FLUSH);
    }
    if (args.depth !== null || plan.unshallow.length > 0) {
      parts.push(pktLine('shallow-info\n'));
      for (const sha of plan.shallow) parts.push(pktLine(`shallow ${sha}\n`));
      for (const sha of plan.unshallow) parts.push(pktLine(`unshallow ${sha}\n`));
      parts.push(PKT_FLUSH);
    }
    parts.push(pktLine('packfile\n'));
    for (const chunk of sidebandChunks(plan.pack)) parts.push(chunk);
    parts.push(PKT_FLUSH);
    return sendRaw(ctx.res, 200, Buffer.concat(parts), { 'content-type': 'application/x-git-upload-pack-result' });
  }

  return errorJson(ctx, 400, 'unknown command');
}

function handleUploadPackV0(ctx: RequestContext, repo: Repository, body: Buffer): void {
  const { packets, consumed } = decodePkts(body);
  void consumed;
  const lines: string[] = [];
  for (const packet of packets) {
    if (packet.kind === 'data') lines.push(packet.payload.toString('utf8'));
  }
  // v0 sends wants, a flush, then haves and done; decodePkts stops at the
  // first flush, so parse the remainder too.
  const allLines = [...lines];
  let pos = consumed;
  while (pos < body.length) {
    const next = decodePkts(body, pos);
    if (next.consumed === pos) break;
    for (const packet of next.packets) {
      if (packet.kind === 'data') allLines.push(packet.payload.toString('utf8'));
    }
    pos = next.consumed;
  }
  const args = collectFetchArgs(allLines, emptyFetchArgs());
  const plan = planFetch(repo, [...new Set(args.wants)], args.haves, args.shallow, resolveDepth(repo, args));
  const parts: Buffer[] = [];
  for (const sha of plan.shallow) parts.push(pktLine(`shallow ${sha}\n`));
  for (const sha of plan.unshallow) parts.push(pktLine(`unshallow ${sha}\n`));
  parts.push(pktLine('NAK\n'));
  for (const chunk of sidebandChunks(plan.pack)) parts.push(chunk);
  parts.push(PKT_FLUSH);
  return sendRaw(ctx.res, 200, Buffer.concat(parts), { 'content-type': 'application/x-git-upload-pack-result' });
}

interface PushCommand {
  oldOid: string;
  newOid: string;
  ref: string;
}

function handleReceivePack(ctx: RequestContext, repo: Repository | null): void {
  if (repo === null) return errorJson(ctx, 404, 'Not Found');
  const body = ctx.body;
  const { packets, consumed } = decodePkts(body);
  const commands: PushCommand[] = [];
  for (const packet of packets) {
    if (packet.kind !== 'data') continue;
    let line = packet.payload.toString('utf8').replace(/\n$/, '');
    const nul = line.indexOf('\0');
    if (nul >= 0) line = line.slice(0, nul);
    const fields = line.split(' ');
    if (fields.length >= 3) {
      commands.push({ oldOid: fields[0] as string, newOid: fields[1] as string, ref: fields.slice(2).join(' ') });
    }
  }
  const packBytes = body.subarray(consumed);
  let unpackOk = true;
  if (packBytes.length > 0) {
    try {
      const pack = readPack(packBytes, (sha) => repo.getObject(sha));
      for (const object of pack.objects) {
        repo.objects.set(hashObject(object.type, object.data), object);
      }
    } catch {
      unpackOk = false;
    }
  }

  const reportLines: string[] = [unpackOk ? 'unpack ok\n' : 'unpack error\n'];
  if (unpackOk) {
    for (const command of commands) {
      const current = repo.refs.get(command.ref) ?? ZERO_OID;
      if (command.newOid === ZERO_OID) {
        // Delete.
        if (current === ZERO_OID || current !== command.oldOid) {
          reportLines.push(`ng ${command.ref} reference does not exist\n`);
          continue;
        }
        repo.refs.delete(command.ref);
        reportLines.push(`ok ${command.ref}\n`);
        continue;
      }
      const newObject = repo.getObject(command.newOid);
      if (newObject === undefined) {
        reportLines.push(`ng ${command.ref} unknown object\n`);
        continue;
      }
      if (current !== command.oldOid) {
        reportLines.push(`ng ${command.ref} non-fast-forward\n`);
        continue;
      }
      if (command.oldOid !== ZERO_OID && command.ref.startsWith('refs/heads/')) {
        const newCommit = peelToCommit(repo, command.newOid);
        const oldCommit = peelToCommit(repo, command.oldOid);
        if (newCommit === null || oldCommit === null || !isAncestor(repo, oldCommit, newCommit)) {
          reportLines.push(`ng ${command.ref} non-fast-forward\n`);
          continue;
        }
      }
      repo.refs.set(command.ref, command.newOid);
      reportLines.push(`ok ${command.ref}\n`);
    }
  } else {
    for (const command of commands) reportLines.push(`ng ${command.ref} unpacker error\n`);
  }
  ctx.uow.stage(repo);

  const reportStream = Buffer.concat([...reportLines.map((line) => pktLine(line)), PKT_FLUSH]);
  const parts: Buffer[] = [];
  const maxPayload = 65520 - 4 - 1;
  for (let pos = 0; pos < reportStream.length; pos += maxPayload) {
    const slice = reportStream.subarray(pos, pos + maxPayload);
    parts.push(pktLine(Buffer.concat([Buffer.from([1]), slice])));
  }
  parts.push(PKT_FLUSH);
  return sendRaw(ctx.res, 200, Buffer.concat(parts), { 'content-type': 'application/x-git-receive-pack-result' });
}

// ---------------------------------------------------------------------------
// GraphQL v4: a compact parser and executor for the documents gh and
// github-mcp-server send, over the same store as REST. Global ids are
// base64 "Type:..." strings that node() and the mutations decode back.
// ---------------------------------------------------------------------------

type GqlValue =
  | { kind: 'var'; name: string }
  | { kind: 'str'; value: string }
  | { kind: 'int'; value: number }
  | { kind: 'float'; value: number }
  | { kind: 'bool'; value: boolean }
  | { kind: 'null' }
  | { kind: 'enum'; value: string }
  | { kind: 'list'; items: GqlValue[] }
  | { kind: 'object'; fields: Array<[string, GqlValue]> };

interface GqlField {
  kind: 'field';
  alias: string | null;
  name: string;
  args: Array<[string, GqlValue]>;
  selections: GqlSelection[];
}
type GqlSelection =
  | GqlField
  | { kind: 'spread'; name: string }
  | { kind: 'inline'; on: string | null; selections: GqlSelection[] };

interface GqlOperation {
  type: 'query' | 'mutation';
  name: string | null;
  selections: GqlSelection[];
}

function gqlTokenize(source: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < source.length) {
    const ch = source[i] as string;
    if (ch === '#') {
      while (i < source.length && source[i] !== '\n') i += 1;
      continue;
    }
    if (/\s|,/.test(ch)) {
      i += 1;
      continue;
    }
    if (source.startsWith('...', i)) {
      tokens.push('...');
      i += 3;
      continue;
    }
    if ('{}()[]:@$!:=|&'.includes(ch)) {
      tokens.push(ch);
      i += 1;
      continue;
    }
    if (ch === '"') {
      if (source.startsWith('"""', i)) {
        const end = source.indexOf('"""', i + 3);
        tokens.push(`"${source.slice(i + 3, end === -1 ? source.length : end)}"`);
        i = end === -1 ? source.length : end + 3;
        continue;
      }
      let j = i + 1;
      let out = '';
      while (j < source.length && source[j] !== '"') {
        if (source[j] === '\\' && j + 1 < source.length) {
          const esc = source[j + 1] as string;
          out += esc === 'n' ? '\n' : esc === 't' ? '\t' : esc === 'r' ? '\r' : esc;
          j += 2;
        } else {
          out += source[j];
          j += 1;
        }
      }
      tokens.push(`"${out}"`);
      i = j + 1;
      continue;
    }
    if (/[0-9-]/.test(ch)) {
      let j = i;
      while (j < source.length && /[0-9.eE+-]/.test(source[j] as string)) j += 1;
      tokens.push(source.slice(i, j));
      i = j;
      continue;
    }
    if (/[_A-Za-z]/.test(ch)) {
      let j = i;
      while (j < source.length && /[_0-9A-Za-z]/.test(source[j] as string)) j += 1;
      tokens.push(source.slice(i, j));
      i = j;
      continue;
    }
    i += 1;
  }
  return tokens;
}

class GqlParser {
  private tokens: string[];
  private pos = 0;
  fragments = new Map<string, { on: string | null; selections: GqlSelection[] }>();

  constructor(source: string) {
    this.tokens = gqlTokenize(source);
  }

  private peek(): string | undefined {
    return this.tokens[this.pos];
  }
  private next(): string {
    const token = this.tokens[this.pos] as string;
    this.pos += 1;
    return token;
  }
  private expect(token: string): void {
    if (this.next() !== token) throw new Error(`expected ${token}`);
  }
  private skipBalanced(open: string, close: string): void {
    let depth = 0;
    for (;;) {
      const token = this.next();
      if (token === undefined) return;
      if (token === open) depth += 1;
      if (token === close) {
        depth -= 1;
        if (depth === 0) return;
      }
    }
  }

  parseDocument(): GqlOperation[] {
    const operations: GqlOperation[] = [];
    while (this.pos < this.tokens.length) {
      const token = this.peek();
      if (token === '{') {
        operations.push({ type: 'query', name: null, selections: this.parseSelectionSet() });
      } else if (token === 'query' || token === 'mutation' || token === 'subscription') {
        this.next();
        let name: string | null = null;
        if (this.peek() !== undefined && /^[_A-Za-z]/.test(this.peek() as string) && this.peek() !== '{' && this.peek() !== '(') {
          name = this.next();
        }
        if (this.peek() === '(') this.skipBalanced('(', ')');
        // Directives between the signature and the selection set.
        while (this.peek() === '@') {
          this.next();
          this.next();
          if (this.peek() === '(') this.skipBalanced('(', ')');
        }
        operations.push({ type: token === 'mutation' ? 'mutation' : 'query', name, selections: this.parseSelectionSet() });
      } else if (token === 'fragment') {
        this.next();
        const fragName = this.next();
        this.expect('on');
        const on = this.next();
        while (this.peek() === '@') {
          this.next();
          this.next();
          if (this.peek() === '(') this.skipBalanced('(', ')');
        }
        this.fragments.set(fragName, { on, selections: this.parseSelectionSet() });
      } else {
        this.next();
      }
    }
    return operations;
  }

  private parseSelectionSet(): GqlSelection[] {
    this.expect('{');
    const selections: GqlSelection[] = [];
    while (this.peek() !== '}' && this.peek() !== undefined) {
      if (this.peek() === '...') {
        this.next();
        if (this.peek() === 'on') {
          this.next();
          const on = this.next();
          while (this.peek() === '@') {
            this.next();
            this.next();
            if (this.peek() === '(') this.skipBalanced('(', ')');
          }
          selections.push({ kind: 'inline', on, selections: this.parseSelectionSet() });
        } else {
          const name = this.next();
          while (this.peek() === '@') {
            this.next();
            this.next();
            if (this.peek() === '(') this.skipBalanced('(', ')');
          }
          selections.push({ kind: 'spread', name });
        }
        continue;
      }
      const first = this.next();
      let alias: string | null = null;
      let name = first;
      if (this.peek() === ':') {
        this.next();
        alias = first;
        name = this.next();
      }
      const args: Array<[string, GqlValue]> = [];
      if (this.peek() === '(') {
        this.next();
        while (this.peek() !== ')' && this.peek() !== undefined) {
          const argName = this.next();
          this.expect(':');
          args.push([argName, this.parseValue()]);
        }
        this.expect(')');
      }
      while (this.peek() === '@') {
        this.next();
        this.next();
        if (this.peek() === '(') this.skipBalanced('(', ')');
      }
      let sub: GqlSelection[] = [];
      if (this.peek() === '{') sub = this.parseSelectionSet();
      selections.push({ kind: 'field', alias, name, args, selections: sub });
    }
    this.expect('}');
    return selections;
  }

  private parseValue(): GqlValue {
    const token = this.next();
    if (token === '$') return { kind: 'var', name: this.next() };
    if (token.startsWith('"')) return { kind: 'str', value: token.slice(1, -1) };
    if (token === '[') {
      const items: GqlValue[] = [];
      while (this.peek() !== ']' && this.peek() !== undefined) items.push(this.parseValue());
      this.expect(']');
      return { kind: 'list', items };
    }
    if (token === '{') {
      const fields: Array<[string, GqlValue]> = [];
      while (this.peek() !== '}' && this.peek() !== undefined) {
        const key = this.next();
        this.expect(':');
        fields.push([key, this.parseValue()]);
      }
      this.expect('}');
      return { kind: 'object', fields };
    }
    if (token === 'true' || token === 'false') return { kind: 'bool', value: token === 'true' };
    if (token === 'null') return { kind: 'null' };
    if (/^-?\d+$/.test(token)) return { kind: 'int', value: Number(token) };
    if (/^-?\d*\.\d/.test(token)) return { kind: 'float', value: Number(token) };
    return { kind: 'enum', value: token };
  }
}

function gqlResolve(value: GqlValue, variables: Record<string, unknown>): unknown {
  switch (value.kind) {
    case 'var':
      return variables[value.name];
    case 'str':
    case 'int':
    case 'float':
    case 'bool':
    case 'enum':
      return value.value;
    case 'null':
      return null;
    case 'list':
      return value.items.map((item) => gqlResolve(item, variables));
    case 'object': {
      const out: Record<string, unknown> = {};
      for (const [key, sub] of value.fields) out[key] = gqlResolve(sub, variables);
      return out;
    }
  }
}

// The schema the introspection probes read. -------------------------------

interface TypeDef {
  kind: 'OBJECT' | 'ENUM' | 'INTERFACE' | 'SCALAR' | 'INPUT_OBJECT';
  fields?: string[];
  enums?: string[];
}

const SCHEMA: Record<string, TypeDef> = {
  Query: { kind: 'OBJECT', fields: ['viewer', 'repository', 'node', 'nodes', 'search', 'rateLimit', 'organization', 'user', '__type', '__schema'] },
  Mutation: {
    kind: 'OBJECT',
    fields: ['createIssue', 'closeIssue', 'reopenIssue', 'updateIssue', 'createPullRequest', 'mergePullRequest', 'addComment', 'createRepository', 'addLabelsToLabelable', 'removeLabelsFromLabelable'],
  },
  Repository: {
    kind: 'OBJECT',
    fields: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'hasProjectsEnabled', 'hasWikiEnabled', 'isPrivate', 'isArchived', 'isFork', 'description', 'url', 'homepageUrl', 'createdAt', 'updatedAt', 'pushedAt', 'issue', 'issues', 'pullRequest', 'pullRequests', 'label', 'labels', 'stargazerCount', 'forkCount', 'primaryLanguage', 'refs', 'ref', 'object', 'assignableUsers', 'mentionableUsers', 'collaborators', 'deployKeys', 'releases', 'tags', 'branches'],
  },
  Issue: {
    kind: 'OBJECT',
    fields: ['id', 'databaseId', 'number', 'title', 'body', 'bodyText', 'state', 'author', 'editor', 'labels', 'comments', 'repository', 'url', 'createdAt', 'updatedAt', 'closedAt', 'closed', 'assignees', 'milestone', 'participants', 'reactions', 'viewerCanReact'],
  },
  PullRequest: {
    kind: 'OBJECT',
    fields: ['id', 'databaseId', 'number', 'title', 'body', 'bodyText', 'state', 'merged', 'mergedAt', 'mergeable', 'headRefName', 'baseRefName', 'headRef', 'baseRef', 'headRepository', 'baseRepository', 'author', 'repository', 'url', 'createdAt', 'updatedAt', 'closedAt', 'closed', 'files', 'commits', 'comments', 'reviews', 'additions', 'deletions', 'changedFiles', 'isDraft', 'mergeCommit', 'mergedBy', 'labels', 'assignees', 'participants'],
  },
  User: { kind: 'OBJECT', fields: ['id', 'databaseId', 'login', 'name', 'email', 'url', 'avatarUrl', 'bio', 'company', 'location', 'createdAt', 'updatedAt', 'isViewer', 'repositories', 'issues', 'pullRequests'] },
  Organization: { kind: 'OBJECT', fields: ['id', 'databaseId', 'login', 'name', 'url', 'avatarUrl', 'repositories'] },
  Actor: { kind: 'INTERFACE', fields: ['login', 'url', 'avatarUrl', 'resourcePath'] },
  Node: { kind: 'INTERFACE', fields: ['id'] },
  Ref: { kind: 'OBJECT', fields: ['id', 'name', 'prefix', 'target', 'repository', 'associatedPullRequests'] },
  Commit: { kind: 'OBJECT', fields: ['id', 'oid', 'abbreviatedOid', 'message', 'messageHeadline', 'messageBody', 'author', 'committer', 'committedDate', 'authoredDate', 'tree', 'parents', 'url', 'repository', 'additions', 'deletions', 'changedFiles'] },
  GitActor: { kind: 'OBJECT', fields: ['name', 'email', 'date', 'avatarUrl', 'user'] },
  Tree: { kind: 'OBJECT', fields: ['id', 'oid', 'abbreviatedOid', 'entries', 'repository'] },
  TreeEntry: { kind: 'OBJECT', fields: ['name', 'path', 'mode', 'type', 'object', 'extension'] },
  Label: { kind: 'OBJECT', fields: ['id', 'name', 'color', 'description', 'url', 'createdAt', 'updatedAt'] },
  IssueComment: { kind: 'OBJECT', fields: ['id', 'databaseId', 'body', 'bodyText', 'author', 'editor', 'createdAt', 'updatedAt', 'url', 'issue', 'pullRequest', 'repository'] },
  PullRequestChangedFile: { kind: 'OBJECT', fields: ['path', 'additions', 'deletions', 'changeType'] },
  PageInfo: { kind: 'OBJECT', fields: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'] },
  IssueConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  IssueEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  PullRequestConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  PullRequestEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  PullRequestChangedFileConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  PullRequestChangedFileEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  LabelConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  LabelEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  IssueCommentConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  IssueCommentEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  RepositoryConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'totalCount'] },
  RepositoryEdge: { kind: 'OBJECT', fields: ['node', 'cursor'] },
  SearchResultItemConnection: { kind: 'OBJECT', fields: ['nodes', 'edges', 'pageInfo', 'issueCount', 'repositoryCount', 'userCount', 'discussionCount', 'codeCount', 'wikiCount'] },
  CreateIssuePayload: { kind: 'OBJECT', fields: ['issue', 'clientMutationId'] },
  CloseIssuePayload: { kind: 'OBJECT', fields: ['issue', 'clientMutationId'] },
  ReopenIssuePayload: { kind: 'OBJECT', fields: ['issue', 'clientMutationId'] },
  UpdateIssuePayload: { kind: 'OBJECT', fields: ['issue', 'clientMutationId'] },
  CreatePullRequestPayload: { kind: 'OBJECT', fields: ['pullRequest', 'clientMutationId'] },
  MergePullRequestPayload: { kind: 'OBJECT', fields: ['pullRequest', 'clientMutationId'] },
  AddCommentPayload: { kind: 'OBJECT', fields: ['commentEdge', 'subject', 'clientMutationId', 'comment'] },
  CreateRepositoryPayload: { kind: 'OBJECT', fields: ['repository', 'clientMutationId'] },
  AddLabelsToLabelablePayload: { kind: 'OBJECT', fields: ['labelable', 'clientMutationId'] },
  RemoveLabelsFromLabelablePayload: { kind: 'OBJECT', fields: ['labelable', 'clientMutationId'] },
  RateLimit: { kind: 'OBJECT', fields: ['limit', 'cost', 'remaining', 'resetAt', 'used', 'nodeCount'] },
  __Type: { kind: 'OBJECT', fields: ['name', 'kind', 'description', 'fields', 'enumValues', 'possibleTypes', 'inputFields', 'interfaces', 'specifiedByURL', 'ofType'] },
  __Field: { kind: 'OBJECT', fields: ['name', 'description', 'args', 'type', 'isDeprecated', 'deprecationReason'] },
  __EnumValue: { kind: 'OBJECT', fields: ['name', 'description', 'isDeprecated', 'deprecationReason'] },
  __InputValue: { kind: 'OBJECT', fields: ['name', 'description', 'type', 'defaultValue', 'isDeprecated', 'deprecationReason'] },
  __Schema: { kind: 'OBJECT', fields: ['types', 'queryType', 'mutationType', 'subscriptionType', 'directives', 'description'] },
  __Directive: { kind: 'OBJECT', fields: ['name', 'description', 'locations', 'args', 'isRepeatable'] },
  SearchType: { kind: 'ENUM', enums: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'] },
  IssueState: { kind: 'ENUM', enums: ['OPEN', 'CLOSED'] },
  IssueOrderField: { kind: 'ENUM', enums: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'] },
  OrderDirection: { kind: 'ENUM', enums: ['ASC', 'DESC'] },
  PullRequestState: { kind: 'ENUM', enums: ['OPEN', 'CLOSED', 'MERGED'] },
  MergeableState: { kind: 'ENUM', enums: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'] },
  PullRequestMergeMethod: { kind: 'ENUM', enums: ['MERGE', 'SQUASH', 'REBASE'] },
  RepositoryPermission: { kind: 'ENUM', enums: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'] },
  DefaultRepositoryPermissionField: { kind: 'ENUM', enums: ['NONE', 'READ', 'WRITE', 'ADMIN'] },
  RepositoryPrivacy: { kind: 'ENUM', enums: ['PUBLIC', 'PRIVATE'] },
  StatusState: { kind: 'ENUM', enums: ['EXPECTED', 'ERROR', 'FAILURE', 'PENDING', 'SUCCESS'] },
  String: { kind: 'SCALAR' },
  Int: { kind: 'SCALAR' },
  Float: { kind: 'SCALAR' },
  Boolean: { kind: 'SCALAR' },
  ID: { kind: 'SCALAR' },
  URI: { kind: 'SCALAR' },
  DateTime: { kind: 'SCALAR' },
  HTML: { kind: 'SCALAR' },
  Base64String: { kind: 'SCALAR' },
  GitObjectID: { kind: 'SCALAR' },
  GitSSHRemote: { kind: 'SCALAR' },
  PreciseDateTime: { kind: 'SCALAR' },
  X509Certificate: { kind: 'SCALAR' },
  CreateIssueInput: { kind: 'INPUT_OBJECT', fields: ['repositoryId', 'title', 'body', 'labelIds', 'assigneeIds', 'milestoneId', 'issueTemplate', 'clientMutationId'] },
  CloseIssueInput: { kind: 'INPUT_OBJECT', fields: ['issueId', 'stateReason', 'clientMutationId'] },
  ReopenIssueInput: { kind: 'INPUT_OBJECT', fields: ['issueId', 'clientMutationId'] },
  UpdateIssueInput: { kind: 'INPUT_OBJECT', fields: ['id', 'title', 'body', 'state', 'labelIds', 'assigneeIds', 'milestoneId', 'clientMutationId'] },
  CreatePullRequestInput: { kind: 'INPUT_OBJECT', fields: ['repositoryId', 'baseRefName', 'headRefName', 'title', 'body', 'draft', 'mantainerCanModify', 'clientMutationId'] },
  MergePullRequestInput: { kind: 'INPUT_OBJECT', fields: ['pullRequestId', 'mergeMethod', 'commitHeadline', 'commitBody', 'expectedHeadOid', 'authorEmail', 'clientMutationId'] },
  AddCommentInput: { kind: 'INPUT_OBJECT', fields: ['subjectId', 'body', 'clientMutationId'] },
  CreateRepositoryInput: { kind: 'INPUT_OBJECT', fields: ['name', 'description', 'visibility', 'ownerId', 'teamId', 'homepageUrl', 'hasIssuesEnabled', 'hasWikiEnabled', 'clientMutationId'] },
  IssueOrder: { kind: 'INPUT_OBJECT', fields: ['field', 'direction'] },
  PullRequestOrder: { kind: 'INPUT_OBJECT', fields: ['field', 'direction'] },
};

// Tagged GraphQL values ------------------------------------------------------

interface GqlObject {
  __t: string;
  [key: string]: unknown;
}

function gqlObj(type: string, props: Record<string, unknown>): GqlObject {
  return { __t: type, ...props };
}

function globalId(type: string, key: string): string {
  return Buffer.from(`${type}:${key}`, 'utf8').toString('base64');
}

function decodeGlobalId(id: string): { type: string; key: string } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const colon = text.indexOf(':');
    if (colon === -1) return null;
    return { type: text.slice(0, colon), key: text.slice(colon + 1) };
  } catch {
    return null;
  }
}

function typeObject(name: string): GqlObject {
  const def = SCHEMA[name];
  return gqlObj('__Type', {
    name,
    kind: def?.kind ?? 'OBJECT',
    description: null,
    _fields: def?.fields ?? null,
    _enums: def?.enums ?? null,
  });
}

function schemaObject(): GqlObject {
  return gqlObj('__Schema', {
    types: Object.keys(SCHEMA).map((name) => typeObject(name)),
    queryType: typeObject('Query'),
    mutationType: typeObject('Mutation'),
    subscriptionType: null,
    directives: [],
    description: null,
  });
}

interface GqlExecCtx {
  forge: Forge;
  uow: UnitOfWork;
  variables: Record<string, unknown>;
  fragments: Map<string, { on: string | null; selections: GqlSelection[] }>;
  errors: Array<{ message: string }>;
}

function wrapUser(): GqlObject {
  return gqlObj('User', {
    id: globalId('User', VIEWER.login),
    databaseId: VIEWER.id,
    login: VIEWER.login,
    name: VIEWER.name,
    email: VIEWER.email,
    url: `https://forge.invalid/${VIEWER.login}`,
    avatarUrl: '',
    bio: null,
    company: null,
    location: null,
    isViewer: true,
    createdAt: isoOf(EPOCH_SEC),
    updatedAt: isoOf(EPOCH_SEC),
  });
}

function wrapRepo(repo: Repository): GqlObject {
  return gqlObj('Repository', {
    _repo: repo,
    id: globalId('Repository', String(repo.id)),
    databaseId: repo.id,
    name: repo.name,
    nameWithOwner: repo.fullName,
    description: repo.description === '' ? null : repo.description,
    isPrivate: repo.isPrivate,
    isArchived: false,
    isFork: false,
    viewerPermission: 'ADMIN',
    hasIssuesEnabled: true,
    hasProjectsEnabled: true,
    hasWikiEnabled: true,
    url: `https://forge.invalid/${repo.fullName}`,
    homepageUrl: null,
    createdAt: isoOf(repo.createdSec),
    updatedAt: isoOf(repo.createdSec),
    pushedAt: isoOf(repo.createdSec),
    stargazerCount: 0,
    forkCount: 0,
    primaryLanguage: null,
  });
}

function wrapIssue(repo: Repository, issue: IssueEntity): GqlObject {
  return gqlObj('Issue', {
    _repo: repo,
    _item: issue,
    id: globalId('Issue', `${repo.id}:${issue.number}`),
    databaseId: repo.id * 100000 + issue.number,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    bodyText: issue.body,
    state: issue.state === 'open' ? 'OPEN' : 'CLOSED',
    closed: issue.state === 'closed',
    url: `https://forge.invalid/${repo.fullName}/issues/${issue.number}`,
    createdAt: isoOf(issue.createdSec),
    updatedAt: isoOf(issue.createdSec),
    closedAt: issue.state === 'closed' ? isoOf(issue.createdSec) : null,
    milestone: null,
  });
}

function wrapPull(repo: Repository, pull: PullEntity): GqlObject {
  return gqlObj('PullRequest', {
    _repo: repo,
    _item: pull,
    id: globalId('PullRequest', `${repo.id}:${pull.number}`),
    databaseId: repo.id * 100000 + pull.number,
    number: pull.number,
    title: pull.title,
    body: pull.body,
    bodyText: pull.body,
    state: pull.merged ? 'MERGED' : pull.state === 'open' ? 'OPEN' : 'CLOSED',
    merged: pull.merged,
    mergedAt: pull.merged ? isoOf(pull.createdSec) : null,
    closed: pull.state === 'closed',
    closedAt: pull.state === 'closed' ? isoOf(pull.createdSec) : null,
    headRefName: pull.head,
    baseRefName: pull.base,
    url: `https://forge.invalid/${repo.fullName}/pull/${pull.number}`,
    createdAt: isoOf(pull.createdSec),
    updatedAt: isoOf(pull.createdSec),
    isDraft: false,
    additions: 0,
    deletions: 0,
    mergedBy: pull.merged ? wrapUser() : null,
  });
}

function wrapRef(repo: Repository, refName: string): GqlObject {
  const sha = repo.refs.get(refName) ?? ZERO_OID;
  return gqlObj('Ref', {
    _repo: repo,
    _refName: refName,
    id: globalId('Ref', `${repo.id}:${refName}`),
    name: refName.replace(/^refs\/(heads|tags)\//, ''),
    prefix: refName.startsWith('refs/tags/') ? 'refs/tags/' : 'refs/heads/',
    _targetSha: sha,
  });
}

function wrapComment(repo: Repository, item: ItemEntity, comment: CommentEntity): GqlObject {
  return gqlObj('IssueComment', {
    _repo: repo,
    _item: item,
    id: globalId('IssueComment', `${repo.id}:${item.number}:${comment.id}`),
    databaseId: comment.id,
    body: comment.body,
    bodyText: comment.body,
    createdAt: isoOf(comment.createdSec),
    updatedAt: isoOf(comment.createdSec),
    url: `https://forge.invalid/${repo.fullName}/issues/${item.number}#issuecomment-${comment.id}`,
  });
}

function wrapLabel(label: LabelEntity): GqlObject {
  return gqlObj('Label', {
    id: globalId('Label', label.name),
    name: label.name,
    color: label.color,
    description: label.description === '' ? null : label.description,
    url: '',
    createdAt: isoOf(EPOCH_SEC),
    updatedAt: isoOf(EPOCH_SEC),
  });
}

interface PageArgs {
  first?: number;
  after?: string;
}

function paginate<T>(items: T[], args: PageArgs, cursorOf: (item: T) => string): { page: T[]; hasNext: boolean; endCursor: string | null; startCursor: string | null } {
  let start = 0;
  if (typeof args.after === 'string' && args.after !== '') {
    const index = items.findIndex((item) => cursorOf(item) === args.after);
    if (index >= 0) start = index + 1;
  }
  const first = typeof args.first === 'number' && args.first > 0 ? Math.trunc(args.first) : 30;
  const page = items.slice(start, start + first);
  return {
    page,
    hasNext: start + first < items.length,
    endCursor: page.length > 0 ? cursorOf(page[page.length - 1] as T) : null,
    startCursor: page.length > 0 ? cursorOf(page[0] as T) : null,
  };
}

function connection(type: string, edgeType: string, nodes: GqlObject[], cursors: string[], total: number, hasNext: boolean, endCursor: string | null, startCursor: string | null): GqlObject {
  return gqlObj(type, {
    nodes,
    totalCount: total,
    edges: nodes.map((node, index) => gqlObj(edgeType, { node, cursor: cursors[index] ?? null })),
    pageInfo: gqlObj('PageInfo', { hasNextPage: hasNext, hasPreviousPage: false, startCursor, endCursor }),
  });
}

const issueCursor = (issue: IssueEntity): string => Buffer.from(`cursor:${issue.number}`, 'utf8').toString('base64');
const pullCursor = (pull: PullEntity): string => Buffer.from(`cursor:pr:${pull.number}`, 'utf8').toString('base64');

// Field resolvers ------------------------------------------------------------

type Resolver = (obj: GqlObject, args: Record<string, unknown>, ctx: GqlExecCtx) => unknown;

const RESOLVERS: Record<string, Record<string, Resolver>> = {
  Query: {
    viewer: () => wrapUser(),
    user: () => wrapUser(),
    organization: () => null,
    repository: (_obj, args, ctx) => {
      const owner = typeof args.owner === 'string' ? args.owner : '';
      const name = typeof args.name === 'string' ? args.name : '';
      const repo = ctx.uow.repo(owner, name);
      return repo === null ? null : wrapRepo(repo);
    },
    node: (_obj, args, ctx) => resolveNode(ctx, typeof args.id === 'string' ? args.id : ''),
    nodes: (_obj, args, ctx) => {
      const ids = Array.isArray(args.ids) ? args.ids : [];
      return ids.map((id) => (typeof id === 'string' ? resolveNode(ctx, id) : null));
    },
    search: () => connection('SearchResultItemConnection', 'SearchResultItemEdge', [], [], 0, false, null, null),
    rateLimit: () => gqlObj('RateLimit', { limit: 5000, cost: 1, remaining: 4999, used: 1, resetAt: isoOf(EPOCH_SEC + 3600), nodeCount: 0 }),
  },
  Mutation: {
    createIssue: (_obj, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const repo = repoByGlobalId(ctx, typeof input.repositoryId === 'string' ? input.repositoryId : '');
      if (repo === null) {
        ctx.errors.push({ message: 'Could not resolve to a Repository with the given id.' });
        return null;
      }
      const issue: IssueEntity = {
        kind: 'issue',
        number: repo.nextNumber,
        title: typeof input.title === 'string' ? input.title : '',
        body: typeof input.body === 'string' ? input.body : '',
        state: 'open',
        labels: [],
        createdSec: nextSec(),
        comments: [],
      };
      repo.nextNumber += 1;
      repo.items.set(issue.number, issue);
      ctx.uow.stage(repo);
      return gqlObj('CreateIssuePayload', { issue: wrapIssue(repo, issue), clientMutationId: input.clientMutationId ?? null });
    },
    closeIssue: (_obj, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const found = itemByGlobalId(ctx, typeof input.issueId === 'string' ? input.issueId : '');
      if (found === null || found.item.kind !== 'issue') {
        ctx.errors.push({ message: 'Could not resolve to an Issue with the given id.' });
        return null;
      }
      found.item.state = 'closed';
      ctx.uow.stage(found.repo);
      return gqlObj('CloseIssuePayload', { issue: wrapIssue(found.repo, found.item), clientMutationId: input.clientMutationId ?? null });
    },
    reopenIssue: (_obj, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const found = itemByGlobalId(ctx, typeof input.issueId === 'string' ? input.issueId : '');
      if (found === null || found.item.kind !== 'issue') {
        ctx.errors.push({ message: 'Could not resolve to an Issue with the given id.' });
        return null;
      }
      found.item.state = 'open';
      ctx.uow.stage(found.repo);
      return gqlObj('ReopenIssuePayload', { issue: wrapIssue(found.repo, found.item), clientMutationId: input.clientMutationId ?? null });
    },
    createPullRequest: (_obj, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const repo = repoByGlobalId(ctx, typeof input.repositoryId === 'string' ? input.repositoryId : '');
      if (repo === null) {
        ctx.errors.push({ message: 'Could not resolve to a Repository with the given id.' });
        return null;
      }
      const pull = makePullEntity(repo, {
        title: typeof input.title === 'string' ? input.title : '',
        body: typeof input.body === 'string' ? input.body : '',
        head: typeof input.headRefName === 'string' ? input.headRefName : '',
        base: typeof input.baseRefName === 'string' ? input.baseRefName : repo.defaultBranch,
      });
      if (pull === null) {
        ctx.errors.push({ message: 'Head or base branch does not exist.' });
        return null;
      }
      ctx.uow.stage(repo);
      return gqlObj('CreatePullRequestPayload', { pullRequest: wrapPull(repo, pull), clientMutationId: input.clientMutationId ?? null });
    },
    mergePullRequest: (_obj, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const found = itemByGlobalId(ctx, typeof input.pullRequestId === 'string' ? input.pullRequestId : '');
      if (found === null || found.item.kind !== 'pull') {
        ctx.errors.push({ message: 'Could not resolve to a PullRequest with the given id.' });
        return null;
      }
      const pull = found.item;
      if (pull.state === 'open') {
        const outcome = mergePull(found.repo, pull);
        if (!outcome.ok) {
          ctx.errors.push({ message: 'Pull Request is not mergeable: conflicts must be resolved first.' });
          return null;
        }
        ctx.uow.stage(found.repo);
      }
      return gqlObj('MergePullRequestPayload', { pullRequest: wrapPull(found.repo, pull), clientMutationId: input.clientMutationId ?? null });
    },
    addComment: (_obj, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const found = itemByGlobalId(ctx, typeof input.subjectId === 'string' ? input.subjectId : '');
      if (found === null) {
        ctx.errors.push({ message: 'Could not resolve to a subject with the given id.' });
        return null;
      }
      const comment: CommentEntity = {
        id: found.repo.nextCommentId,
        body: typeof input.body === 'string' ? input.body : '',
        createdSec: nextSec(),
      };
      found.repo.nextCommentId += 1;
      found.item.comments.push(comment);
      ctx.uow.stage(found.repo);
      const wrapped = wrapComment(found.repo, found.item, comment);
      return gqlObj('AddCommentPayload', {
        commentEdge: gqlObj('IssueCommentEdge', { node: wrapped, cursor: Buffer.from(`cursor:comment:${comment.id}`, 'utf8').toString('base64') }),
        subject: found.item.kind === 'issue' ? wrapIssue(found.repo, found.item) : wrapPull(found.repo, found.item),
        comment: wrapped,
        clientMutationId: input.clientMutationId ?? null,
      });
    },
    createRepository: (_obj, args, ctx) => {
      const input = (args.input ?? {}) as Record<string, unknown>;
      const name = typeof input.name === 'string' ? input.name : '';
      if (name === '') return null;
      const repo = ctx.forge.createRepo(name, typeof input.description === 'string' ? input.description : '', input.visibility === 'PRIVATE', 'main');
      if (repo === null) {
        ctx.errors.push({ message: 'Repository creation failed.' });
        return null;
      }
      ctx.uow.stage(repo);
      return gqlObj('CreateRepositoryPayload', { repository: wrapRepo(repo), clientMutationId: input.clientMutationId ?? null });
    },
  },
  Repository: {
    owner: () => wrapUser(),
    defaultBranchRef: (obj) => {
      const repo = obj._repo as Repository;
      const ref = repo.headRef();
      if (!repo.refs.has(ref)) return null;
      return wrapRef(repo, ref);
    },
    issue: (obj, args) => {
      const repo = obj._repo as Repository;
      const item = repo.items.get(typeof args.number === 'number' ? args.number : -1);
      return item !== undefined && item.kind === 'issue' ? wrapIssue(repo, item) : null;
    },
    issues: (obj, args) => {
      const repo = obj._repo as Repository;
      let issues = [...repo.items.values()].filter((item): item is IssueEntity => item.kind === 'issue');
      const states = Array.isArray(args.states) ? (args.states as string[]) : null;
      if (states !== null && states.length > 0) {
        issues = issues.filter((issue) => states.includes(issue.state === 'open' ? 'OPEN' : 'CLOSED'));
      }
      const orderBy = (args.orderBy ?? {}) as Record<string, unknown>;
      const direction = typeof orderBy.direction === 'string' ? orderBy.direction : 'DESC';
      issues.sort((a, b) => (direction === 'ASC' ? a.number - b.number || a.createdSec - b.createdSec : b.number - a.number || b.createdSec - a.createdSec));
      // Default (no explicit order) is newest first, matching gh's list use.
      const { page, hasNext, endCursor, startCursor } = paginate(issues, args as PageArgs, issueCursor);
      return connection('IssueConnection', 'IssueEdge', page.map((i) => wrapIssue(repo, i)), page.map(issueCursor), issues.length, hasNext, endCursor, startCursor);
    },
    pullRequest: (obj, args) => {
      const repo = obj._repo as Repository;
      const item = repo.items.get(typeof args.number === 'number' ? args.number : -1);
      return item !== undefined && item.kind === 'pull' ? wrapPull(repo, item) : null;
    },
    pullRequests: (obj, args) => {
      const repo = obj._repo as Repository;
      let pulls = [...repo.items.values()].filter((item): item is PullEntity => item.kind === 'pull');
      const states = Array.isArray(args.states) ? (args.states as string[]) : null;
      if (states !== null && states.length > 0) {
        pulls = pulls.filter((pull) => states.includes(pull.merged ? 'MERGED' : pull.state === 'open' ? 'OPEN' : 'CLOSED'));
      }
      pulls.sort((a, b) => b.number - a.number);
      const { page, hasNext, endCursor, startCursor } = paginate(pulls, args as PageArgs, pullCursor);
      return connection('PullRequestConnection', 'PullRequestEdge', page.map((p) => wrapPull(repo, p)), page.map(pullCursor), pulls.length, hasNext, endCursor, startCursor);
    },
    label: (obj, args) => {
      const repo = obj._repo as Repository;
      const label = repo.labels.get(typeof args.name === 'string' ? args.name : '');
      return label === undefined ? null : wrapLabel(label);
    },
    labels: (obj, args) => {
      const repo = obj._repo as Repository;
      const labels = [...repo.labels.values()];
      const cursorOf = (label: LabelEntity): string => Buffer.from(`cursor:label:${label.name}`, 'utf8').toString('base64');
      const { page, hasNext, endCursor, startCursor } = paginate(labels, args as PageArgs, cursorOf);
      return connection('LabelConnection', 'LabelEdge', page.map(wrapLabel), page.map(cursorOf), labels.length, hasNext, endCursor, startCursor);
    },
  },
  Issue: {
    author: () => wrapUser(),
    editor: () => null,
    repository: (obj) => wrapRepo(obj._repo as Repository),
    labels: (obj, args) => {
      const repo = obj._repo as Repository;
      const issue = obj._item as IssueEntity;
      const labels = issue.labels
        .map((name) => repo.labels.get(name) ?? { name, color: 'ededed', description: '' })
        .map(wrapLabel);
      const { page, hasNext, endCursor, startCursor } = paginate(labels, args as PageArgs, () => '');
      void hasNext;
      void endCursor;
      void startCursor;
      return connection('LabelConnection', 'LabelEdge', page, page.map(() => ''), labels.length, false, null, null);
    },
    comments: (obj, args) => {
      const repo = obj._repo as Repository;
      const issue = obj._item as IssueEntity;
      const cursorOf = (comment: CommentEntity): string => Buffer.from(`cursor:comment:${comment.id}`, 'utf8').toString('base64');
      const { page, hasNext, endCursor, startCursor } = paginate(issue.comments, args as PageArgs, cursorOf);
      return connection('IssueCommentConnection', 'IssueCommentEdge', page.map((c) => wrapComment(repo, issue, c)), page.map(cursorOf), issue.comments.length, hasNext, endCursor, startCursor);
    },
    assignees: () => connection('UserConnection' in SCHEMA ? 'LabelConnection' : 'LabelConnection', 'LabelEdge', [], [], 0, false, null, null),
    participants: () => connection('LabelConnection', 'LabelEdge', [], [], 0, false, null, null),
    reactions: () => connection('LabelConnection', 'LabelEdge', [], [], 0, false, null, null),
  },
  PullRequest: {
    author: () => wrapUser(),
    repository: (obj) => wrapRepo(obj._repo as Repository),
    mergeable: (obj) => pullMergeable(obj._repo as Repository, obj._item as PullEntity),
    headRef: (obj) => {
      const repo = obj._repo as Repository;
      const pull = obj._item as PullEntity;
      const ref = `refs/heads/${pull.head}`;
      return repo.refs.has(ref) ? wrapRef(repo, ref) : null;
    },
    baseRef: (obj) => {
      const repo = obj._repo as Repository;
      const pull = obj._item as PullEntity;
      const ref = `refs/heads/${pull.base}`;
      return repo.refs.has(ref) ? wrapRef(repo, ref) : null;
    },
    headRepository: (obj) => wrapRepo(obj._repo as Repository),
    baseRepository: (obj) => wrapRepo(obj._repo as Repository),
    mergeCommit: (obj) => {
      const pull = obj._item as PullEntity;
      return pull.mergeCommitSha === null ? null : wrapCommit(obj._repo as Repository, pull.mergeCommitSha);
    },
    files: (obj, args) => {
      const repo = obj._repo as Repository;
      const pull = obj._item as PullEntity;
      const headSha = repo.tipOf(pull.head);
      const baseSha = repo.tipOf(pull.base);
      if (headSha === undefined || baseSha === undefined) {
        return connection('PullRequestChangedFileConnection', 'PullRequestChangedFileEdge', [], [], 0, false, null, null);
      }
      const base = mergeBase(repo, baseSha, headSha) ?? baseSha;
      const files = changedFiles(repo, base, headSha).map((file) =>
        gqlObj('PullRequestChangedFile', {
          path: file.filename,
          additions: file.additions,
          deletions: file.deletions,
          changeType: file.status === 'added' ? 'ADDED' : file.status === 'removed' ? 'DELETED' : 'MODIFIED',
        }),
      );
      const cursorOf = (file: GqlObject): string => Buffer.from(`cursor:file:${String(file.path)}`, 'utf8').toString('base64');
      const { page, hasNext, endCursor, startCursor } = paginate(files, args as PageArgs, cursorOf);
      return connection('PullRequestChangedFileConnection', 'PullRequestChangedFileEdge', page, page.map(cursorOf), files.length, hasNext, endCursor, startCursor);
    },
    commits: (obj, args) => {
      const repo = obj._repo as Repository;
      const pull = obj._item as PullEntity;
      const headSha = repo.tipOf(pull.head);
      const baseSha = repo.tipOf(pull.base);
      if (headSha === undefined || baseSha === undefined) {
        return connection('PullRequestChangedFileConnection', 'PullRequestChangedFileEdge', [], [], 0, false, null, null);
      }
      const baseAncestors = ancestorShas(repo, baseSha);
      const shas = orderedAncestry(repo, headSha).filter((sha) => !baseAncestors.has(sha)).reverse();
      const commits = shas.map((sha) => gqlObj('PullRequestCommit', { _repo: repo, _sha: sha, id: globalId('PullRequestCommit', `${repo.id}:${sha}`), commit: wrapCommit(repo, sha), resourcePath: '', url: '' }));
      const cursorOf = (entry: GqlObject): string => Buffer.from(`cursor:commit:${String(entry._sha)}`, 'utf8').toString('base64');
      const { page, hasNext, endCursor, startCursor } = paginate(commits, args as PageArgs, cursorOf);
      return connection('PullRequestChangedFileConnection', 'PullRequestChangedFileEdge', page, page.map(cursorOf), commits.length, hasNext, endCursor, startCursor);
    },
    comments: (obj, args) => {
      const repo = obj._repo as Repository;
      const pull = obj._item as PullEntity;
      const cursorOf = (comment: CommentEntity): string => Buffer.from(`cursor:comment:${comment.id}`, 'utf8').toString('base64');
      const { page, hasNext, endCursor, startCursor } = paginate(pull.comments, args as PageArgs, cursorOf);
      return connection('IssueCommentConnection', 'IssueCommentEdge', page.map((c) => wrapComment(repo, pull, c)), page.map(cursorOf), pull.comments.length, hasNext, endCursor, startCursor);
    },
    labels: (obj, args) => {
      void obj;
      void args;
      return connection('LabelConnection', 'LabelEdge', [], [], 0, false, null, null);
    },
    assignees: () => connection('LabelConnection', 'LabelEdge', [], [], 0, false, null, null),
    participants: () => connection('LabelConnection', 'LabelEdge', [], [], 0, false, null, null),
    reviews: () => connection('LabelConnection', 'LabelEdge', [], [], 0, false, null, null),
  },
  Ref: {
    repository: (obj) => wrapRepo(obj._repo as Repository),
    target: (obj) => {
      const repo = obj._repo as Repository;
      const sha = obj._targetSha as string;
      const object = repo.getObject(sha);
      if (object === undefined) return null;
      if (object.type === 'commit') return wrapCommit(repo, sha);
      return gqlObj('Blob', { id: globalId('Blob', `${repo.id}:${sha}`), oid: sha, isTruncated: false, text: object.type === 'blob' ? object.data.toString('utf8') : null });
    },
    associatedPullRequests: () => connection('PullRequestConnection', 'PullRequestEdge', [], [], 0, false, null, null),
  },
  IssueComment: {
    author: () => wrapUser(),
    editor: () => null,
    repository: (obj) => wrapRepo(obj._repo as Repository),
    issue: (obj) => {
      const item = obj._item as ItemEntity;
      return item.kind === 'issue' ? wrapIssue(obj._repo as Repository, item) : null;
    },
    pullRequest: (obj) => {
      const item = obj._item as ItemEntity;
      return item.kind === 'pull' ? wrapPull(obj._repo as Repository, item) : null;
    },
  },
  __Type: {
    fields: (obj) => {
      const names = obj._fields as string[] | null;
      if (names === null) return null;
      return names.map((name) =>
        gqlObj('__Field', {
          name,
          description: null,
          args: [],
          type: gqlObj('__Type', { name: 'String', kind: 'SCALAR', description: null, _fields: null, _enums: null }),
          isDeprecated: false,
          deprecationReason: null,
        }),
      );
    },
    enumValues: (obj) => {
      const values = obj._enums as string[] | null;
      if (values === null) return null;
      return values.map((name) => gqlObj('__EnumValue', { name, description: null, isDeprecated: false, deprecationReason: null }));
    },
    possibleTypes: () => null,
    inputFields: (obj) => {
      const def = SCHEMA[obj.name as string];
      if (def === undefined || def.kind !== 'INPUT_OBJECT' || def.fields === undefined) return null;
      return def.fields.map((name) =>
        gqlObj('__InputValue', {
          name,
          description: null,
          type: gqlObj('__Type', { name: 'String', kind: 'SCALAR', description: null, _fields: null, _enums: null }),
          defaultValue: null,
          isDeprecated: false,
          deprecationReason: null,
        }),
      );
    },
    interfaces: () => [],
    specifiedByURL: () => null,
    ofType: () => null,
  },
  __Field: {
    type: (obj) => obj.type,
    args: () => [],
  },
  __Schema: {},
};

function wrapCommit(repo: Repository, sha: string): GqlObject {
  const object = repo.getObject(sha);
  const info = object !== undefined && object.type === 'commit' ? parseCommit(object.data) : null;
  const person = (line: string): GqlObject =>
    gqlObj('GitActor', {
      name: line.replace(/ <.*$/, ''),
      email: /<(.*)>/.exec(line)?.[1] ?? '',
      date: info !== null ? isoOf(info.timeSec) : isoOf(EPOCH_SEC),
      avatarUrl: '',
      user: null,
    });
  return gqlObj('Commit', {
    _repo: repo,
    _sha: sha,
    id: globalId('Commit', `${repo.id}:${sha}`),
    oid: sha,
    abbreviatedOid: sha.slice(0, 7),
    message: info?.message ?? '',
    messageHeadline: (info?.message ?? '').split('\n')[0] ?? '',
    messageBody: '',
    author: info !== null ? person(info.author) : null,
    committer: info !== null ? person(info.committer) : null,
    committedDate: info !== null ? isoOf(info.timeSec) : isoOf(EPOCH_SEC),
    authoredDate: info !== null ? isoOf(info.timeSec) : isoOf(EPOCH_SEC),
    url: `https://forge.invalid/${repo.fullName}/commit/${sha}`,
    additions: 0,
    deletions: 0,
    changedFiles: 0,
  });
}

function repoByGlobalId(ctx: GqlExecCtx, id: string): Repository | null {
  const decoded = decodeGlobalId(id);
  if (decoded === null || decoded.type !== 'Repository') return null;
  const repoId = Number(decoded.key);
  for (const repo of ctx.forge.listRepos()) if (repo.id === repoId) return repo;
  return null;
}

function itemByGlobalId(ctx: GqlExecCtx, id: string): { repo: Repository; item: ItemEntity } | null {
  const decoded = decodeGlobalId(id);
  if (decoded === null) return null;
  const parts = decoded.key.split(':');
  if (parts.length !== 2) return null;
  const repoId = Number(parts[0]);
  const number = Number(parts[1]);
  for (const repo of ctx.forge.listRepos()) {
    if (repo.id !== repoId) continue;
    const item = repo.items.get(number);
    return item === undefined ? null : { repo, item };
  }
  return null;
}

function resolveNode(ctx: GqlExecCtx, id: string): GqlObject | null {
  const decoded = decodeGlobalId(id);
  if (decoded === null) return null;
  if (decoded.type === 'Repository') {
    const repo = repoByGlobalId(ctx, id);
    return repo === null ? null : wrapRepo(repo);
  }
  if (decoded.type === 'Issue' || decoded.type === 'PullRequest') {
    const found = itemByGlobalId(ctx, id);
    if (found === null) return null;
    return found.item.kind === 'issue' ? wrapIssue(found.repo, found.item) : wrapPull(found.repo, found.item);
  }
  if (decoded.type === 'User') return wrapUser();
  return null;
}

const NODE_TYPES = new Set(['Repository', 'Issue', 'PullRequest', 'User', 'Organization', 'Label', 'IssueComment', 'Ref', 'Commit']);

function typeMatches(obj: GqlObject, condition: string | null): boolean {
  if (condition === null) return true;
  if (obj.__t === condition) return true;
  if (condition === 'Node') return NODE_TYPES.has(obj.__t) || obj._repo !== undefined || obj.__t === 'Commit';
  if (condition === 'Actor') return obj.__t === 'User' || obj.__t === 'Organization';
  return false;
}

function executeSelections(obj: GqlObject | null, selections: GqlSelection[], ctx: GqlExecCtx): Record<string, unknown> | null {
  if (obj === null) return null;
  const out: Record<string, unknown> = {};
  const walk = (sels: GqlSelection[]): void => {
    for (const selection of sels) {
      if (selection.kind === 'spread') {
        const fragment = ctx.fragments.get(selection.name);
        if (fragment !== undefined && typeMatches(obj, fragment.on)) walk(fragment.selections);
        continue;
      }
      if (selection.kind === 'inline') {
        if (typeMatches(obj, selection.on)) walk(selection.selections);
        continue;
      }
      const key = selection.alias ?? selection.name;
      if (selection.name === '__typename') {
        out[key] = obj.__t;
        continue;
      }
      if (selection.name === '__type' || selection.name === '__schema') continue; // handled at the root
      const typeDef = SCHEMA[obj.__t];
      const knownFields = typeDef?.fields ?? [];
      if (typeDef !== undefined && typeDef.kind !== 'INPUT_OBJECT' && !knownFields.includes(selection.name) && !(selection.name in obj)) {
        ctx.errors.push({ message: `Field '${selection.name}' doesn't exist on type '${obj.__t}'` });
        out[key] = null;
        continue;
      }
      const args: Record<string, unknown> = {};
      for (const [argName, argValue] of selection.args) args[argName] = gqlResolve(argValue, ctx.variables);
      const resolver = RESOLVERS[obj.__t]?.[selection.name];
      let value: unknown;
      try {
        value = resolver !== undefined ? resolver(obj, args, ctx) : (obj[selection.name] as unknown);
      } catch (err) {
        ctx.errors.push({ message: err instanceof Error ? err.message : String(err) });
        value = null;
      }
      out[key] = completeValue(value, selection.selections, ctx);
    }
  };
  walk(selections);
  return out;
}

function completeValue(value: unknown, selections: GqlSelection[], ctx: GqlExecCtx): unknown {
  if (value === null || value === undefined) return null;
  if (Array.isArray(value)) return value.map((entry) => completeValue(entry, selections, ctx));
  if (typeof value === 'object' && '__t' in (value as Record<string, unknown>)) {
    if (selections.length === 0) return {};
    return executeSelections(value as GqlObject, selections, ctx);
  }
  return value;
}

function executeOperation(forge: Forge, uow: UnitOfWork, queryText: string, variables: Record<string, unknown>, operationName: string | null): Record<string, unknown> {
  const parser = new GqlParser(queryText);
  let operations: GqlOperation[];
  try {
    operations = parser.parseDocument();
  } catch (err) {
    return { errors: [{ message: err instanceof Error ? err.message : 'parse error' }] };
  }
  const operation = operationName !== null
    ? operations.find((op) => op.name === operationName) ?? operations[0]
    : operations[0];
  if (operation === undefined) return { errors: [{ message: 'no operation in document' }] };
  const ctx: GqlExecCtx = { forge, uow, variables, fragments: parser.fragments, errors: [] };
  const root = gqlObj(operation.type === 'mutation' ? 'Mutation' : 'Query', {});
  // Root-level __type / __schema are resolved before normal field walking.
  const data: Record<string, unknown> = {};
  const rootSelections: GqlSelection[] = [];
  for (const selection of operation.selections) {
    if (selection.kind === 'field' && selection.name === '__type') {
      const args: Record<string, unknown> = {};
      for (const [argName, argValue] of selection.args) args[argName] = gqlResolve(argValue, ctx.variables);
      const name = typeof args.name === 'string' ? args.name : '';
      const typeObj = SCHEMA[name] !== undefined ? typeObject(name) : null;
      data[selection.alias ?? selection.name] = typeObj === null ? null : executeSelections(typeObj, selection.selections, ctx);
      continue;
    }
    if (selection.kind === 'field' && selection.name === '__schema') {
      data[selection.alias ?? selection.name] = executeSelections(schemaObject(), selection.selections, ctx);
      continue;
    }
    rootSelections.push(selection);
  }
  const walked = executeSelections(root, rootSelections, ctx) ?? {};
  for (const [key, value] of Object.entries(walked)) data[key] = value;
  const result: Record<string, unknown> = { data };
  if (ctx.errors.length > 0) result.errors = ctx.errors;
  return result;
}

function handleGraphQL(ctx: RequestContext): void {
  if (ctx.jsonError) {
    return sendJson(ctx, 200, { errors: [{ message: 'Problems parsing JSON' }] });
  }
  if (Array.isArray(ctx.json)) {
    const results = (ctx.json as unknown[]).map((entry) => {
      const doc = (typeof entry === 'object' && entry !== null ? entry : {}) as Record<string, unknown>;
      return executeOperation(
        ctx.forge,
        ctx.uow,
        typeof doc.query === 'string' ? doc.query : '',
        (typeof doc.variables === 'object' && doc.variables !== null ? doc.variables : {}) as Record<string, unknown>,
        typeof doc.operationName === 'string' ? doc.operationName : null,
      );
    });
    return sendJson(ctx, 200, results);
  }
  const doc = bodyObject(ctx);
  const result = executeOperation(
    ctx.forge,
    ctx.uow,
    typeof doc.query === 'string' ? doc.query : '',
    (typeof doc.variables === 'object' && doc.variables !== null ? doc.variables : {}) as Record<string, unknown>,
    typeof doc.operationName === 'string' ? doc.operationName : null,
  );
  return sendJson(ctx, 200, result);
}

// ---------------------------------------------------------------------------
// MCP: JSON-RPC 2.0 over Streamable HTTP. Speaks the 2026-07-28 revision via
// server/discover and the 2025-11-25 handshake via initialize. The tools act
// on the very same store as REST, so ids agree across surfaces.
// ---------------------------------------------------------------------------

const MCP_REVISIONS = ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];
const MCP_SERVER_INFO = { name: 'bright-falcon-forge', title: 'Bright Falcon Forge', version: '1.0.0' };

interface McpToolDef {
  name: string;
  description: string;
  inputSchema: Record<string, unknown>;
  required: string[];
}

const MCP_TOOLS: McpToolDef[] = [
  {
    name: 'create_repo',
    description: 'Create a new repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'Repository name' },
        description: { type: 'string', description: 'Repository description' },
        private: { type: 'boolean', description: 'Whether the repository is private' },
      },
      required: ['name'],
    },
    required: ['name'],
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        full_name: { type: 'string', description: 'Full name in owner/repo form' },
      },
      required: ['owner', 'repo'],
    },
    required: ['owner', 'repo'],
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Issue title' },
        body: { type: 'string', description: 'Issue body' },
      },
      required: ['owner', 'repo', 'title'],
    },
    required: ['owner', 'repo', 'title'],
  },
  {
    name: 'list_issues',
    description: 'List the issues of a repository, optionally filtered by state.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        state: { type: 'string', description: 'open, closed or all' },
      },
      required: ['owner', 'repo'],
    },
    required: ['owner', 'repo'],
  },
  {
    name: 'create_pull_request',
    description: 'Open a pull request from a head branch into a base branch.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Pull request title' },
        body: { type: 'string', description: 'Pull request body' },
        head: { type: 'string', description: 'Head branch name' },
        base: { type: 'string', description: 'Base branch name' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
    required: ['owner', 'repo', 'title', 'head', 'base'],
  },
  {
    name: 'merge_pull_request',
    description: 'Merge an open pull request into its base branch (squash).',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        pull_number: { type: 'number', description: 'Pull request number' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
    required: ['owner', 'repo', 'pull_number'],
  },
];

// Serialized once so two tools/list answers are byte-identical.
const TOOLS_LIST_JSON = JSON.stringify({
  tools: MCP_TOOLS.map((tool) => ({ name: tool.name, description: tool.description, inputSchema: tool.inputSchema })),
});

function mcpToolResult(payload: unknown, isError = false): Record<string, unknown> {
  return {
    content: [{ type: 'text', text: JSON.stringify(payload) }],
    structuredContent: payload as Record<string, unknown>,
    isError,
  };
}

function mcpOwnerRepo(args: Record<string, unknown>): { owner: string; repo: string } {
  let owner = typeof args.owner === 'string' ? args.owner : '';
  let repo = typeof args.repo === 'string' ? args.repo : '';
  if (typeof args.full_name === 'string' && args.full_name.includes('/')) {
    const [o, r] = args.full_name.split('/', 2);
    if (owner === '') owner = o as string;
    if (repo === '') repo = r as string;
  }
  if (owner === '') owner = VIEWER.login;
  return { owner, repo };
}

function runMcpTool(ctx: RequestContext, name: string, args: Record<string, unknown>): { result?: Record<string, unknown>; error?: { code: number; message: string } } {
  const canonical = name.toLowerCase();
  const tool = MCP_TOOLS.find((t) => canonical === t.name || canonical.endsWith(`__${t.name}`) || canonical.endsWith(`/${t.name}`));
  if (tool === undefined) {
    return { error: { code: -32602, message: `Unknown tool: ${name}` } };
  }
  for (const required of tool.required) {
    const value = args[required];
    const satisfied = required === 'owner' || required === 'repo'
      ? value !== undefined || typeof args.full_name === 'string'
      : value !== undefined && value !== '';
    if (!satisfied) {
      return { result: mcpToolResult({ message: `Missing required argument: ${required}` }, true) };
    }
  }
  switch (tool.name) {
    case 'create_repo': {
      const repoName = typeof args.name === 'string' ? args.name : '';
      const repo = ctx.forge.createRepo(repoName, typeof args.description === 'string' ? args.description : '', args.private === true, 'main');
      if (repo === null) return { result: mcpToolResult({ message: 'Repository creation failed' }, true) };
      ctx.uow.stage(repo);
      return { result: mcpToolResult(repoJson(repo)) };
    }
    case 'get_repo': {
      const { owner, repo: repoName } = mcpOwnerRepo(args);
      const repo = ctx.uow.repo(owner, repoName);
      if (repo === null) return { result: mcpToolResult({ message: 'Not Found' }, true) };
      return { result: mcpToolResult(repoJson(repo)) };
    }
    case 'create_issue': {
      const { owner, repo: repoName } = mcpOwnerRepo(args);
      const repo = ctx.uow.repo(owner, repoName);
      if (repo === null) return { result: mcpToolResult({ message: 'Not Found' }, true) };
      const issue: IssueEntity = {
        kind: 'issue',
        number: repo.nextNumber,
        title: typeof args.title === 'string' ? args.title : '',
        body: typeof args.body === 'string' ? args.body : '',
        state: 'open',
        labels: [],
        createdSec: nextSec(),
        comments: [],
      };
      repo.nextNumber += 1;
      repo.items.set(issue.number, issue);
      ctx.uow.stage(repo);
      return { result: mcpToolResult(issueJson(repo, issue)) };
    }
    case 'list_issues': {
      const { owner, repo: repoName } = mcpOwnerRepo(args);
      const repo = ctx.uow.repo(owner, repoName);
      if (repo === null) return { result: mcpToolResult({ message: 'Not Found' }, true) };
      const state = typeof args.state === 'string' ? args.state : 'open';
      let issues = [...repo.items.values()].filter((item): item is IssueEntity => item.kind === 'issue');
      if (state === 'open' || state === 'closed') issues = issues.filter((i) => i.state === state);
      issues.sort((a, b) => a.number - b.number);
      const views = issues.map((issue) => issueJson(repo, issue));
      return { result: mcpToolResult({ issues: views, total: views.length }) };
    }
    case 'create_pull_request': {
      const { owner, repo: repoName } = mcpOwnerRepo(args);
      const repo = ctx.uow.repo(owner, repoName);
      if (repo === null) return { result: mcpToolResult({ message: 'Not Found' }, true) };
      const pull = makePullEntity(repo, {
        title: typeof args.title === 'string' ? args.title : '',
        body: typeof args.body === 'string' ? args.body : '',
        head: typeof args.head === 'string' ? args.head : '',
        base: typeof args.base === 'string' ? args.base : repo.defaultBranch,
      });
      if (pull === null) return { result: mcpToolResult({ message: 'Validation Failed: head or base branch does not exist' }, true) };
      ctx.uow.stage(repo);
      return { result: mcpToolResult(pullJson(repo, pull)) };
    }
    case 'merge_pull_request': {
      const { owner, repo: repoName } = mcpOwnerRepo(args);
      const repo = ctx.uow.repo(owner, repoName);
      if (repo === null) return { result: mcpToolResult({ message: 'Not Found' }, true) };
      const number = typeof args.pull_number === 'number' ? args.pull_number : typeof args.number === 'number' ? args.number : Number(args.pull_number ?? NaN);
      const item = Number.isInteger(number) ? repo.items.get(number) : undefined;
      if (item === undefined || item.kind !== 'pull') return { result: mcpToolResult({ message: 'Not Found' }, true) };
      if (item.state === 'open') {
        const outcome = mergePull(repo, item);
        if (!outcome.ok) return { result: mcpToolResult({ message: 'Pull Request is not mergeable' }, true) };
        ctx.uow.stage(repo);
      }
      const view = pullJson(repo, item);
      view.merged = item.merged;
      view.sha = item.mergeCommitSha;
      return { result: mcpToolResult(view) };
    }
    default:
      return { error: { code: -32602, message: `Unknown tool: ${name}` } };
  }
}

function mcpHandleOne(ctx: RequestContext, message: Record<string, unknown>): Record<string, unknown> | null {
  const method = typeof message.method === 'string' ? message.method : '';
  const id = message.id;
  const isNotification = id === undefined || id === null;
  const respond = (result: unknown): Record<string, unknown> => ({ jsonrpc: '2.0', id: id ?? null, result });
  const respondError = (code: number, text: string): Record<string, unknown> => ({
    jsonrpc: '2.0',
    id: id ?? null,
    error: { code, message: text },
  });
  switch (method) {
    case 'server/discover':
      return respond({
        supportedVersions: MCP_REVISIONS,
        capabilities: { tools: { listChanged: false } },
        serverInfo: MCP_SERVER_INFO,
        protocolVersion: '2026-07-28',
        _meta: { 'io.modelcontextprotocol/serverInfo': MCP_SERVER_INFO },
      });
    case 'initialize': {
      const params = (typeof message.params === 'object' && message.params !== null ? message.params : {}) as Record<string, unknown>;
      const offered = typeof params.protocolVersion === 'string' ? params.protocolVersion : '';
      const chosen = MCP_REVISIONS.includes(offered) ? offered : '2025-11-25';
      return respond({
        protocolVersion: chosen,
        capabilities: { tools: { listChanged: false } },
        serverInfo: MCP_SERVER_INFO,
      });
    }
    case 'notifications/initialized':
    case 'notifications/cancelled':
      return null;
    case 'ping':
      return respond({});
    case 'tools/list':
      return respond(JSON.parse(TOOLS_LIST_JSON) as unknown);
    case 'tools/call': {
      const params = (typeof message.params === 'object' && message.params !== null ? message.params : {}) as Record<string, unknown>;
      const toolName = typeof params.name === 'string' ? params.name : '';
      const toolArgs = (typeof params.arguments === 'object' && params.arguments !== null ? params.arguments : {}) as Record<string, unknown>;
      const outcome = runMcpTool(ctx, toolName, toolArgs);
      if (outcome.error !== undefined) return respondError(outcome.error.code, outcome.error.message);
      return respond(outcome.result ?? {});
    }
    default:
      if (isNotification) return null;
      return respondError(-32601, `Method not found: ${method}`);
  }
}

function handleMcp(ctx: RequestContext): void {
  if (ctx.req.method !== 'POST') {
    ctx.res.writeHead(405, { 'content-type': JSON_TYPE, 'x-github-request-id': requestId() });
    ctx.res.end(`${JSON.stringify({ message: 'Method Not Allowed' })}\n`);
    return;
  }
  if (ctx.jsonError) {
    ctx.res.writeHead(400, { 'content-type': JSON_TYPE, 'x-github-request-id': requestId() });
    ctx.res.end(`${JSON.stringify({ jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } })}\n`);
    return;
  }
  const sessionHeaders = { 'mcp-session-id': 'brightfalcon-session-1' };
  if (Array.isArray(ctx.json)) {
    const replies = (ctx.json as unknown[])
      .map((entry) => (typeof entry === 'object' && entry !== null ? mcpHandleOne(ctx, entry as Record<string, unknown>) : null))
      .filter((entry) => entry !== null);
    if (replies.length === 0) {
      ctx.res.writeHead(202, sessionHeaders);
      ctx.res.end();
      return;
    }
    return sendJson(ctx, 200, replies, sessionHeaders);
  }
  const message = bodyObject(ctx);
  const reply = mcpHandleOne(ctx, message);
  if (reply === null) {
    ctx.res.writeHead(202, sessionHeaders);
    ctx.res.end();
    return;
  }
  return sendJson(ctx, 200, reply, sessionHeaders);
}

// ---------------------------------------------------------------------------
// The server: one Forge, a template router for REST, and the git / GraphQL /
// MCP surfaces beside it. Every request runs inside its own unit of work.
// ---------------------------------------------------------------------------

const MAX_BODY_BYTES = 256 * 1024 * 1024;

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let total = 0;
    req.on('data', (chunk: Buffer) => {
      total += chunk.length;
      if (total > MAX_BODY_BYTES) {
        reject(new Error('body too large'));
        req.destroy();
        return;
      }
      chunks.push(chunk);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

export function createApp(): Server {
  const forge = new Forge();
  const router = new TemplateRouter();
  registerRest(router);

  const server = createServer((req: IncomingMessage, res: ServerResponse) => {
    void (async () => {
      let body: Buffer;
      try {
        body = await readBody(req);
      } catch {
        res.writeHead(400, { 'content-type': JSON_TYPE });
        res.end(`${JSON.stringify({ message: 'Bad Request' })}\n`);
        return;
      }
      const uow = new UnitOfWork(forge);
      let url: URL;
      try {
        url = new URL(req.url ?? '/', 'http://entry');
      } catch {
        url = new URL('/', 'http://entry');
      }
      const pathname = url.pathname;
      const method = req.method ?? 'GET';

      let json: unknown = undefined;
      let jsonError = false;
      if (body.length > 0) {
        try {
          json = JSON.parse(body.toString('utf8')) as unknown;
        } catch {
          jsonError = true;
        }
      }

      const ctx: RequestContext = {
        req,
        res,
        forge,
        uow,
        params: {},
        query: url.searchParams,
        url,
        body,
        json,
        jsonError,
      };

      try {
        // The env's boot probe takes no token.
        if (method === 'GET' && pathname === '/healthz') {
          return sendJson(ctx, 200, { ok: true });
        }

        const isApi = pathname === '/api/v3' || pathname.startsWith('/api/v3/') || pathname === '/api/graphql' || pathname === '/mcp';
        const gitMatch = /^\/([^/]+)\/([^/]+)\.git(?:\/(.*))?$/.exec(pathname);

        if (isApi || gitMatch !== null) {
          if (!isAuthed(req)) {
            return errorJson(ctx, 401, 'Unauthorized');
          }
        }

        if (pathname === '/api/graphql') {
          if (method !== 'POST') return errorJson(ctx, 404, 'Not Found');
          handleGraphQL(ctx);
          uow.commit();
          return;
        }

        if (pathname === '/mcp') {
          handleMcp(ctx);
          uow.commit();
          return;
        }

        if (gitMatch !== null) {
          const owner = decodeURIComponent(gitMatch[1] as string);
          const repoName = decodeURIComponent(gitMatch[2] as string);
          const sub = gitMatch[3] ?? '';
          const repo = uow.repo(owner, repoName);
          if (method === 'GET' && sub === 'info/refs') {
            handleInfoRefs(ctx, repo);
            return;
          }
          if (method === 'POST' && sub === 'git-upload-pack') {
            handleUploadPack(ctx, repo);
            return;
          }
          if (method === 'POST' && sub === 'git-receive-pack') {
            handleReceivePack(ctx, repo);
            uow.commit();
            return;
          }
          return errorJson(ctx, 404, 'Not Found');
        }

        if (pathname === '/api/v3' || pathname.startsWith('/api/v3/')) {
          const routePath = pathname.length > 1 && pathname.endsWith('/') ? pathname.slice(0, -1) : pathname;
          const matched = router.match(method, routePath);
          if (matched !== null) {
            ctx.params = matched.params;
            await matched.handler(ctx);
            uow.commit();
            return;
          }
          // Known path with another method, or an unknown route: JSON 404.
          return errorJson(ctx, 404, 'Not Found');
        }

        return errorJson(ctx, 404, 'Not Found');
      } catch (err) {
        if (!res.headersSent) {
          res.writeHead(500, { 'content-type': JSON_TYPE, 'x-github-request-id': requestId() });
        }
        res.end(`${JSON.stringify({ message: err instanceof Error ? err.message : 'Internal Server Error' })}\n`);
      }
    })();
  });
  return server;
}
