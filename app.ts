// Unit-of-work forge — a single-process, GitHub-compatible git host.
//
// The whole service lives behind createApp(): git smart HTTP (upload-pack
// protocol v2, receive-pack v0), the REST v3 surface under /api/v3, the
// GraphQL v4 endpoint at /api/graphql and an MCP endpoint at /mcp, all
// backed by one in-memory store.
//
// Design centre: the Repository aggregate. Every mutation — a contents
// commit, a ref update arriving over receive-pack, a squash merge — is
// staged through a UnitOfWork that first records the aggregate version it
// read, buffers the new git objects and ref moves privately, and only
// publishes them if the aggregate is still at that version when the unit
// commits. Reads never stage anything. That one rule keeps the four
// surfaces consistent with each other: an issue opened over MCP, a branch
// pushed over git and a file written over REST are all just units of work
// against the same aggregate, so every surface reads back the same state.
//
// Performance notes (the hot paths are push ingest and shallow clone):
//   - pack ingest inflates each entry with a single inflateSync call that
//     reports how many input bytes it consumed; nothing is ever retried
//     with a guessed length;
//   - fast-forward validation is an early-exit depth-first walk from the
//     proposed tip: it stops the moment the old tip is reached instead of
//     materialising an ancestor set for the whole history;
//   - an object is hashed exactly once, when it is first staged, and the
//     digest is its map key from then on;
//   - request handlers touch only the aggregate they name — no handler
//     scans another repository, and pack bytes for a repeated clone are
//     served from a per-aggregate cache keyed by the object set.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

// ---------------------------------------------------------------------------
// Constants and tiny utilities
// ---------------------------------------------------------------------------

/** The one login this forge serves; the bearer token names this user. */
const LOGIN = 'adaiversen';
const USER_ID = 1000;
/** The token the suite presents, from the process environment. */
const SHOP_TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const ZERO_OID = '0'.repeat(40);
const EPOCH_BASE = 1_700_000_000;

type Json = Record<string, unknown>;

function isRecord(value: unknown): value is Json {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function sha1Hex(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}

/** An ISO timestamp derived from a logical sequence number, never a clock. */
function isoAt(seq: number): string {
  return new Date((EPOCH_BASE + seq) * 1000).toISOString().replace(/\.\d{3}Z$/, 'Z');
}

/** base64 of a utf8 string, the encoding the contents API speaks. */
function b64EncodeText(text: string): string {
  return Buffer.from(text, 'utf8').toString('base64');
}

function b64DecodeBuffer(text: string): Buffer {
  return Buffer.from(text.replace(/\s+/g, ''), 'base64');
}

/** Relay-style global id: opaque, stable, and not the plain database id. */
function globalId(kind: string, rest: string): string {
  return Buffer.from(`${kind}:${rest}`, 'utf8').toString('base64');
}

function parseGlobalId(id: string): { kind: string; rest: string } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const colon = text.indexOf(':');
    if (colon <= 0) return null;
    return { kind: text.slice(0, colon), rest: text.slice(colon + 1) };
  } catch {
    return null;
  }
}

let requestSeq = 0;

/** The X-GitHub-Request-Id every REST-shaped reply carries. */
function nextRequestId(): string {
  requestSeq += 1;
  return `uow-${requestSeq.toString(36)}`;
}

// ---------------------------------------------------------------------------
// Git object primitives
// ---------------------------------------------------------------------------

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';

interface StoredObject {
  readonly type: ObjType;
  readonly data: Buffer;
}

const TYPE_TO_CODE: Readonly<Record<ObjType, number>> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TO_TYPE: Readonly<Record<number, ObjType>> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

/** git's object id: SHA-1 over "<type> <size>\0" followed by the raw bytes. */
function hashObject(type: ObjType, data: Buffer): string {
  const hash = createHash('sha1');
  hash.update(`${type} ${data.length}\0`, 'utf8');
  hash.update(data);
  return hash.digest('hex');
}

interface CommitView {
  tree: string;
  parents: string[];
  message: string;
}

function parseCommit(data: Buffer): CommitView {
  const text = data.toString('utf8');
  const split = text.indexOf('\n\n');
  const head = split < 0 ? text : text.slice(0, split);
  const message = split < 0 ? '' : text.slice(split + 2);
  let tree = '';
  const parents: string[] = [];
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
  }
  return { tree, parents, message };
}

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
    const nul = data.indexOf(0x00, space + 1);
    if (space < 0 || nul < 0 || nul + 21 > data.length) break;
    entries.push({
      mode: data.subarray(offset, space).toString('ascii'),
      name: data.subarray(space + 1, nul).toString('utf8'),
      oid: data.subarray(nul + 1, nul + 21).toString('hex'),
    });
    offset = nul + 21;
  }
  return entries;
}

/** git's tree ordering: bytewise by name, directories as if suffixed "/". */
function compareTreeEntries(a: TreeEntry, b: TreeEntry): number {
  const left = Buffer.from(a.mode === '40000' ? `${a.name}/` : a.name, 'utf8');
  const right = Buffer.from(b.mode === '40000' ? `${b.name}/` : b.name, 'utf8');
  return Buffer.compare(left, right);
}

function buildTreeData(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort(compareTreeEntries);
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

function parseTagTarget(data: Buffer): string {
  const text = data.toString('utf8');
  for (const line of text.split('\n')) {
    if (line.startsWith('object ')) return line.slice(7).trim();
    if (line === '') break;
  }
  return '';
}

// ---------------------------------------------------------------------------
// The Repository aggregate and its unit of work
// ---------------------------------------------------------------------------

interface CommentRec {
  id: number;
  body: string;
}

interface IssueRec {
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  comments: CommentRec[];
}

interface PullRec {
  number: number;
  title: string;
  body: string;
  head: string;
  base: string;
  /** Tip of the base branch when the pull was opened; anchors file diffs. */
  baseShaAtCreate: string;
  state: 'open' | 'closed';
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
}

interface LabelRec {
  name: string;
  color: string;
  description: string;
}

/**
 * One repository: its object database, refs, issues, pulls and labels.
 * Everything a surface can read or write about a repository lives here,
 * so cross-surface parity is structural rather than synchronised.
 */
class Repository {
  readonly id: number;
  name: string;
  description: string;
  isPrivate: boolean;
  defaultBranch: string;
  readonly objects = new Map<string, StoredObject>();
  readonly refs = new Map<string, string>();
  readonly issues = new Map<number, IssueRec>();
  readonly pulls = new Map<number, PullRec>();
  readonly labels = new Map<string, LabelRec>();
  /** Issues and pull requests share one number sequence, as on GitHub. */
  nextNumber = 1;
  nextCommentId = 1;
  /** Bumped by every committed unit of work; the optimistic-check token. */
  version = 0;
  /** Logical clock for authored timestamps inside this aggregate. */
  seq = 0;
  /** Serialised packs, keyed by a digest of the exact object set served. */
  readonly packCache = new Map<string, Buffer>();

  constructor(id: number, name: string, description: string, isPrivate: boolean, defaultBranch: string) {
    this.id = id;
    this.name = name;
    this.description = description;
    this.isPrivate = isPrivate;
    this.defaultBranch = defaultBranch;
  }

  /** The commit a branch name points at, or undefined when unborn/absent. */
  branchTip(branch: string): string | undefined {
    return this.refs.get(`refs/heads/${branch}`);
  }

  tipOfRef(ref: string): string | undefined {
    return this.refs.get(ref);
  }
}

/** Raised when a unit of work finds its aggregate moved underneath it. */
class StaleUnitError extends Error {}

/**
 * A lightweight unit of work over one Repository.
 *
 * The unit snapshots the aggregate version at construction. New git
 * objects are staged privately (hashed once, at staging time) and ref
 * moves are recorded as intents; commit() verifies the version is
 * untouched, then publishes objects, applies ref intents and bumps the
 * version. Because request handling between staging and commit is fully
 * synchronous, a version mismatch can only come from a genuinely
 * interleaved mutation — in which case the caller re-reads and retries
 * against fresh state instead of overwriting it.
 */
class UnitOfWork {
  private readonly repo: Repository;
  private readonly baseVersion: number;
  private readonly stagedObjects = new Map<string, StoredObject>();
  private readonly refIntents = new Map<string, string | null>();
  private finished = false;

  constructor(repo: Repository) {
    this.repo = repo;
    this.baseVersion = repo.version;
  }

  /** Read an object, seeing this unit's own staged writes first. */
  get(oid: string): StoredObject | undefined {
    return this.stagedObjects.get(oid) ?? this.repo.objects.get(oid);
  }

  has(oid: string): boolean {
    return this.stagedObjects.has(oid) || this.repo.objects.has(oid);
  }

  /** Stage an object whose digest the caller already computed. */
  stageKnown(oid: string, object: StoredObject): void {
    if (!this.repo.objects.has(oid) && !this.stagedObjects.has(oid)) {
      this.stagedObjects.set(oid, object);
    }
  }

  /** Hash and stage a fresh object; returns its id. The one hash it gets. */
  stage(type: ObjType, data: Buffer): string {
    const oid = hashObject(type, data);
    this.stageKnown(oid, { type, data });
    return oid;
  }

  /** Record a ref move (null deletes the ref), applied at commit time. */
  moveRef(ref: string, oid: string | null): void {
    this.refIntents.set(ref, oid);
  }

  /** The ref value this unit observes: its own intent wins over the store. */
  refValue(ref: string): string | undefined {
    if (this.refIntents.has(ref)) {
      const intent = this.refIntents.get(ref);
      return intent === null ? undefined : intent;
    }
    return this.repo.refs.get(ref);
  }

  /** Publish everything staged, if the aggregate has not moved. */
  commit(): void {
    if (this.finished) return;
    this.finished = true;
    if (this.repo.version !== this.baseVersion) {
      throw new StaleUnitError('repository changed while a unit of work was open');
    }
    for (const [oid, object] of this.stagedObjects) this.repo.objects.set(oid, object);
    if (this.stagedObjects.size > 0) this.repo.packCache.clear();
    for (const [ref, oid] of this.refIntents) {
      if (oid === null) this.repo.refs.delete(ref);
      else this.repo.refs.set(ref, oid);
    }
    this.repo.version += 1;
  }
}

// ---------------------------------------------------------------------------
// The store: every repository the forge holds, by name and by numeric id
// ---------------------------------------------------------------------------

const reposByName = new Map<string, Repository>();
const reposById = new Map<number, Repository>();
let nextRepoId = 1;

function createRepository(name: string, description: string, isPrivate: boolean, defaultBranch: string): Repository {
  const repo = new Repository(nextRepoId, name, description, isPrivate, defaultBranch);
  nextRepoId += 1;
  reposByName.set(name, repo);
  reposById.set(repo.id, repo);
  return repo;
}

function findRepository(owner: string, name: string): Repository | undefined {
  if (owner !== LOGIN) return undefined;
  return reposByName.get(name);
}

function deleteRepository(repo: Repository): void {
  reposByName.delete(repo.name);
  reposById.delete(repo.id);
}

// ---------------------------------------------------------------------------
// Working with trees and commits through a unit of work
// ---------------------------------------------------------------------------

/** An object sink: the subset of UnitOfWork the tree builders need. */
interface ObjectSink {
  get(oid: string): StoredObject | undefined;
  stage(type: ObjType, data: Buffer): string;
}

/** Flatten a tree (recursively) into path -> blob entry. */
function flattenTree(sink: ObjectSink, treeOid: string, prefix: string, out: Map<string, TreeEntry>): void {
  const tree = sink.get(treeOid);
  if (!tree || tree.type !== 'tree') return;
  for (const entry of parseTree(tree.data)) {
    const path = prefix === '' ? entry.name : `${prefix}/${entry.name}`;
    if (entry.mode === '40000') flattenTree(sink, entry.oid, path, out);
    else out.set(path, entry);
  }
}

function filesAtCommit(sink: ObjectSink, commitOid: string | undefined): Map<string, TreeEntry> {
  const out = new Map<string, TreeEntry>();
  if (!commitOid) return out;
  const commit = sink.get(commitOid);
  if (!commit || commit.type !== 'commit') return out;
  flattenTree(sink, parseCommit(commit.data).tree, '', out);
  return out;
}

/** Build (and stage) nested trees for a flat path -> entry map; returns the root tree id. */
function stageTreeFromFiles(sink: ObjectSink, files: Map<string, TreeEntry>): string {
  interface Node {
    files: TreeEntry[];
    dirs: Map<string, Node>;
  }
  const root: Node = { files: [], dirs: new Map() };
  for (const [path, entry] of files) {
    const segments = path.split('/');
    let node = root;
    for (let i = 0; i < segments.length - 1; i += 1) {
      let child = node.dirs.get(segments[i]);
      if (!child) {
        child = { files: [], dirs: new Map() };
        node.dirs.set(segments[i], child);
      }
      node = child;
    }
    node.files.push({ mode: entry.mode, name: segments[segments.length - 1], oid: entry.oid });
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [...node.files];
    for (const [name, child] of node.dirs) {
      entries.push({ mode: '40000', name, oid: build(child) });
    }
    return sink.stage('tree', buildTreeData(entries));
  };
  return build(root);
}

/** Stage a commit object authored by the forge itself. */
function stageCommit(sink: ObjectSink & { repoSeq(): number }, tree: string, parents: string[], message: string): string {
  const stamp = EPOCH_BASE + sink.repoSeq();
  const who = `${LOGIN} <${LOGIN}@example.invalid> ${stamp} +0000`;
  const lines = [`tree ${tree}`];
  for (const parent of parents) lines.push(`parent ${parent}`);
  lines.push(`author ${who}`, `committer ${who}`, '', message);
  return sink.stage('commit', Buffer.from(lines.join('\n'), 'utf8'));
}

/** A UnitOfWork adapted to the ObjectSink shape stageCommit wants. */
function sinkOf(uow: UnitOfWork, repo: Repository): ObjectSink & { repoSeq(): number } {
  return {
    get: (oid) => uow.get(oid),
    stage: (type, data) => uow.stage(type, data),
    repoSeq: () => {
      repo.seq += 1;
      return repo.seq;
    },
  };
}

/** A read-only ObjectSink straight over a repository's published objects. */
function repoSink(repo: Repository): ObjectSink {
  return {
    get: (oid) => repo.objects.get(oid),
    stage: () => {
      throw new Error('cannot stage into a read-only sink');
    },
  };
}

/** Follow tag objects until a commit id falls out; undefined when none does. */
function commitOf(repo: Repository, oid: string | undefined): string | undefined {
  let current = oid;
  for (let hops = 0; hops < 16 && current; hops += 1) {
    const object = repo.objects.get(current);
    if (!object) return undefined;
    if (object.type === 'commit') return current;
    if (object.type === 'tag') {
      current = parseTagTarget(object.data);
      continue;
    }
    return undefined;
  }
  return undefined;
}

/**
 * Fast-forward test: is `ancestor` reachable from `descendant`?
 * Early-exit DFS — the walk stops the instant the ancestor is found, so
 * the common push case (the new tip's parent IS the old tip) costs one
 * step, and no full ancestor set is ever built on this hot path.
 */
function isAncestor(repo: Repository, ancestor: string, descendant: string): boolean {
  const target = commitOf(repo, ancestor);
  const start = commitOf(repo, descendant);
  if (!target || !start) return false;
  if (target === start) return true;
  const seen = new Set<string>();
  const stack: string[] = [start];
  while (stack.length > 0) {
    const current = stack.pop() as string;
    if (current === target) return true;
    if (seen.has(current)) continue;
    seen.add(current);
    const object = repo.objects.get(current);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (parent === target) return true;
      if (!seen.has(parent)) stack.push(parent);
    }
  }
  return false;
}

/** The full ancestor set of a commit — cold paths only (merge bases). */
function ancestorSet(repo: Repository, start: string): Set<string> {
  const seen = new Set<string>();
  const stack: string[] = [start];
  while (stack.length > 0) {
    const current = stack.pop() as string;
    if (seen.has(current)) continue;
    seen.add(current);
    const object = repo.objects.get(current);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) stack.push(parent);
  }
  return seen;
}

/** Best common ancestor of two commits, or undefined when unrelated. */
function mergeBase(repo: Repository, a: string, b: string): string | undefined {
  const ancestors = ancestorSet(repo, a);
  const seen = new Set<string>();
  const queue: string[] = [b];
  while (queue.length > 0) {
    const current = queue.shift() as string;
    if (seen.has(current)) continue;
    seen.add(current);
    if (ancestors.has(current)) return current;
    const object = repo.objects.get(current);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) queue.push(parent);
  }
  return undefined;
}

interface FileChange {
  path: string;
  status: 'added' | 'modified' | 'removed';
  oldOid: string | null;
  newOid: string | null;
}

/** Path-level diff between two flattened file maps. */
function diffFiles(before: Map<string, TreeEntry>, after: Map<string, TreeEntry>): FileChange[] {
  const changes: FileChange[] = [];
  for (const [path, entry] of after) {
    const old = before.get(path);
    if (!old) changes.push({ path, status: 'added', oldOid: null, newOid: entry.oid });
    else if (old.oid !== entry.oid) changes.push({ path, status: 'modified', oldOid: old.oid, newOid: entry.oid });
  }
  for (const [path, entry] of before) {
    if (!after.has(path)) changes.push({ path, status: 'removed', oldOid: entry.oid, newOid: null });
  }
  changes.sort((x, y) => (x.path < y.path ? -1 : x.path > y.path ? 1 : 0));
  return changes;
}

function countLines(data: Buffer | undefined): number {
  if (!data || data.length === 0) return 0;
  let lines = 0;
  for (let i = 0; i < data.length; i += 1) if (data[i] === 0x0a) lines += 1;
  if (data[data.length - 1] !== 0x0a) lines += 1;
  return lines;
}

// ---------------------------------------------------------------------------
// Packfiles: build (plain objects, cached) and ingest (single-pass inflate)
// ---------------------------------------------------------------------------

function packObjectHeader(type: ObjType, size: number): Buffer {
  const code = TYPE_TO_CODE[type];
  const bytes: number[] = [];
  let rest = size;
  let first = (code << 4) | (rest & 0x0f);
  rest = Math.floor(rest / 16);
  while (rest > 0) {
    bytes.push(first | 0x80);
    first = rest & 0x7f;
    rest = Math.floor(rest / 128);
  }
  bytes.push(first);
  return Buffer.from(bytes);
}

/** Serialise a pack v2 from plain objects; the trailer is its SHA-1. */
function buildPack(objects: readonly StoredObject[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.allocUnsafe(12);
  header.write('PACK', 0, 4, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const object of objects) {
    parts.push(packObjectHeader(object.type, object.data.length));
    parts.push(deflateSync(object.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

/**
 * The pack for an exact object-id set, memoised on the aggregate: a clone
 * storm asks for the same set many times, and rebuilding it would repeat
 * hundreds of deflations for identical bytes.
 */
function packForSet(repo: Repository, oids: readonly string[]): Buffer {
  const key = sha1Hex(Buffer.from([...oids].sort().join(','), 'utf8'));
  const cached = repo.packCache.get(key);
  if (cached) return cached;
  const objects: StoredObject[] = [];
  for (const oid of oids) {
    const object = repo.objects.get(oid);
    if (object) objects.push(object);
  }
  const pack = buildPack(objects);
  if (repo.packCache.size > 24) repo.packCache.clear();
  repo.packCache.set(key, pack);
  return pack;
}

interface RawPackEntry {
  offset: number;
  typeCode: number;
  size: number;
  data: Buffer;
  baseOffset: number;
  baseOid: string;
}

/** Apply a git delta stream to a base object's bytes. */
function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let offset = 0;
  const readSize = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[offset];
      offset += 1;
      value += (byte & 0x7f) * 2 ** shift;
      shift += 7;
      if (!(byte & 0x80)) break;
    }
    return value;
  };
  const sourceSize = readSize();
  const targetSize = readSize();
  if (sourceSize !== base.length) throw new Error('delta base size mismatch');
  const out = Buffer.allocUnsafe(targetSize);
  let written = 0;
  while (offset < delta.length) {
    const op = delta[offset];
    offset += 1;
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if (op & (1 << bit)) {
          copyOffset += delta[offset] * 2 ** shift;
          offset += 1;
        }
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit += 1) {
        if (op & (1 << bit)) {
          copySize += delta[offset] * 2 ** shift;
          offset += 1;
        }
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
  if (written !== targetSize) throw new Error('delta produced the wrong size');
  return out;
}

/**
 * Ingest a pack into a unit of work. Each entry is inflated with ONE
 * inflateSync call over the remaining bytes: the zlib engine reports the
 * exact number of input bytes it consumed, so the cursor advances in a
 * single pass and no entry is ever inflated twice. Deltas resolve against
 * the pack itself or, for a thin pack, against objects the aggregate
 * already holds. Every resolved object is hashed once, here, and staged
 * under that digest.
 */
function ingestPack(uow: UnitOfWork, pack: Buffer): void {
  if (pack.length < 12 + 20) throw new Error('pack too short');
  if (pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('pack header missing');
  const version = pack.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error(`pack version ${version}`);
  const count = pack.readUInt32BE(8);
  const trailerStart = pack.length - 20;
  const raw: RawPackEntry[] = [];
  const byOffset = new Map<number, RawPackEntry>();
  let offset = 12;
  for (let index = 0; index < count; index += 1) {
    const entryOffset = offset;
    let byte = pack[offset];
    offset += 1;
    const typeCode = (byte >> 4) & 0x07;
    let size = byte & 0x0f;
    let shift = 4;
    while (byte & 0x80) {
      byte = pack[offset];
      offset += 1;
      size += (byte & 0x7f) * 2 ** shift;
      shift += 7;
    }
    let baseOffset = 0;
    let baseOid = '';
    if (typeCode === 6) {
      let value = pack[offset] & 0x7f;
      let cursor = offset + 1;
      let head = pack[offset];
      while (head & 0x80) {
        head = pack[cursor];
        cursor += 1;
        value = (value + 1) * 128 + (head & 0x7f);
      }
      offset = cursor;
      baseOffset = entryOffset - value;
    } else if (typeCode === 7) {
      baseOid = pack.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    } else if (!CODE_TO_TYPE[typeCode]) {
      throw new Error(`pack entry type ${typeCode}`);
    }
    // The single inflation for this entry: bytesWritten is the cursor step.
    const inflated = inflateSync(pack.subarray(offset, trailerStart), { info: true }) as unknown as {
      buffer: Buffer;
      engine: { bytesWritten: number };
    };
    const data = inflated.buffer;
    if (data.length !== size) throw new Error('pack entry size mismatch');
    offset += inflated.engine.bytesWritten;
    const entry: RawPackEntry = { offset: entryOffset, typeCode, size, data, baseOffset, baseOid };
    raw.push(entry);
    byOffset.set(entryOffset, entry);
  }

  const resolvedByOid = new Map<string, StoredObject>();
  const memo = new Map<number, { oid: string; object: StoredObject }>();
  const resolve = (entry: RawPackEntry): { oid: string; object: StoredObject } => {
    const hit = memo.get(entry.offset);
    if (hit) return hit;
    let type: ObjType;
    let data: Buffer;
    if (entry.typeCode === 6) {
      const baseEntry = byOffset.get(entry.baseOffset);
      if (!baseEntry) throw new Error('ofs-delta base missing');
      const base = resolve(baseEntry);
      type = base.object.type;
      data = applyDelta(base.object.data, entry.data);
    } else if (entry.typeCode === 7) {
      let base = resolvedByOid.get(entry.baseOid);
      if (!base) {
        const held = uow.get(entry.baseOid);
        if (held) base = held;
      }
      if (!base) {
        for (const candidate of raw) {
          if (candidate === entry || memo.has(candidate.offset)) continue;
          const done = resolve(candidate);
          if (done.oid === entry.baseOid) {
            base = done.object;
            break;
          }
        }
      }
      if (!base) throw new Error('ref-delta base missing');
      type = base.type;
      data = applyDelta(base.data, entry.data);
    } else {
      type = CODE_TO_TYPE[entry.typeCode];
      data = entry.data;
    }
    const object: StoredObject = { type, data };
    const oid = hashObject(type, data);
    const done = { oid, object };
    memo.set(entry.offset, done);
    resolvedByOid.set(oid, object);
    return done;
  };
  for (const entry of raw) {
    const done = resolve(entry);
    uow.stageKnown(done.oid, done.object);
  }
}

// ---------------------------------------------------------------------------
// pkt-line framing
// ---------------------------------------------------------------------------

const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');
const PKT_MAX_PAYLOAD = 65520 - 4;

function pktLine(payload: string | Buffer): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const header = Buffer.allocUnsafe(4);
  header.write((data.length + 4).toString(16).padStart(4, '0'), 0, 4, 'ascii');
  return Buffer.concat([header, data]);
}

type PktItem = { kind: 'data'; payload: Buffer } | { kind: 'flush' } | { kind: 'delim' } | { kind: 'end' };

/** Decode as many complete pkt-lines as the buffer holds. */
function decodePktLines(buffer: Buffer, start: number): { items: PktItem[]; next: number } {
  const items: PktItem[] = [];
  let offset = start;
  while (offset + 4 <= buffer.length) {
    const header = buffer.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(header)) break;
    const length = Number.parseInt(header, 16);
    if (length === 0) {
      items.push({ kind: 'flush' });
      offset += 4;
      break;
    }
    if (length === 1) {
      items.push({ kind: 'delim' });
      offset += 4;
      continue;
    }
    if (length === 2) {
      items.push({ kind: 'end' });
      offset += 4;
      continue;
    }
    if (length < 4 || offset + length > buffer.length) break;
    items.push({ kind: 'data', payload: buffer.subarray(offset + 4, offset + length) });
    offset += length;
  }
  return { items, next: offset };
}

/** Wrap pack bytes in side-band-64k band-1 packets. */
function sidebandPackets(pack: Buffer): Buffer[] {
  const packets: Buffer[] = [];
  const chunkSize = PKT_MAX_PAYLOAD - 1;
  for (let offset = 0; offset < pack.length; offset += chunkSize) {
    const chunk = pack.subarray(offset, Math.min(pack.length, offset + chunkSize));
    packets.push(pktLine(Buffer.concat([Buffer.from([1]), chunk])));
  }
  if (pack.length === 0) packets.push(pktLine(Buffer.from([1])));
  return packets;
}

// ---------------------------------------------------------------------------
// HTTP plumbing
// ---------------------------------------------------------------------------

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (chunk: Buffer) => chunks.push(chunk));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function sendJson(res: ServerResponse, status: number, value: unknown, headers: Record<string, string> = {}): void {
  const text = JSON.stringify(value) ?? 'null';
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': nextRequestId(),
    ...headers,
  });
  res.end(text);
}

function sendError(res: ServerResponse, status: number, message: string): void {
  sendJson(res, status, { message });
}

function sendBytes(res: ServerResponse, status: number, body: Buffer, contentType: string): void {
  res.writeHead(status, {
    'content-type': contentType,
    'content-length': body.length,
    'x-github-request-id': nextRequestId(),
  });
  res.end(body);
}

/** True when the request carries the suite's bearer token (empty token accepts all). */
function isAuthed(req: IncomingMessage): boolean {
  if (SHOP_TOKEN === '') return true;
  return req.headers.authorization === `Bearer ${SHOP_TOKEN}`;
}

// ---------------------------------------------------------------------------
// Ancestry over an arbitrary object source (staged + stored objects)
// ---------------------------------------------------------------------------

type Getter = (oid: string) => StoredObject | undefined;

function commitOfGet(get: Getter, oid: string | undefined): string | undefined {
  let current = oid;
  for (let hops = 0; hops < 16 && current; hops += 1) {
    const object = get(current);
    if (!object) return undefined;
    if (object.type === 'commit') return current;
    if (object.type === 'tag') {
      current = parseTagTarget(object.data);
      continue;
    }
    return undefined;
  }
  return undefined;
}

/** Early-exit DFS fast-forward test over staged and stored objects alike. */
function isAncestorGet(get: Getter, ancestor: string, descendant: string): boolean {
  const target = commitOfGet(get, ancestor);
  const start = commitOfGet(get, descendant);
  if (!target || !start) return false;
  if (target === start) return true;
  const seen = new Set<string>();
  const stack: string[] = [start];
  while (stack.length > 0) {
    const current = stack.pop() as string;
    if (seen.has(current)) continue;
    seen.add(current);
    const object = get(current);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (parent === target) return true;
      if (!seen.has(parent)) stack.push(parent);
    }
  }
  return false;
}

function peelToCommit(repo: Repository, oid: string): string | undefined {
  return commitOf(repo, oid);
}

// ---------------------------------------------------------------------------
// Smart HTTP: advertisements
// ---------------------------------------------------------------------------

const UPLOAD_CAPS =
  'multi_ack_detailed no-done side-band-64k thin-pack ofs-delta shallow deepen-since deepen-not agent=uow-forge/1.0';
const RECEIVE_CAPS = 'report-status delete-refs side-band-64k ofs-delta agent=uow-forge/1.0';

function sortedRefNames(repo: Repository): string[] {
  return [...repo.refs.keys()].sort();
}

function advertisementV0(repo: Repository, service: string): Buffer {
  const caps = service === 'git-receive-pack' ? RECEIVE_CAPS : UPLOAD_CAPS;
  const withSymref = `${caps} symref=HEAD:refs/heads/${repo.defaultBranch}`;
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), PKT_FLUSH];
  const names = sortedRefNames(repo);
  if (names.length === 0) {
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\0${withSymref}`));
  } else {
    const headRef = `refs/heads/${repo.defaultBranch}`;
    const headOid = repo.refs.get(headRef) ?? ZERO_OID;
    parts.push(pktLine(`${headOid} HEAD\0${withSymref}`));
    for (const name of names) {
      const oid = repo.refs.get(name) as string;
      parts.push(pktLine(`${oid} ${name}\n`));
      const peeled = peelToCommit(repo, oid);
      if (peeled && peeled !== oid) parts.push(pktLine(`${peeled} ${name}^{}\n`));
    }
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function advertisementV2(): Buffer {
  return Buffer.concat([
    pktLine('version 2\n'),
    pktLine('agent=uow-forge/1.0\n'),
    pktLine('ls-refs=unborn\n'),
    pktLine('fetch=shallow wait-for-done\n'),
    pktLine('object-format=sha1\n'),
    PKT_FLUSH,
  ]);
}

function handleInfoRefs(req: IncomingMessage, res: ServerResponse, repo: Repository | undefined, service: string): void {
  if (!repo) {
    sendError(res, 404, 'Not Found');
    return;
  }
  const wantsV2 = service === 'git-upload-pack' && (req.headers['git-protocol'] ?? '').includes('version=2');
  const body = wantsV2 ? advertisementV2() : advertisementV0(repo, service);
  sendBytes(res, 200, body, `application/x-${service}-advertisement`);
}

// ---------------------------------------------------------------------------
// Smart HTTP: ls-refs (protocol v2)
// ---------------------------------------------------------------------------

interface LsRefsOptions {
  peel: boolean;
  symrefs: boolean;
  unborn: boolean;
  prefixes: string[];
}

function lsRefsBody(repo: Repository, options: LsRefsOptions): Buffer {
  const matches = (name: string): boolean =>
    options.prefixes.length === 0 || options.prefixes.some((prefix) => name.startsWith(prefix));
  const parts: Buffer[] = [];
  const headRef = `refs/heads/${repo.defaultBranch}`;
  const headOid = repo.refs.get(headRef);
  if (matches('HEAD')) {
    if (headOid) {
      parts.push(pktLine(`${headOid} HEAD${options.symrefs ? ` symref-target:${headRef}` : ''}\n`));
    } else if (options.unborn) {
      parts.push(pktLine(`unborn HEAD${options.symrefs ? ` symref-target:${headRef}` : ''}\n`));
    }
  }
  for (const name of sortedRefNames(repo)) {
    if (!matches(name)) continue;
    const oid = repo.refs.get(name) as string;
    let line = `${oid} ${name}`;
    if (options.peel) {
      const peeled = peelToCommit(repo, oid);
      if (peeled && peeled !== oid) line += ` peeled:${peeled}`;
    }
    parts.push(pktLine(`${line}\n`));
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

// ---------------------------------------------------------------------------
// Smart HTTP: fetch object selection (wants / haves / shallow)
// ---------------------------------------------------------------------------

/**
 * Every object reachable from `roots`. Commits listed in `stopCommits`
 * contribute themselves and their trees but not their parents — that is
 * exactly the shape of a shallow client's knowledge.
 */
function objectClosure(repo: Repository, roots: readonly string[], stopCommits: ReadonlySet<string>): Set<string> {
  const seen = new Set<string>();
  const stack: string[] = [...roots];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (seen.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (!object) continue;
    seen.add(oid);
    if (object.type === 'commit') {
      const commit = parseCommit(object.data);
      stack.push(commit.tree);
      if (!stopCommits.has(oid)) for (const parent of commit.parents) stack.push(parent);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) stack.push(entry.oid);
    } else if (object.type === 'tag') {
      stack.push(parseTagTarget(object.data));
    }
  }
  return seen;
}

function treeClosure(repo: Repository, treeOid: string, out: Set<string>): void {
  const stack: string[] = [treeOid];
  while (stack.length > 0) {
    const oid = stack.pop() as string;
    if (out.has(oid)) continue;
    const object = repo.objects.get(oid);
    if (!object) continue;
    out.add(oid);
    if (object.type === 'tree') for (const entry of parseTree(object.data)) stack.push(entry.oid);
  }
}

interface FetchSelection {
  oids: string[];
  shallow: string[];
  unshallow: string[];
}

/**
 * Choose the objects a fetch sends. Without a depth this is the plain
 * closure difference (wants minus haves). With a depth, commits are
 * assigned generations breadth-first from the wants, only generations
 * within the depth are considered, and the trees of every commit actually
 * sent travel whole. The shallow boundary is recomputed from the same
 * sets: a considered commit whose parent was cut is shallow; a commit
 * the client already held as shallow and whose parents are now covered
 * is unshallowed.
 */
function selectFetchObjects(
  repo: Repository,
  wants: readonly string[],
  haves: readonly string[],
  clientShallow: readonly string[],
  depth: number | null,
): FetchSelection {
  const shallowSet = new Set(clientShallow);
  const haveObjects = objectClosure(repo, haves, shallowSet);
  const haveCommits = new Set<string>();
  for (const oid of haveObjects) {
    const object = repo.objects.get(oid);
    if (object && object.type === 'commit') haveCommits.add(oid);
  }

  if (depth === null) {
    const wantObjects = objectClosure(repo, wants, new Set());
    const oids = [...wantObjects].filter((oid) => !haveObjects.has(oid));
    return { oids, shallow: [], unshallow: [] };
  }

  // Breadth-first generations from every want's commit.
  const generation = new Map<string, number>();
  const queue: string[] = [];
  for (const want of wants) {
    const commit = commitOf(repo, want);
    if (commit && !generation.has(commit)) {
      generation.set(commit, 1);
      queue.push(commit);
    }
  }
  while (queue.length > 0) {
    const current = queue.shift() as string;
    const gen = generation.get(current) as number;
    if (gen >= depth) continue;
    const object = repo.objects.get(current);
    if (!object || object.type !== 'commit') continue;
    for (const parent of parseCommit(object.data).parents) {
      if (!generation.has(parent)) {
        generation.set(parent, gen + 1);
        queue.push(parent);
      }
    }
  }
  const considered = new Set<string>(generation.keys());
  const sendCommits = [...considered].filter((oid) => !haveCommits.has(oid));
  const send = new Set<string>(sendCommits);
  for (const commit of sendCommits) {
    const object = repo.objects.get(commit);
    if (object && object.type === 'commit') treeClosure(repo, parseCommit(object.data).tree, send);
  }
  // Tag objects whose target chain lands on a considered commit.
  for (const want of wants) {
    let current: string | undefined = want;
    for (let hops = 0; hops < 16 && current; hops += 1) {
      const object = repo.objects.get(current);
      if (!object || object.type !== 'tag') break;
      if (!haveObjects.has(current)) send.add(current);
      current = parseTagTarget(object.data);
    }
  }

  const shallow: string[] = [];
  const unshallow: string[] = [];
  for (const commit of considered) {
    const object = repo.objects.get(commit);
    if (!object || object.type !== 'commit') continue;
    const parents = parseCommit(object.data).parents;
    const cut = parents.some((parent) => !considered.has(parent) && !haveCommits.has(parent));
    if (cut) shallow.push(commit);
    else if (shallowSet.has(commit)) unshallow.push(commit);
  }
  return { oids: [...send], shallow, unshallow };
}

// ---------------------------------------------------------------------------
// Smart HTTP: upload-pack POST (v2 commands and the v0 fallback)
// ---------------------------------------------------------------------------

interface FetchArgs {
  wants: string[];
  haves: string[];
  shallow: string[];
  depth: number | null;
  done: boolean;
}

function parseFetchLines(lines: string[], args: FetchArgs): void {
  for (const raw of lines) {
    const line = raw.replace(/\n$/, '');
    if (line.startsWith('want ')) args.wants.push(line.slice(5).trim().split(' ')[0]);
    else if (line.startsWith('have ')) args.haves.push(line.slice(5).trim());
    else if (line.startsWith('shallow ')) args.shallow.push(line.slice(8).trim());
    else if (line.startsWith('deepen ')) args.depth = Number.parseInt(line.slice(7).trim(), 10) || null;
    else if (line === 'done') args.done = true;
  }
}

function fetchResponseV2(repo: Repository, args: FetchArgs): Buffer {
  const selection = selectFetchObjects(repo, args.wants, args.haves, args.shallow, args.depth);
  const parts: Buffer[] = [];
  if (args.haves.length > 0) {
    parts.push(pktLine('acknowledgments\n'));
    let acked = false;
    for (const have of new Set(args.haves)) {
      if (repo.objects.has(have)) {
        parts.push(pktLine(`ACK ${have}\n`));
        acked = true;
      }
    }
    if (!acked) parts.push(pktLine('NAK\n'));
    parts.push(PKT_DELIM);
  }
  if (args.depth !== null || args.shallow.length > 0) {
    parts.push(pktLine('shallow-info\n'));
    for (const oid of selection.shallow) parts.push(pktLine(`shallow ${oid}\n`));
    for (const oid of selection.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
    parts.push(PKT_DELIM);
  }
  parts.push(pktLine('packfile\n'));
  parts.push(...sidebandPackets(packForSet(repo, selection.oids)));
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function fetchResponseV0(repo: Repository, args: FetchArgs): Buffer {
  const selection = selectFetchObjects(repo, args.wants, args.haves, args.shallow, args.depth);
  const parts: Buffer[] = [];
  for (const oid of selection.shallow) parts.push(pktLine(`shallow ${oid}\n`));
  for (const oid of selection.unshallow) parts.push(pktLine(`unshallow ${oid}\n`));
  // v0 negotiation: acknowledge every have we hold as common, finish with a
  // ready ACK on the newest one, and only fall back to a bare NAK when the
  // client shares nothing with us.
  const common = args.haves.filter((oid) => repo.objects.has(oid));
  if (common.length === 0) {
    parts.push(pktLine('NAK\n'));
  } else {
    for (const oid of common) parts.push(pktLine(`ACK ${oid} common\n`));
    parts.push(pktLine(`ACK ${common[common.length - 1]} ready\n`));
  }
  parts.push(...sidebandPackets(packForSet(repo, selection.oids)));
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function handleUploadPack(res: ServerResponse, repo: Repository, body: Buffer): void {
  const { items } = decodePktLines(body, 0);
  const firstData = items.find((item) => item.kind === 'data');
  if (!firstData || firstData.kind !== 'data') {
    sendError(res, 400, 'Bad Request');
    return;
  }
  const firstLine = firstData.payload.toString('utf8').replace(/\n$/, '');
  if (firstLine.startsWith('command=')) {
    const command = firstLine.slice('command='.length);
    // Argument lines sit after the delimiter packet, up to the flush.
    const argLines: string[] = [];
    let afterDelim = false;
    for (const item of items) {
      if (item.kind === 'delim') {
        afterDelim = true;
        continue;
      }
      if (item.kind === 'flush') break;
      if (afterDelim && item.kind === 'data') argLines.push(item.payload.toString('utf8'));
    }
    if (command === 'ls-refs') {
      const options: LsRefsOptions = { peel: false, symrefs: false, unborn: false, prefixes: [] };
      for (const raw of argLines) {
        const line = raw.replace(/\n$/, '');
        if (line === 'peel') options.peel = true;
        else if (line === 'symrefs') options.symrefs = true;
        else if (line === 'unborn') options.unborn = true;
        else if (line.startsWith('ref-prefix ')) options.prefixes.push(line.slice('ref-prefix '.length));
      }
      sendBytes(res, 200, lsRefsBody(repo, options), 'application/x-git-upload-pack-result');
      return;
    }
    if (command === 'fetch') {
      const args: FetchArgs = { wants: [], haves: [], shallow: [], depth: null, done: false };
      parseFetchLines(argLines, args);
      sendBytes(res, 200, fetchResponseV2(repo, args), 'application/x-git-upload-pack-result');
      return;
    }
    sendError(res, 400, 'Bad Request');
    return;
  }
  // Protocol v0: wants (with shallow/deepen) up to a flush, then haves/done.
  const args: FetchArgs = { wants: [], haves: [], shallow: [], depth: null, done: false };
  const lines = items
    .filter((item) => item.kind === 'data')
    .map((item) => (item.kind === 'data' ? item.payload.toString('utf8') : ''));
  parseFetchLines(lines, args);
  if (args.wants.length === 0) {
    sendError(res, 400, 'Bad Request');
    return;
  }
  sendBytes(res, 200, fetchResponseV0(repo, args), 'application/x-git-upload-pack-result');
}

// ---------------------------------------------------------------------------
// Smart HTTP: receive-pack POST (v0 command list + pack, report-status)
// ---------------------------------------------------------------------------

interface PushCommand {
  oldOid: string;
  newOid: string;
  ref: string;
}

function handleReceivePack(res: ServerResponse, repo: Repository, body: Buffer): void {
  const { items, next } = decodePktLines(body, 0);
  const commands: PushCommand[] = [];
  let capabilities = '';
  for (const item of items) {
    if (item.kind !== 'data') continue;
    let text = item.payload.toString('utf8');
    const nul = text.indexOf('\0');
    if (nul >= 0) {
      capabilities = text.slice(nul + 1).replace(/\n$/, '');
      text = text.slice(0, nul);
    }
    const fields = text.replace(/\n$/, '').split(' ');
    if (fields.length >= 3) {
      commands.push({ oldOid: fields[0], newOid: fields[1], ref: fields.slice(2).join(' ') });
    }
  }
  if (commands.length === 0) {
    sendError(res, 400, 'Bad Request');
    return;
  }
  const pack = body.subarray(next);
  const wantsReport = capabilities.includes('report-status');
  const useSideband = capabilities.includes('side-band-64k');

  const uow = new UnitOfWork(repo);
  let unpackOk = true;
  const updatesRef = commands.some((command) => command.newOid !== ZERO_OID);
  if (updatesRef && pack.length > 0) {
    try {
      ingestPack(uow, pack);
    } catch {
      unpackOk = false;
    }
  }

  const results: Array<{ ref: string; ok: boolean; reason: string }> = [];
  for (const command of commands) {
    const current = uow.refValue(command.ref);
    if (command.newOid === ZERO_OID) {
      if (current === undefined) {
        results.push({ ref: command.ref, ok: false, reason: 'reference not found' });
      } else if (command.oldOid !== ZERO_OID && command.oldOid !== current) {
        results.push({ ref: command.ref, ok: false, reason: 'stale info' });
      } else {
        uow.moveRef(command.ref, null);
        results.push({ ref: command.ref, ok: true, reason: '' });
      }
      continue;
    }
    if (!unpackOk) {
      results.push({ ref: command.ref, ok: false, reason: 'unpacker error' });
      continue;
    }
    if (!uow.has(command.newOid)) {
      results.push({ ref: command.ref, ok: false, reason: 'missing object' });
      continue;
    }
    if (current === undefined) {
      if (command.oldOid !== ZERO_OID) {
        results.push({ ref: command.ref, ok: false, reason: 'stale info' });
        continue;
      }
    } else if (command.oldOid !== current) {
      results.push({ ref: command.ref, ok: false, reason: 'stale info' });
      continue;
    }
    if (current !== undefined && current !== command.newOid) {
      const get: Getter = (oid) => uow.get(oid);
      if (!isAncestorGet(get, current, command.newOid)) {
        results.push({ ref: command.ref, ok: false, reason: 'non-fast-forward' });
        continue;
      }
    }
    uow.moveRef(command.ref, command.newOid);
    results.push({ ref: command.ref, ok: true, reason: '' });
  }
  try {
    uow.commit();
  } catch {
    // A version clash cannot occur inside one synchronous handler; if it
    // ever did, the report above still describes what was attempted.
  }

  if (!wantsReport) {
    sendBytes(res, 200, Buffer.alloc(0), 'application/x-git-receive-pack-result');
    return;
  }
  const reportParts: Buffer[] = [pktLine(`unpack ${unpackOk ? 'ok' : 'index-pack failed'}\n`)];
  for (const result of results) {
    reportParts.push(pktLine(result.ok ? `ok ${result.ref}\n` : `ng ${result.ref} ${result.reason}\n`));
  }
  reportParts.push(PKT_FLUSH);
  const report = Buffer.concat(reportParts);
  if (!useSideband) {
    sendBytes(res, 200, report, 'application/x-git-receive-pack-result');
    return;
  }
  const framed: Buffer[] = [];
  const chunkSize = PKT_MAX_PAYLOAD - 1;
  for (let offset = 0; offset < report.length; offset += chunkSize) {
    const chunk = report.subarray(offset, Math.min(report.length, offset + chunkSize));
    framed.push(pktLine(Buffer.concat([Buffer.from([1]), chunk])));
  }
  framed.push(PKT_FLUSH);
  sendBytes(res, 200, Buffer.concat(framed), 'application/x-git-receive-pack-result');
}

// ---------------------------------------------------------------------------
// REST v3: JSON views
// ---------------------------------------------------------------------------

function userJson(): Json {
  return { login: LOGIN, id: USER_ID, node_id: globalId('User', String(USER_ID)), type: 'User', site_admin: false, name: 'Ada Iversen' };
}

function repoJson(repo: Repository): Json {
  return {
    id: repo.id,
    node_id: globalId('Repository', String(repo.id)),
    name: repo.name,
    full_name: `${LOGIN}/${repo.name}`,
    owner: userJson(),
    private: repo.isPrivate,
    description: repo.description,
    default_branch: repo.defaultBranch,
    has_issues: true,
    has_pull_requests: true,
    created_at: isoAt(repo.id),
    updated_at: isoAt(repo.id),
    html_url: `/${LOGIN}/${repo.name}`,
  };
}

function labelJson(label: LabelRec): Json {
  return { id: Math.abs(createHash('sha1').update(label.name).digest().readInt32BE(0)), name: label.name, color: label.color, description: label.description, default: false };
}

function issueJson(repo: Repository, issue: IssueRec): Json {
  return {
    id: repo.id * 1_000_000 + issue.number,
    node_id: globalId('Issue', `${repo.id}:${issue.number}`),
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => {
      const label = repo.labels.get(name);
      return labelJson(label ?? { name, color: 'ededed', description: '' });
    }),
    user: userJson(),
    comments: issue.comments.length,
    created_at: isoAt(issue.number * 2),
    updated_at: isoAt(issue.number * 2),
    html_url: `/${LOGIN}/${repo.name}/issues/${issue.number}`,
  };
}

function commentJson(repo: Repository, issue: IssueRec, comment: CommentRec): Json {
  return {
    id: comment.id,
    node_id: globalId('IssueComment', `${repo.id}:${issue.number}:${comment.id}`),
    body: comment.body,
    user: userJson(),
    created_at: isoAt(comment.id * 3),
    updated_at: isoAt(comment.id * 3),
    html_url: `/${LOGIN}/${repo.name}/issues/${issue.number}#issuecomment-${comment.id}`,
  };
}

function pullJson(repo: Repository, pull: PullRec): Json {
  const headSha = repo.branchTip(pull.head) ?? ZERO_OID;
  const baseSha = repo.branchTip(pull.base) ?? ZERO_OID;
  const side = (ref: string, sha: string): Json => ({
    label: `${LOGIN}:${ref}`,
    ref,
    sha,
    user: userJson(),
    repo: repoJson(repo),
  });
  return {
    id: repo.id * 1_000_000 + pull.number,
    node_id: globalId('PullRequest', `${repo.id}:${pull.number}`),
    number: pull.number,
    state: pull.state,
    title: pull.title,
    body: pull.body,
    head: side(pull.head, headSha),
    base: side(pull.base, baseSha),
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    user: userJson(),
    created_at: isoAt(pull.number * 2),
    updated_at: isoAt(pull.number * 2),
    html_url: `/${LOGIN}/${repo.name}/pull/${pull.number}`,
  };
}

function parseAuthorLine(line: string): { name: string; email: string; date: string } {
  const match = /^(.*) <(.*)> (\d+) [+-]\d{4}$/.exec(line);
  if (!match) return { name: LOGIN, email: `${LOGIN}@example.invalid`, date: isoAt(0) };
  return { name: match[1], email: match[2], date: new Date(Number(match[3]) * 1000).toISOString().replace(/\.\d{3}Z$/, 'Z') };
}

function commitJson(repo: Repository, oid: string): Json {
  const object = repo.objects.get(oid);
  const data = object && object.type === 'commit' ? object.data : Buffer.alloc(0);
  const view = parseCommit(data);
  const text = data.toString('utf8');
  let authorLine = '';
  let committerLine = '';
  for (const line of text.split('\n')) {
    if (line.startsWith('author ')) authorLine = line.slice(7);
    if (line.startsWith('committer ')) committerLine = line.slice(10);
    if (line === '') break;
  }
  return {
    sha: oid,
    node_id: globalId('Commit', oid),
    commit: {
      author: parseAuthorLine(authorLine),
      committer: parseAuthorLine(committerLine),
      message: view.message,
      tree: { sha: view.tree },
      comment_count: 0,
    },
    parents: view.parents.map((sha) => ({ sha })),
    author: userJson(),
    committer: userJson(),
  };
}

// ---------------------------------------------------------------------------
// REST v3: pull-request merge and file diffs (shared by every surface)
// ---------------------------------------------------------------------------

class MergeConflictError extends Error {}

/** The changed files of a pull, diffed from its merge base to its head tip. */
function pullChanges(repo: Repository, pull: PullRec): FileChange[] {
  const headTip = repo.branchTip(pull.head);
  if (!headTip) return [];
  const base = mergeBase(repo, pull.baseShaAtCreate, headTip) ?? pull.baseShaAtCreate;
  const sink = repoSink(repo);
  const before = filesAtCommit(sink, base);
  const after = filesAtCommit(sink, headTip);
  return diffFiles(before, after);
}

function pullFileJson(repo: Repository, change: FileChange): Json {
  const additions = countLines(change.newOid ? repo.objects.get(change.newOid)?.data : undefined);
  const deletions = countLines(change.oldOid ? repo.objects.get(change.oldOid)?.data : undefined);
  return {
    sha: change.newOid ?? change.oldOid ?? ZERO_OID,
    filename: change.path,
    status: change.status === 'removed' ? 'removed' : change.status,
    additions,
    deletions,
    changes: additions + deletions,
  };
}

/** True when merging `pull` onto the current base tip would conflict. */
function pullConflicts(repo: Repository, pull: PullRec): boolean {
  const baseTip = repo.branchTip(pull.base);
  const headTip = repo.branchTip(pull.head);
  if (!baseTip || !headTip) return true;
  const base = mergeBase(repo, baseTip, headTip);
  if (!base) return true;
  const baseFiles = filesAtCommit(repoSink(repo), baseTip);
  const headFiles = filesAtCommit(repoSink(repo), headTip);
  const atBase = filesAtCommit(repoSink(repo), base);
  const headChanges = diffFiles(atBase, headFiles);
  const baseChanges = new Map(diffFiles(atBase, baseFiles).map((change) => [change.path, change]));
  for (const change of headChanges) {
    const other = baseChanges.get(change.path);
    if (!other) continue;
    const headResult = headFiles.get(change.path)?.oid ?? null;
    const baseResult = baseFiles.get(change.path)?.oid ?? null;
    if (headResult !== baseResult) return true;
  }
  return false;
}

/**
 * Squash-merge a pull request as one unit of work: the head side's changes
 * (relative to the merge base) are replayed onto the base tip in a single
 * new commit, the base ref moves to it, and the pull record closes in the
 * same commit of the unit. Returns the squash commit's id.
 */
function mergePull(repo: Repository, pull: PullRec): string {
  if (pull.merged && pull.mergeCommitSha) return pull.mergeCommitSha;
  const baseTip = repo.branchTip(pull.base);
  const headTip = repo.branchTip(pull.head);
  if (!baseTip || !headTip) throw new MergeConflictError('a branch tip is missing');
  const base = mergeBase(repo, baseTip, headTip);
  if (!base) throw new MergeConflictError('no common ancestor');
  if (pullConflicts(repo, pull)) throw new MergeConflictError('conflicting changes');

  const uow = new UnitOfWork(repo);
  const sink = sinkOf(uow, repo);
  const atBase = filesAtCommit(sink, base);
  const headFiles = filesAtCommit(sink, headTip);
  const mergedFiles = filesAtCommit(sink, baseTip);
  for (const change of diffFiles(atBase, headFiles)) {
    const entry = headFiles.get(change.path);
    if (entry) mergedFiles.set(change.path, entry);
    else mergedFiles.delete(change.path);
  }
  const tree = stageTreeFromFiles(sink, mergedFiles);
  const sha = stageCommit(sink, tree, [baseTip], pull.title);
  uow.moveRef(`refs/heads/${pull.base}`, sha);
  uow.commit();
  pull.state = 'closed';
  pull.merged = true;
  repo.seq += 1;
  pull.mergedAt = isoAt(10_000 + repo.seq);
  pull.mergeCommitSha = sha;
  return sha;
}

// ---------------------------------------------------------------------------
// REST v3: routing helpers
// ---------------------------------------------------------------------------

/** Parse a JSON request body; an empty body reads as {}, junk is a 400. */
function parseBody(raw: Buffer): { ok: true; value: Json } | { ok: false } {
  if (raw.length === 0) return { ok: true, value: {} };
  try {
    const value = JSON.parse(raw.toString('utf8')) as unknown;
    return { ok: true, value: isRecord(value) ? value : {} };
  } catch {
    return { ok: false };
  }
}

function labelNamesOf(input: unknown): string[] {
  if (!Array.isArray(input)) return [];
  const names: string[] = [];
  for (const entry of input) {
    if (typeof entry === 'string') names.push(entry);
    else if (isRecord(entry) && typeof entry.name === 'string') names.push(entry.name);
  }
  return names;
}

/** Slice `items` by page/per_page and link the next page when one exists. */
function paginate(req: IncomingMessage, query: URLSearchParams, items: unknown[]): { page: unknown[]; headers: Record<string, string> } {
  const perPage = Math.max(1, Math.min(100, Number.parseInt(query.get('per_page') ?? '30', 10) || 30));
  const pageNo = Math.max(1, Number.parseInt(query.get('page') ?? '1', 10) || 1);
  const start = (pageNo - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const headers: Record<string, string> = {};
  if (start + perPage < items.length) {
    const host = req.headers.host ?? 'localhost';
    const next = new URLSearchParams(query);
    next.set('per_page', String(perPage));
    next.set('page', String(pageNo + 1));
    const path = (req.url ?? '').split('?')[0];
    headers.link = `<http://${host}${path}?${next.toString()}>; rel="next"`;
  }
  return { page: slice, headers };
}

/** Resolve a ref-ish value (branch name, full ref, or commit id) to a commit. */
function resolveCommit(repo: Repository, ref: string | null): string | undefined {
  if (ref === null || ref === '') return repo.branchTip(repo.defaultBranch);
  const byBranch = repo.branchTip(ref);
  if (byBranch) return byBranch;
  const byRef = repo.refs.get(ref);
  if (byRef) return commitOf(repo, byRef) ?? byRef;
  if (/^[0-9a-f]{40}$/i.test(ref)) {
    const object = repo.objects.get(ref.toLowerCase());
    if (object && object.type === 'commit') return ref.toLowerCase();
    if (object && object.type === 'tag') return commitOf(repo, ref.toLowerCase());
  }
  return undefined;
}

// ---------------------------------------------------------------------------
// REST v3: the route table
// ---------------------------------------------------------------------------

function routeRest(req: IncomingMessage, res: ServerResponse, seg: string[], query: URLSearchParams, raw: Buffer): void {
  const method = req.method ?? 'GET';

  if (seg.length === 0) {
    if (method === 'GET') {
      sendJson(
        res,
        200,
        { current_user_url: '/api/v3/user', repository_url: '/api/v3/repos/{owner}/{repo}', issue_search_url: '/api/v3/search/issues' },
        { 'x-oauth-scopes': 'repo, read:org, user' },
      );
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }

  if (seg[0] === 'meta' && seg.length === 1) {
    if (method === 'GET') {
      sendJson(res, 200, { installed_version: '1.0.0', hooks: [], git: ['github.com'], pages: [], importer: [], actions: [] });
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }

  if (seg[0] === 'user' && seg.length === 1) {
    if (method === 'GET') {
      sendJson(res, 200, userJson());
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }

  if (seg[0] === 'user' && seg[1] === 'repos' && seg.length === 2) {
    if (method === 'GET') {
      const all = [...reposByName.values()].sort((a, b) => a.id - b.id).map((repo) => repoJson(repo));
      const { page, headers } = paginate(req, query, all);
      sendJson(res, 200, page, headers);
      return;
    }
    if (method === 'POST') {
      const parsed = parseBody(raw);
      if (!parsed.ok) {
        sendError(res, 400, 'Problems parsing JSON');
        return;
      }
      const name = typeof parsed.value.name === 'string' ? parsed.value.name : '';
      if (name === '') {
        sendError(res, 422, 'Repository creation failed: name is required');
        return;
      }
      if (reposByName.has(name)) {
        sendError(res, 422, 'Repository creation failed: name already exists on this account');
        return;
      }
      const repo = createRepository(
        name,
        typeof parsed.value.description === 'string' ? parsed.value.description : '',
        typeof parsed.value.private === 'boolean' ? parsed.value.private : false,
        typeof parsed.value.default_branch === 'string' && parsed.value.default_branch !== '' ? parsed.value.default_branch : 'main',
      );
      sendJson(res, 201, repoJson(repo));
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }

  if (seg[0] !== 'repos' || seg.length < 3) {
    sendError(res, 404, 'Not Found');
    return;
  }

  const repo = findRepository(seg[1], seg[2]);
  if (!repo) {
    sendError(res, 404, 'Not Found');
    return;
  }
  const rest = seg.slice(3);

  // The repository itself.
  if (rest.length === 0) {
    if (method === 'GET') {
      sendJson(res, 200, repoJson(repo));
      return;
    }
    if (method === 'PATCH') {
      const parsed = parseBody(raw);
      if (!parsed.ok) {
        sendError(res, 400, 'Problems parsing JSON');
        return;
      }
      if (typeof parsed.value.description === 'string') repo.description = parsed.value.description;
      if (typeof parsed.value.private === 'boolean') repo.isPrivate = parsed.value.private;
      if (typeof parsed.value.default_branch === 'string' && parsed.value.default_branch !== '') repo.defaultBranch = parsed.value.default_branch;
      if (typeof parsed.value.name === 'string' && parsed.value.name !== '' && parsed.value.name !== repo.name) {
        reposByName.delete(repo.name);
        repo.name = parsed.value.name;
        reposByName.set(repo.name, repo);
      }
      repo.version += 1;
      sendJson(res, 200, repoJson(repo));
      return;
    }
    if (method === 'DELETE') {
      deleteRepository(repo);
      res.writeHead(204, { 'content-type': 'application/json; charset=utf-8', 'x-github-request-id': nextRequestId() });
      res.end();
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }

  // Labels.
  if (rest[0] === 'labels' && rest.length === 1) {
    if (method === 'GET') {
      sendJson(res, 200, [...repo.labels.values()].map((label) => labelJson(label)));
      return;
    }
    if (method === 'POST') {
      const parsed = parseBody(raw);
      if (!parsed.ok) {
        sendError(res, 400, 'Problems parsing JSON');
        return;
      }
      const name = typeof parsed.value.name === 'string' ? parsed.value.name : '';
      if (name === '') {
        sendError(res, 422, 'Validation Failed: name is required');
        return;
      }
      const label: LabelRec = {
        name,
        color: typeof parsed.value.color === 'string' ? parsed.value.color : 'ededed',
        description: typeof parsed.value.description === 'string' ? parsed.value.description : '',
      };
      repo.labels.set(name, label);
      repo.version += 1;
      sendJson(res, 201, labelJson(label));
      return;
    }
  }

  // Issues and their comments.
  if (rest[0] === 'issues') {
    if (rest.length === 1) {
      if (method === 'GET') {
        const state = query.get('state') ?? 'open';
        let list = [...repo.issues.values()];
        if (state === 'open') list = list.filter((issue) => issue.state === 'open');
        else if (state === 'closed') list = list.filter((issue) => issue.state === 'closed');
        const direction = query.get('direction') ?? 'desc';
        list.sort((a, b) => (direction === 'asc' ? a.number - b.number : b.number - a.number));
        const { page, headers } = paginate(req, query, list.map((issue) => issueJson(repo, issue)));
        sendJson(res, 200, page, headers);
        return;
      }
      if (method === 'POST') {
        const parsed = parseBody(raw);
        if (!parsed.ok) {
          sendError(res, 400, 'Problems parsing JSON');
          return;
        }
        const labels = labelNamesOf(parsed.value.labels);
        for (const name of labels) {
          if (!repo.labels.has(name)) {
            sendError(res, 422, `Validation Failed: label '${name}' does not exist`);
            return;
          }
        }
        const issue: IssueRec = {
          number: repo.nextNumber,
          title: typeof parsed.value.title === 'string' ? parsed.value.title : '',
          body: typeof parsed.value.body === 'string' ? parsed.value.body : '',
          state: 'open',
          labels,
          comments: [],
        };
        repo.nextNumber += 1;
        repo.issues.set(issue.number, issue);
        repo.version += 1;
        sendJson(res, 201, issueJson(repo, issue));
        return;
      }
    }
    const number = Number.parseInt(rest[1] ?? '', 10);
    const issue = Number.isInteger(number) ? repo.issues.get(number) : undefined;
    if (rest.length === 2) {
      if (!issue) {
        sendError(res, 404, 'Not Found');
        return;
      }
      if (method === 'GET') {
        sendJson(res, 200, issueJson(repo, issue));
        return;
      }
      if (method === 'PATCH') {
        const parsed = parseBody(raw);
        if (!parsed.ok) {
          sendError(res, 400, 'Problems parsing JSON');
          return;
        }
        if (typeof parsed.value.title === 'string') issue.title = parsed.value.title;
        if (typeof parsed.value.body === 'string') issue.body = parsed.value.body;
        if (parsed.value.state === 'open' || parsed.value.state === 'closed') issue.state = parsed.value.state;
        if (parsed.value.labels !== undefined) {
          const labels = labelNamesOf(parsed.value.labels);
          for (const name of labels) {
            if (!repo.labels.has(name)) {
              sendError(res, 422, `Validation Failed: label '${name}' does not exist`);
              return;
            }
          }
          issue.labels = labels;
        }
        repo.version += 1;
        sendJson(res, 200, issueJson(repo, issue));
        return;
      }
    }
    if (rest.length === 3 && rest[2] === 'comments') {
      if (!issue) {
        sendError(res, 404, 'Not Found');
        return;
      }
      if (method === 'GET') {
        sendJson(res, 200, issue.comments.map((comment) => commentJson(repo, issue, comment)));
        return;
      }
      if (method === 'POST') {
        const parsed = parseBody(raw);
        if (!parsed.ok) {
          sendError(res, 400, 'Problems parsing JSON');
          return;
        }
        const comment: CommentRec = {
          id: repo.nextCommentId,
          body: typeof parsed.value.body === 'string' ? parsed.value.body : '',
        };
        repo.nextCommentId += 1;
        issue.comments.push(comment);
        repo.version += 1;
        sendJson(res, 201, commentJson(repo, issue, comment));
        return;
      }
    }
    sendError(res, 404, 'Not Found');
    return;
  }

  // Pull requests.
  if (rest[0] === 'pulls') {
    if (rest.length === 1) {
      if (method === 'GET') {
        const state = query.get('state') ?? 'open';
        let list = [...repo.pulls.values()];
        if (state === 'open') list = list.filter((pull) => pull.state === 'open');
        else if (state === 'closed') list = list.filter((pull) => pull.state === 'closed');
        list.sort((a, b) => a.number - b.number);
        const { page, headers } = paginate(req, query, list.map((pull) => pullJson(repo, pull)));
        sendJson(res, 200, page, headers);
        return;
      }
      if (method === 'POST') {
        const parsed = parseBody(raw);
        if (!parsed.ok) {
          sendError(res, 400, 'Problems parsing JSON');
          return;
        }
        const cleanRef = (value: unknown): string => {
          if (typeof value !== 'string') return '';
          const colon = value.indexOf(':');
          return colon >= 0 ? value.slice(colon + 1) : value;
        };
        const head = cleanRef(parsed.value.head);
        const base = cleanRef(parsed.value.base);
        const headTip = repo.branchTip(head);
        const baseTip = repo.branchTip(base);
        if (!headTip) {
          sendError(res, 422, 'Validation Failed: head is invalid');
          return;
        }
        if (!baseTip) {
          sendError(res, 422, 'Validation Failed: base is invalid');
          return;
        }
        const pull: PullRec = {
          number: repo.nextNumber,
          title: typeof parsed.value.title === 'string' ? parsed.value.title : '',
          body: typeof parsed.value.body === 'string' ? parsed.value.body : '',
          head,
          base,
          baseShaAtCreate: baseTip,
          state: 'open',
          merged: false,
          mergedAt: null,
          mergeCommitSha: null,
        };
        repo.nextNumber += 1;
        repo.pulls.set(pull.number, pull);
        repo.version += 1;
        sendJson(res, 201, pullJson(repo, pull));
        return;
      }
    }
    const number = Number.parseInt(rest[1] ?? '', 10);
    const pull = Number.isInteger(number) ? repo.pulls.get(number) : undefined;
    if (rest.length === 2 && method === 'GET') {
      if (!pull) {
        sendError(res, 404, 'Not Found');
        return;
      }
      sendJson(res, 200, pullJson(repo, pull));
      return;
    }
    if (rest.length === 3 && rest[2] === 'files' && method === 'GET') {
      if (!pull) {
        sendError(res, 404, 'Not Found');
        return;
      }
      sendJson(res, 200, pullChanges(repo, pull).map((change) => pullFileJson(repo, change)));
      return;
    }
    if (rest.length === 3 && rest[2] === 'merge' && method === 'PUT') {
      if (!pull) {
        sendError(res, 404, 'Not Found');
        return;
      }
      try {
        const sha = mergePull(repo, pull);
        sendJson(res, 200, { sha, merged: true, message: 'Pull Request successfully merged' });
      } catch (err) {
        if (err instanceof MergeConflictError) {
          sendError(res, 405, 'Pull Request is not mergeable');
          return;
        }
        throw err;
      }
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }

  // Contents API.
  if (rest[0] === 'contents') {
    routeContents(req, res, repo, rest.slice(1).join('/'), query, raw);
    return;
  }

  // Git data: refs.
  if (rest[0] === 'git' && rest[1] === 'refs') {
    if (rest.length === 2) {
      if (method === 'POST') {
        const parsed = parseBody(raw);
        if (!parsed.ok) {
          sendError(res, 400, 'Problems parsing JSON');
          return;
        }
        const ref = typeof parsed.value.ref === 'string' ? parsed.value.ref : '';
        const sha = typeof parsed.value.sha === 'string' ? parsed.value.sha.toLowerCase() : '';
        const object = repo.objects.get(sha);
        if (!ref.startsWith('refs/') || !object || (object.type !== 'commit' && object.type !== 'tag')) {
          sendError(res, 422, 'Validation Failed: ref or sha is invalid');
          return;
        }
        if (repo.refs.has(ref)) {
          sendError(res, 422, 'Reference already exists');
          return;
        }
        const uow = new UnitOfWork(repo);
        uow.moveRef(ref, sha);
        uow.commit();
        sendJson(res, 201, { ref, node_id: globalId('Ref', `${repo.id}:${ref}`), object: { sha, type: object.type } });
        return;
      }
      if (method === 'GET') {
        sendJson(
          res,
          200,
          sortedRefNames(repo).map((ref) => ({ ref, object: { sha: repo.refs.get(ref) } })),
        );
        return;
      }
    }
    if (rest.length >= 3 && method === 'GET') {
      const ref = `refs/${rest.slice(2).join('/')}`;
      const sha = repo.refs.get(ref);
      if (!sha) {
        sendError(res, 404, 'Not Found');
        return;
      }
      const object = repo.objects.get(sha);
      sendJson(res, 200, { ref, node_id: globalId('Ref', `${repo.id}:${ref}`), object: { sha, type: object?.type ?? 'commit' } });
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
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
      const name = rest.slice(1).join('/');
      const sha = repo.branchTip(name);
      if (!sha) {
        sendError(res, 404, 'Not Found');
        return;
      }
      sendJson(res, 200, { name, commit: { sha }, protected: false });
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }

  // Commits.
  if (rest[0] === 'commits') {
    if (rest.length === 1 && method === 'GET') {
      const start = resolveCommit(repo, query.get('sha'));
      if (!start) {
        sendJson(res, 200, []);
        return;
      }
      const ordered: string[] = [];
      const seen = new Set<string>();
      const stack: string[] = [start];
      while (stack.length > 0) {
        const current = stack.pop() as string;
        if (seen.has(current)) continue;
        seen.add(current);
        ordered.push(current);
        const object = repo.objects.get(current);
        if (!object || object.type !== 'commit') continue;
        const parents = parseCommit(object.data).parents;
        for (let i = parents.length - 1; i >= 0; i -= 1) stack.push(parents[i]);
      }
      const { page, headers } = paginate(req, query, ordered.map((oid) => commitJson(repo, oid)));
      sendJson(res, 200, page, headers);
      return;
    }
    if (rest.length === 2 && method === 'GET') {
      const oid = rest[1].toLowerCase();
      const object = repo.objects.get(oid);
      if (!object || object.type !== 'commit') {
        sendError(res, 404, 'Not Found');
        return;
      }
      sendJson(res, 200, commitJson(repo, oid));
      return;
    }
    sendError(res, 404, 'Not Found');
    return;
  }

  sendError(res, 404, 'Not Found');
}

/** The contents API: files and directory listings backed by tree objects. */
function routeContents(req: IncomingMessage, res: ServerResponse, repo: Repository, path: string, query: URLSearchParams, raw: Buffer): void {
  const method = req.method ?? 'GET';
  const cleanPath = path.replace(/^\/+|\/+$/g, '');

  if (method === 'GET') {
    const commitOid = resolveCommit(repo, query.get('ref'));
    if (!commitOid) {
      sendError(res, 404, 'Not Found');
      return;
    }
    const commit = repo.objects.get(commitOid);
    if (!commit || commit.type !== 'commit') {
      sendError(res, 404, 'Not Found');
      return;
    }
    let treeOid = parseCommit(commit.data).tree;
    if (cleanPath === '') {
      sendContentsListing(res, repo, treeOid, '');
      return;
    }
    const segments = cleanPath.split('/');
    for (let i = 0; i < segments.length; i += 1) {
      const tree = repo.objects.get(treeOid);
      if (!tree || tree.type !== 'tree') {
        sendError(res, 404, 'Not Found');
        return;
      }
      const entry = parseTree(tree.data).find((candidate) => candidate.name === segments[i]);
      if (!entry) {
        sendError(res, 404, 'Not Found');
        return;
      }
      if (i === segments.length - 1) {
        if (entry.mode === '40000') {
          sendContentsListing(res, repo, entry.oid, cleanPath);
          return;
        }
        const blob = repo.objects.get(entry.oid);
        if (!blob) {
          sendError(res, 404, 'Not Found');
          return;
        }
        sendJson(res, 200, {
          type: 'file',
          encoding: 'base64',
          content: blob.data.toString('base64'),
          name: entry.name,
          path: cleanPath,
          sha: entry.oid,
          size: blob.data.length,
        });
        return;
      }
      if (entry.mode !== '40000') {
        sendError(res, 404, 'Not Found');
        return;
      }
      treeOid = entry.oid;
    }
    sendError(res, 404, 'Not Found');
    return;
  }

  if (method === 'PUT' || method === 'DELETE') {
    const parsed = parseBody(raw);
    if (!parsed.ok) {
      sendError(res, 400, 'Problems parsing JSON');
      return;
    }
    const branch = typeof parsed.value.branch === 'string' && parsed.value.branch !== '' ? parsed.value.branch : repo.defaultBranch;
    const message = typeof parsed.value.message === 'string' ? parsed.value.message : `${method === 'PUT' ? 'Update' : 'Delete'} ${cleanPath}`;
    const uow = new UnitOfWork(repo);
    const sink = sinkOf(uow, repo);
    let tip = uow.refValue(`refs/heads/${branch}`);
    if (!tip && branch !== repo.defaultBranch) tip = uow.refValue(`refs/heads/${repo.defaultBranch}`);
    const files = filesAtCommit(sink, tip);
    const existing = files.get(cleanPath);

    if (method === 'DELETE') {
      if (!existing) {
        sendError(res, 404, 'Not Found');
        return;
      }
      if (typeof parsed.value.sha === 'string' && parsed.value.sha.toLowerCase() !== existing.oid) {
        sendError(res, 409, 'Conflict: the file sha does not match');
        return;
      }
      files.delete(cleanPath);
      const tree = stageTreeFromFiles(sink, files);
      const sha = stageCommit(sink, tree, tip ? [tip] : [], message);
      uow.moveRef(`refs/heads/${branch}`, sha);
      uow.commit();
      sendJson(res, 200, { content: null, commit: { sha, message } });
      return;
    }

    // PUT: create or update one file as a single commit.
    if (existing && typeof parsed.value.sha === 'string' && parsed.value.sha.toLowerCase() !== existing.oid) {
      sendError(res, 409, 'Conflict: the file sha does not match');
      return;
    }
    const content = typeof parsed.value.content === 'string' ? b64DecodeBuffer(parsed.value.content) : Buffer.alloc(0);
    const blobOid = sink.stage('blob', content);
    files.set(cleanPath, { mode: '100644', name: cleanPath.split('/').pop() ?? cleanPath, oid: blobOid });
    const tree = stageTreeFromFiles(sink, files);
    const sha = stageCommit(sink, tree, tip ? [tip] : [], message);
    uow.moveRef(`refs/heads/${branch}`, sha);
    uow.commit();
    sendJson(res, existing ? 200 : 201, {
      content: {
        type: 'file',
        encoding: 'base64',
        name: cleanPath.split('/').pop() ?? cleanPath,
        path: cleanPath,
        sha: blobOid,
        size: content.length,
      },
      commit: { sha, message },
    });
    return;
  }

  sendError(res, 404, 'Not Found');
}

function sendContentsListing(res: ServerResponse, repo: Repository, treeOid: string, prefix: string): void {
  const tree = repo.objects.get(treeOid);
  if (!tree || tree.type !== 'tree') {
    sendError(res, 404, 'Not Found');
    return;
  }
  const entries = parseTree(tree.data).map((entry) => {
    const object = repo.objects.get(entry.oid);
    return {
      type: entry.mode === '40000' ? 'dir' : 'file',
      name: entry.name,
      path: prefix === '' ? entry.name : `${prefix}/${entry.name}`,
      sha: entry.oid,
      size: object && object.type === 'blob' ? object.data.length : 0,
    };
  });
  sendJson(res, 200, entries);
}

// ---------------------------------------------------------------------------
// GraphQL v4: a small parser for the documents gh and github-mcp-server send
// ---------------------------------------------------------------------------

type GValue =
  | { k: 'var'; name: string }
  | { k: 'str'; v: string }
  | { k: 'num'; v: number }
  | { k: 'word'; v: string }
  | { k: 'bool'; v: boolean }
  | { k: 'null' }
  | { k: 'list'; v: GValue[] }
  | { k: 'obj'; v: Array<[string, GValue]> };

interface GField {
  name: string;
  alias: string | null;
  args: Array<[string, GValue]>;
  selection: GField[] | null;
  fragmentType: string | null;
  spread: string | null;
}

interface GOperation {
  opType: 'query' | 'mutation';
  name: string | null;
  selection: GField[];
}

interface GDocument {
  operations: GOperation[];
  fragments: Map<string, { typeCondition: string; selection: GField[] }>;
}

function tokenizeGraphQL(source: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < source.length) {
    const ch = source[i];
    if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === ',' || ch === '﻿') {
      i += 1;
      continue;
    }
    if (ch === '#') {
      while (i < source.length && source[i] !== '\n') i += 1;
      continue;
    }
    if (ch === '.' && source.slice(i, i + 3) === '...') {
      tokens.push('...');
      i += 3;
      continue;
    }
    if ('{}()[]:$!@=|&'.includes(ch)) {
      tokens.push(ch);
      i += 1;
      continue;
    }
    if (ch === '"') {
      if (source.slice(i, i + 3) === '"""') {
        const end = source.indexOf('"""', i + 3);
        const text = end < 0 ? source.slice(i + 3) : source.slice(i + 3, end);
        tokens.push(`"${text.replace(/\\/g, '\\\\').replace(/"/g, '\\"')}"`);
        i = end < 0 ? source.length : end + 3;
        continue;
      }
      let j = i + 1;
      let text = '';
      while (j < source.length && source[j] !== '"') {
        if (source[j] === '\\' && j + 1 < source.length) {
          const esc = source[j + 1];
          if (esc === 'u') {
            text += String.fromCharCode(Number.parseInt(source.slice(j + 2, j + 6), 16));
            j += 6;
          } else {
            text += { n: '\n', t: '\t', r: '\r', b: '\b', f: '\f', '/': '/', '\\': '\\', '"': '"' }[esc] ?? esc;
            j += 2;
          }
        } else {
          text += source[j];
          j += 1;
        }
      }
      tokens.push(`"${text.replace(/\\/g, '\\\\').replace(/"/g, '\\"')}"`);
      i = j + 1;
      continue;
    }
    const nameMatch = /^[_A-Za-z][_0-9A-Za-z]*/.exec(source.slice(i));
    if (nameMatch) {
      tokens.push(nameMatch[0]);
      i += nameMatch[0].length;
      continue;
    }
    const numMatch = /^-?\d+(\.\d+)?([eE][+-]?\d+)?/.exec(source.slice(i));
    if (numMatch) {
      tokens.push(numMatch[0]);
      i += numMatch[0].length;
      continue;
    }
    throw new Error(`unexpected character ${JSON.stringify(ch)} in GraphQL document`);
  }
  return tokens;
}

class GParser {
  private pos = 0;
  private readonly tokens: string[];

  constructor(tokens: string[]) {
    this.tokens = tokens;
  }

  private peek(): string | undefined {
    return this.tokens[this.pos];
  }

  private next(): string {
    const token = this.tokens[this.pos];
    this.pos += 1;
    if (token === undefined) throw new Error('unexpected end of GraphQL document');
    return token;
  }

  private expect(token: string): void {
    const got = this.next();
    if (got !== token) throw new Error(`expected ${token}, found ${got}`);
  }

  /** Skip a balanced (...) group (variable definitions, directive arguments). */
  private skipParens(): void {
    this.expect('(');
    let depth = 1;
    while (depth > 0) {
      const token = this.next();
      if (token === '(') depth += 1;
      else if (token === ')') depth -= 1;
    }
  }

  private skipDirectives(): void {
    while (this.peek() === '@') {
      this.next();
      this.next();
      if (this.peek() === '(') this.skipParens();
    }
  }

  parseDocument(): GDocument {
    const operations: GOperation[] = [];
    const fragments = new Map<string, { typeCondition: string; selection: GField[] }>();
    while (this.pos < this.tokens.length) {
      const head = this.peek();
      if (head === '{') {
        operations.push({ opType: 'query', name: null, selection: this.parseSelectionSet() });
      } else if (head === 'query' || head === 'mutation' || head === 'subscription') {
        const opType = this.next() === 'mutation' ? 'mutation' : 'query';
        let name: string | null = null;
        const maybeName = this.peek();
        if (maybeName !== undefined && maybeName !== '(' && maybeName !== '{' && maybeName !== '@') name = this.next();
        if (this.peek() === '(') this.skipParens();
        this.skipDirectives();
        operations.push({ opType, name, selection: this.parseSelectionSet() });
      } else if (head === 'fragment') {
        this.next();
        const fragName = this.next();
        this.expect('on');
        const typeCondition = this.next();
        this.skipDirectives();
        fragments.set(fragName, { typeCondition, selection: this.parseSelectionSet() });
      } else {
        throw new Error(`unexpected token ${head} in GraphQL document`);
      }
    }
    return { operations, fragments };
  }

  private parseSelectionSet(): GField[] {
    this.expect('{');
    const fields: GField[] = [];
    while (this.peek() !== '}') fields.push(this.parseField());
    this.expect('}');
    return fields;
  }

  private parseField(): GField {
    if (this.peek() === '...') {
      this.next();
      if (this.peek() === 'on') {
        this.next();
        const typeCondition = this.next();
        this.skipDirectives();
        return { name: '', alias: null, args: [], selection: this.parseSelectionSet(), fragmentType: typeCondition, spread: null };
      }
      const spread = this.next();
      this.skipDirectives();
      return { name: '', alias: null, args: [], selection: null, fragmentType: null, spread };
    }
    let name = this.next();
    let alias: string | null = null;
    if (this.peek() === ':') {
      this.next();
      alias = name;
      name = this.next();
    }
    const args: Array<[string, GValue]> = [];
    if (this.peek() === '(') {
      this.next();
      while (this.peek() !== ')') {
        const argName = this.next();
        this.expect(':');
        args.push([argName, this.parseValue()]);
      }
      this.expect(')');
    }
    this.skipDirectives();
    let selection: GField[] | null = null;
    if (this.peek() === '{') selection = this.parseSelectionSet();
    return { name, alias, args, selection, fragmentType: null, spread: null };
  }

  private parseValue(): GValue {
    const token = this.next();
    if (token === '$') return { k: 'var', name: this.next() };
    if (token.startsWith('"')) return { k: 'str', v: JSON.parse(token) as string };
    if (token === '[') {
      const items: GValue[] = [];
      while (this.peek() !== ']') items.push(this.parseValue());
      this.expect(']');
      return { k: 'list', v: items };
    }
    if (token === '{') {
      const entries: Array<[string, GValue]> = [];
      while (this.peek() !== '}') {
        const key = this.next();
        this.expect(':');
        entries.push([key, this.parseValue()]);
      }
      this.expect('}');
      return { k: 'obj', v: entries };
    }
    if (token === 'true') return { k: 'bool', v: true };
    if (token === 'false') return { k: 'bool', v: false };
    if (token === 'null') return { k: 'null' };
    if (/^-?\d/.test(token)) return { k: 'num', v: Number(token) };
    return { k: 'word', v: token };
  }
}

function evalGValue(value: GValue, variables: Json): unknown {
  switch (value.k) {
    case 'var':
      return variables[value.name] ?? null;
    case 'str':
      return value.v;
    case 'num':
      return value.v;
    case 'word':
      return value.v;
    case 'bool':
      return value.v;
    case 'null':
      return null;
    case 'list':
      return value.v.map((item) => evalGValue(item, variables));
    case 'obj': {
      const out: Json = {};
      for (const [key, item] of value.v) out[key] = evalGValue(item, variables);
      return out;
    }
  }
}

// ---------------------------------------------------------------------------
// GraphQL v4: schema tables the introspection probes read
// ---------------------------------------------------------------------------

const TYPE_FIELDS: Readonly<Record<string, readonly string[]>> = {
  Query: ['viewer', 'repository', 'node', 'nodes', 'search', 'user', 'organization', 'rateLimit', '__type', '__schema'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment', 'updateIssue', 'reopenIssue', 'addPullRequestReview'],
  User: ['id', 'login', 'name', 'email', 'url', 'databaseId', 'avatarUrl', 'createdAt', 'updatedAt'],
  Repository: [
    'id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled',
    'issue', 'issues', 'pullRequest', 'pullRequests', 'description', 'isPrivate', 'url', 'createdAt', 'updatedAt',
    'primaryLanguage', 'stargazerCount', 'forkCount', 'isFork', 'parent', 'labels', 'collaborators',
  ],
  Issue: [
    'id', 'databaseId', 'number', 'title', 'titleHTML', 'state', 'body', 'bodyText', 'url', 'createdAt', 'updatedAt',
    'closedAt', 'author', 'labels', 'comments', 'repository', 'reactions', 'assignees', 'milestone',
  ],
  PullRequest: [
    'id', 'databaseId', 'number', 'title', 'body', 'state', 'merged', 'mergedAt', 'mergeable', 'headRefName',
    'baseRefName', 'headRef', 'baseRef', 'files', 'url', 'createdAt', 'updatedAt', 'author', 'repository',
    'mergeCommit', 'additions', 'deletions', 'changedFiles', 'commits', 'reviews', 'comments', 'labels', 'isDraft', 'closed', 'locked',
  ],
  IssueComment: ['id', 'databaseId', 'body', 'bodyText', 'createdAt', 'updatedAt', 'author', 'url', 'issue', 'repository'],
  Label: ['id', 'name', 'color', 'description', 'url'],
  Ref: ['id', 'name', 'prefix', 'target', 'repository'],
  Commit: ['id', 'oid', 'message', 'messageHeadline', 'tree', 'parents', 'author', 'committer', 'committedDate', 'url', 'additions', 'deletions'],
  Tree: ['id', 'oid', 'entries'],
  TreeEntry: ['name', 'path', 'oid', 'type', 'mode'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'],
  IssueConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  IssueEdge: ['node', 'cursor'],
  PullRequestConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestEdge: ['node', 'cursor'],
  PullRequestChangedFileConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  PullRequestChangedFile: ['path', 'additions', 'deletions', 'changeType'],
  LabelConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  IssueCommentConnection: ['nodes', 'edges', 'pageInfo', 'totalCount'],
  SearchResultItemConnection: ['nodes', 'edges', 'pageInfo', 'totalCount', 'issueCount', 'repositoryCount', 'userCount', 'codeCount', 'discussionCount'],
  CreateIssuePayload: ['clientMutationId', 'issue', 'actor'],
  CloseIssuePayload: ['clientMutationId', 'issue', 'actor'],
  CreatePullRequestPayload: ['clientMutationId', 'pullRequest', 'actor'],
  MergePullRequestPayload: ['clientMutationId', 'pullRequest', 'actor'],
  AddCommentPayload: ['clientMutationId', 'commentEdge', 'subject', 'actor'],
  CommentEdge: ['node', 'cursor'],
  __Type: ['name', 'kind', 'description', 'fields', 'enumValues', 'possibleTypes', 'inputFields', 'ofType', 'specifiedByURL', 'isOneOf'],
  __Field: ['name', 'description', 'args', 'type', 'isDeprecated', 'deprecationReason'],
  __EnumValue: ['name', 'description', 'isDeprecated', 'deprecationReason'],
  __InputValue: ['name', 'description', 'type', 'defaultValue', 'isDeprecated', 'deprecationReason'],
  __Schema: ['types', 'queryType', 'mutationType', 'subscriptionType', 'directives', 'description'],
  __Directive: ['name', 'description', 'locations', 'args', 'isRepeatable'],
  RateLimit: ['cost', 'limit', 'remaining', 'resetAt', 'used', 'nodeCount'],
};

const TYPE_ENUMS: Readonly<Record<string, readonly string[]>> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION', 'CODE', 'COMMIT'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  PullRequestMergeMethod: ['MERGE', 'SQUASH', 'REBASE'],
  RepositoryPermission: ['ADMIN', 'MAINTAIN', 'WRITE', 'TRIAGE', 'READ'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  OrderDirection: ['ASC', 'DESC'],
  PullRequestOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
  IssueOrderField2: ['CREATED_AT'],
  DefaultRepositoryVisibility: ['PUBLIC', 'PRIVATE'],
  StatusState: ['EXPECTED', 'ERROR', 'FAILURE', 'PENDING', 'SUCCESS'],
};

// ---------------------------------------------------------------------------
// GraphQL v4: the executor
// ---------------------------------------------------------------------------

interface GObj {
  __type: string;
  value: unknown;
}

function wrap(type: string, value: unknown): GObj {
  return { __type: type, value };
}

function isGObj(value: unknown): value is GObj {
  return isRecord(value) && typeof value.__type === 'string' && 'value' in value;
}

interface GContext {
  variables: Json;
  fragments: Map<string, { typeCondition: string; selection: GField[] }>;
  errors: Array<{ message: string }>;
}

function cursorFor(number: number): string {
  return Buffer.from(`cursor:${number}`, 'utf8').toString('base64');
}

function numberFromCursor(cursor: unknown): number | null {
  if (typeof cursor !== 'string' || cursor === '') return null;
  try {
    const text = Buffer.from(cursor, 'base64').toString('utf8');
    const match = /^cursor:(\d+)$/.exec(text);
    return match ? Number.parseInt(match[1], 10) : null;
  } catch {
    return null;
  }
}

interface Connection {
  total: number;
  numbers: number[];
  hasNextPage: boolean;
  endCursor: string | null;
}

/** Apply states/orderBy/first/after to a numbered list, GitHub-style. */
function pageOf(items: Array<{ number: number }>, args: Json, states: string[] | null, stateOf: (item: { number: number }) => string): Connection & { items: Array<{ number: number }> } {
  let list = items;
  if (states) list = list.filter((item) => states.includes(stateOf(item)));
  const orderBy = isRecord(args.orderBy) ? args.orderBy : null;
  const direction = orderBy && typeof orderBy.direction === 'string' ? orderBy.direction : null;
  list = [...list].sort((a, b) => (direction === 'DESC' ? b.number - a.number : a.number - b.number));
  const total = list.length;
  const afterNumber = numberFromCursor(args.after);
  if (afterNumber !== null) {
    const index = list.findIndex((item) => item.number === afterNumber);
    if (index >= 0) list = list.slice(index + 1);
  }
  const first = typeof args.first === 'number' && Number.isFinite(args.first) ? Math.max(0, Math.trunc(args.first)) : list.length;
  const taken = list.slice(0, first);
  return {
    items: taken,
    total,
    numbers: taken.map((item) => item.number),
    hasNextPage: list.length > taken.length,
    endCursor: taken.length > 0 ? cursorFor(taken[taken.length - 1].number) : null,
  };
}

function repoFromGlobalId(id: unknown): Repository | undefined {
  if (typeof id !== 'string') return undefined;
  const parsed = parseGlobalId(id);
  if (parsed && parsed.kind === 'Repository') return reposById.get(Number.parseInt(parsed.rest, 10));
  const numeric = Number.parseInt(id, 10);
  if (Number.isInteger(numeric)) return reposById.get(numeric);
  return undefined;
}

function issueFromGlobalId(id: unknown): { repo: Repository; issue: IssueRec } | undefined {
  if (typeof id !== 'string') return undefined;
  const parsed = parseGlobalId(id);
  if (!parsed || parsed.kind !== 'Issue') return undefined;
  const [repoId, number] = parsed.rest.split(':');
  const repo = reposById.get(Number.parseInt(repoId, 10));
  const issue = repo?.issues.get(Number.parseInt(number, 10));
  return repo && issue ? { repo, issue } : undefined;
}

function pullFromGlobalId(id: unknown): { repo: Repository; pull: PullRec } | undefined {
  if (typeof id !== 'string') return undefined;
  const parsed = parseGlobalId(id);
  if (!parsed || parsed.kind !== 'PullRequest') return undefined;
  const [repoId, number] = parsed.rest.split(':');
  const repo = reposById.get(Number.parseInt(repoId, 10));
  const pull = repo?.pulls.get(Number.parseInt(number, 10));
  return repo && pull ? { repo, pull } : undefined;
}

type Resolved = { v: unknown; unknown?: boolean };

function argsOf(field: GField, ctx: GContext): Json {
  const out: Json = {};
  for (const [key, value] of field.args) out[key] = evalGValue(value, ctx.variables);
  return out;
}

function resolveField(typeName: string, source: unknown, field: GField, ctx: GContext): Resolved {
  const name = field.name;
  const args = argsOf(field, ctx);
  const known = TYPE_FIELDS[typeName];
  if (known && !known.includes(name) && name !== '__typename' && name !== '__type' && name !== '__schema') {
    ctx.errors.push({ message: `Field '${name}' doesn't exist on type '${typeName}'` });
    return { v: null, unknown: true };
  }

  if (name === '__typename') return { v: typeName };
  if (name === '__type') {
    const typeNameArg = typeof args.name === 'string' ? args.name : '';
    if (TYPE_FIELDS[typeNameArg] || TYPE_ENUMS[typeNameArg]) return { v: wrap('__Type', { name: typeNameArg }) };
    return { v: null };
  }
  if (name === '__schema') return { v: wrap('__Schema', {}) };

  switch (typeName) {
    case 'Query': {
      if (name === 'viewer') return { v: wrap('User', { login: LOGIN }) };
      if (name === 'repository') {
        const repo = typeof args.name === 'string' ? findRepository(typeof args.owner === 'string' ? args.owner : '', args.name) : undefined;
        return { v: repo ? wrap('Repository', repo) : null };
      }
      if (name === 'node') {
        const parsed = typeof args.id === 'string' ? parseGlobalId(args.id) : null;
        if (!parsed) return { v: null };
        if (parsed.kind === 'Repository') {
          const repo = reposById.get(Number.parseInt(parsed.rest, 10));
          return { v: repo ? wrap('Repository', repo) : null };
        }
        if (parsed.kind === 'Issue') {
          const found = issueFromGlobalId(args.id as string);
          return { v: found ? wrap('Issue', found) : null };
        }
        if (parsed.kind === 'PullRequest') {
          const found = pullFromGlobalId(args.id as string);
          return { v: found ? wrap('PullRequest', found) : null };
        }
        if (parsed.kind === 'User') return { v: wrap('User', { login: LOGIN }) };
        return { v: null };
      }
      if (name === 'user') return { v: wrap('User', { login: typeof args.login === 'string' ? args.login : LOGIN }) };
      if (name === 'search') return { v: wrap('SearchResultItemConnection', { items: [] as unknown[] }) };
      if (name === 'rateLimit') return { v: wrap('RateLimit', {}) };
      break;
    }
    case 'Mutation': {
      if (name === 'createIssue') {
        const input = isRecord(args.input) ? args.input : {};
        const repo = repoFromGlobalId(input.repositoryId);
        if (!repo) {
          ctx.errors.push({ message: 'Could not resolve the repository for createIssue' });
          return { v: wrap('CreateIssuePayload', { issue: null }) };
        }
        const issue: IssueRec = {
          number: repo.nextNumber,
          title: typeof input.title === 'string' ? input.title : '',
          body: typeof input.body === 'string' ? input.body : '',
          state: 'open',
          labels: [],
          comments: [],
        };
        repo.nextNumber += 1;
        repo.issues.set(issue.number, issue);
        repo.version += 1;
        return { v: wrap('CreateIssuePayload', { issue: wrap('Issue', { repo, issue }) }) };
      }
      if (name === 'closeIssue') {
        const input = isRecord(args.input) ? args.input : {};
        const found = issueFromGlobalId(input.issueId);
        if (!found) {
          ctx.errors.push({ message: 'Could not resolve the issue for closeIssue' });
          return { v: wrap('CloseIssuePayload', { issue: null }) };
        }
        found.issue.state = 'closed';
        found.repo.version += 1;
        return { v: wrap('CloseIssuePayload', { issue: wrap('Issue', found) }) };
      }
      if (name === 'createPullRequest') {
        const input = isRecord(args.input) ? args.input : {};
        const repo = repoFromGlobalId(input.repositoryId);
        const head = typeof input.headRefName === 'string' ? input.headRefName : '';
        const base = typeof input.baseRefName === 'string' ? input.baseRefName : '';
        if (!repo || !repo.branchTip(head) || !repo.branchTip(base)) {
          ctx.errors.push({ message: 'Could not resolve the branches for createPullRequest' });
          return { v: wrap('CreatePullRequestPayload', { pullRequest: null }) };
        }
        const pull: PullRec = {
          number: repo.nextNumber,
          title: typeof input.title === 'string' ? input.title : '',
          body: typeof input.body === 'string' ? input.body : '',
          head,
          base,
          baseShaAtCreate: repo.branchTip(base) as string,
          state: 'open',
          merged: false,
          mergedAt: null,
          mergeCommitSha: null,
        };
        repo.nextNumber += 1;
        repo.pulls.set(pull.number, pull);
        repo.version += 1;
        return { v: wrap('CreatePullRequestPayload', { pullRequest: wrap('PullRequest', { repo, pull }) }) };
      }
      if (name === 'mergePullRequest') {
        const input = isRecord(args.input) ? args.input : {};
        const found = pullFromGlobalId(input.pullRequestId);
        if (!found) {
          ctx.errors.push({ message: 'Could not resolve the pull request for mergePullRequest' });
          return { v: wrap('MergePullRequestPayload', { pullRequest: null }) };
        }
        try {
          mergePull(found.repo, found.pull);
        } catch (err) {
          if (err instanceof MergeConflictError) ctx.errors.push({ message: 'Pull Request is not mergeable' });
          else throw err;
        }
        return { v: wrap('MergePullRequestPayload', { pullRequest: wrap('PullRequest', found) }) };
      }
      if (name === 'addComment') {
        const input = isRecord(args.input) ? args.input : {};
        const found = issueFromGlobalId(input.subjectId);
        if (!found) {
          ctx.errors.push({ message: 'Could not resolve the subject for addComment' });
          return { v: wrap('AddCommentPayload', { commentEdge: null }) };
        }
        const comment: CommentRec = {
          id: found.repo.nextCommentId,
          body: typeof input.body === 'string' ? input.body : '',
        };
        found.repo.nextCommentId += 1;
        found.issue.comments.push(comment);
        found.repo.version += 1;
        const node = wrap('IssueComment', { repo: found.repo, issue: found.issue, comment });
        return { v: wrap('AddCommentPayload', { commentEdge: wrap('CommentEdge', { node }) }) };
      }
      break;
    }
    case 'User': {
      const user = source as { login: string };
      if (name === 'login') return { v: user.login };
      if (name === 'id') return { v: globalId('User', String(USER_ID)) };
      if (name === 'databaseId') return { v: USER_ID };
      if (name === 'name') return { v: 'Ada Iversen' };
      if (name === 'email') return { v: `${LOGIN}@example.invalid` };
      if (name === 'url' || name === 'avatarUrl') return { v: '' };
      if (name === 'createdAt' || name === 'updatedAt') return { v: isoAt(0) };
      break;
    }
    case 'Repository': {
      const repo = source as Repository;
      switch (name) {
        case 'id':
          return { v: globalId('Repository', String(repo.id)) };
        case 'databaseId':
          return { v: repo.id };
        case 'name':
          return { v: repo.name };
        case 'nameWithOwner':
          return { v: `${LOGIN}/${repo.name}` };
        case 'owner':
          return { v: wrap('User', { login: LOGIN }) };
        case 'defaultBranchRef': {
          const tip = repo.branchTip(repo.defaultBranch);
          return { v: tip ? wrap('Ref', { repo, name: repo.defaultBranch }) : null };
        }
        case 'viewerPermission':
          return { v: 'ADMIN' };
        case 'hasIssuesEnabled':
          return { v: true };
        case 'description':
          return { v: repo.description };
        case 'isPrivate':
          return { v: repo.isPrivate };
        case 'url':
          return { v: `/${LOGIN}/${repo.name}` };
        case 'createdAt':
        case 'updatedAt':
          return { v: isoAt(repo.id) };
        case 'stargazerCount':
        case 'forkCount':
          return { v: 0 };
        case 'isFork':
          return { v: false };
        case 'parent':
          return { v: null };
        case 'primaryLanguage':
          return { v: null };
        case 'issue': {
          const issue = typeof args.number === 'number' ? repo.issues.get(args.number) : undefined;
          return { v: issue ? wrap('Issue', { repo, issue }) : null };
        }
        case 'issues': {
          const states = Array.isArray(args.states) ? (args.states as string[]) : null;
          const page = pageOf([...repo.issues.values()], args, states, (item) => {
            const issue = repo.issues.get(item.number);
            return issue ? issue.state.toUpperCase() : 'OPEN';
          });
          return { v: wrap('IssueConnection', { repo, page }) };
        }
        case 'pullRequest': {
          const pull = typeof args.number === 'number' ? repo.pulls.get(args.number) : undefined;
          return { v: pull ? wrap('PullRequest', { repo, pull }) : null };
        }
        case 'pullRequests': {
          const states = Array.isArray(args.states) ? (args.states as string[]) : null;
          const page = pageOf([...repo.pulls.values()], { ...args, orderBy: args.orderBy ?? { direction: 'DESC' } }, states, (item) => {
            const pull = repo.pulls.get(item.number);
            if (!pull) return 'OPEN';
            return pull.merged ? 'MERGED' : pull.state.toUpperCase();
          });
          return { v: wrap('PullRequestConnection', { repo, page }) };
        }
        case 'labels':
          return { v: wrap('LabelConnection', { repo, items: [...repo.labels.values()] }) };
        case 'collaborators':
          return { v: null };
      }
      break;
    }
    case 'Issue': {
      const { repo, issue } = source as { repo: Repository; issue: IssueRec };
      switch (name) {
        case 'id':
          return { v: globalId('Issue', `${repo.id}:${issue.number}`) };
        case 'databaseId':
          return { v: repo.id * 1_000_000 + issue.number };
        case 'number':
          return { v: issue.number };
        case 'title':
        case 'titleHTML':
          return { v: issue.title };
        case 'state':
          return { v: issue.state.toUpperCase() };
        case 'body':
        case 'bodyText':
          return { v: issue.body };
        case 'url':
          return { v: `/${LOGIN}/${repo.name}/issues/${issue.number}` };
        case 'createdAt':
        case 'updatedAt':
          return { v: isoAt(issue.number * 2) };
        case 'closedAt':
          return { v: issue.state === 'closed' ? isoAt(issue.number * 2 + 1) : null };
        case 'author':
          return { v: wrap('User', { login: LOGIN }) };
        case 'repository':
          return { v: wrap('Repository', repo) };
        case 'labels':
          return {
            v: wrap('LabelConnection', {
              repo,
              items: issue.labels.map((labelName) => repo.labels.get(labelName) ?? { name: labelName, color: 'ededed', description: '' }),
            }),
          };
        case 'comments':
          return { v: wrap('IssueCommentConnection', { repo, issue, items: issue.comments }) };
        case 'reactions':
        case 'assignees':
          return { v: wrap('IssueConnection', { repo, page: { items: [], total: 0, numbers: [], hasNextPage: false, endCursor: null } }) };
        case 'milestone':
          return { v: null };
      }
      break;
    }
    case 'PullRequest': {
      const { repo, pull } = source as { repo: Repository; pull: PullRec };
      switch (name) {
        case 'id':
          return { v: globalId('PullRequest', `${repo.id}:${pull.number}`) };
        case 'databaseId':
          return { v: repo.id * 1_000_000 + pull.number };
        case 'number':
          return { v: pull.number };
        case 'title':
          return { v: pull.title };
        case 'body':
          return { v: pull.body };
        case 'state':
          return { v: pull.merged ? 'MERGED' : pull.state.toUpperCase() };
        case 'merged':
          return { v: pull.merged };
        case 'mergedAt':
          return { v: pull.mergedAt };
        case 'mergeable':
          return { v: pull.state !== 'open' ? 'UNKNOWN' : pullConflicts(repo, pull) ? 'CONFLICTING' : 'MERGEABLE' };
        case 'headRefName':
          return { v: pull.head };
        case 'baseRefName':
          return { v: pull.base };
        case 'headRef':
          return { v: repo.branchTip(pull.head) ? wrap('Ref', { repo, name: pull.head }) : null };
        case 'baseRef':
          return { v: repo.branchTip(pull.base) ? wrap('Ref', { repo, name: pull.base }) : null };
        case 'files': {
          const changes = pullChanges(repo, pull);
          const first = typeof args.first === 'number' ? Math.max(0, Math.trunc(args.first)) : changes.length;
          return { v: wrap('PullRequestChangedFileConnection', { repo, pull, changes: changes.slice(0, first), total: changes.length }) };
        }
        case 'url':
          return { v: `/${LOGIN}/${repo.name}/pull/${pull.number}` };
        case 'createdAt':
        case 'updatedAt':
          return { v: isoAt(pull.number * 2) };
        case 'author':
          return { v: wrap('User', { login: LOGIN }) };
        case 'repository':
          return { v: wrap('Repository', repo) };
        case 'mergeCommit':
          return { v: pull.mergeCommitSha ? wrap('Commit', { repo, oid: pull.mergeCommitSha }) : null };
        case 'additions':
        case 'deletions':
        case 'changedFiles': {
          const changes = pullChanges(repo, pull);
          if (name === 'changedFiles') return { v: changes.length };
          let sum = 0;
          for (const change of changes) {
            sum += countLines(repo.objects.get((name === 'additions' ? change.newOid : change.oldOid) ?? '')?.data);
          }
          return { v: sum };
        }
        case 'isDraft':
        case 'closed':
          return { v: name === 'closed' ? pull.state === 'closed' : false };
        case 'locked':
          return { v: false };
        case 'commits':
        case 'reviews':
        case 'comments':
        case 'labels':
          return { v: wrap('LabelConnection', { repo, items: [] as LabelRec[] }) };
      }
      break;
    }
    case 'IssueComment': {
      const { repo, issue, comment } = source as { repo: Repository; issue: IssueRec; comment: CommentRec };
      switch (name) {
        case 'id':
          return { v: globalId('IssueComment', `${repo.id}:${issue.number}:${comment.id}`) };
        case 'databaseId':
          return { v: comment.id };
        case 'body':
        case 'bodyText':
          return { v: comment.body };
        case 'createdAt':
        case 'updatedAt':
          return { v: isoAt(comment.id * 3) };
        case 'author':
          return { v: wrap('User', { login: LOGIN }) };
        case 'url':
          return { v: `/${LOGIN}/${repo.name}/issues/${issue.number}#issuecomment-${comment.id}` };
        case 'issue':
          return { v: wrap('Issue', { repo, issue }) };
        case 'repository':
          return { v: wrap('Repository', repo) };
      }
      break;
    }
    case 'Label': {
      const label = source as LabelRec;
      if (name === 'id') return { v: globalId('Label', label.name) };
      if (name === 'name') return { v: label.name };
      if (name === 'color') return { v: label.color };
      if (name === 'description') return { v: label.description };
      if (name === 'url') return { v: '' };
      break;
    }
    case 'Ref': {
      const { repo, name: refName } = source as { repo: Repository; name: string };
      if (name === 'id') return { v: globalId('Ref', `${repo.id}:refs/heads/${refName}`) };
      if (name === 'name') return { v: refName };
      if (name === 'prefix') return { v: 'refs/heads/' };
      if (name === 'repository') return { v: wrap('Repository', repo) };
      if (name === 'target') {
        const tip = repo.branchTip(refName);
        return { v: tip ? wrap('Commit', { repo, oid: tip }) : null };
      }
      break;
    }
    case 'Commit': {
      const { repo, oid } = source as { repo: Repository; oid: string };
      const object = repo.objects.get(oid);
      const view = object && object.type === 'commit' ? parseCommit(object.data) : { tree: '', parents: [], message: '' };
      if (name === 'id') return { v: globalId('Commit', oid) };
      if (name === 'oid') return { v: oid };
      if (name === 'message' || name === 'messageHeadline') return { v: view.message.split('\n')[0] ?? '' };
      if (name === 'tree') return { v: wrap('Tree', { repo, oid: view.tree }) };
      if (name === 'parents') return { v: wrap('LabelConnection', { repo, items: [] as LabelRec[] }) };
      if (name === 'committedDate') return { v: isoAt(0) };
      if (name === 'url') return { v: `/${LOGIN}/${repo.name}/commit/${oid}` };
      if (name === 'additions' || name === 'deletions') return { v: 0 };
      if (name === 'author' || name === 'committer') return { v: wrap('User', { login: LOGIN }) };
      break;
    }
    case 'IssueConnection':
    case 'PullRequestConnection': {
      const { repo, page } = source as { repo: Repository; page: Connection & { items: Array<{ number: number }> } };
      const isIssue = typeName === 'IssueConnection';
      const nodes = page.items.map((item) =>
        isIssue
          ? wrap('Issue', { repo, issue: repo.issues.get(item.number) as IssueRec })
          : wrap('PullRequest', { repo, pull: repo.pulls.get(item.number) as PullRec }),
      );
      if (name === 'nodes') return { v: nodes };
      if (name === 'totalCount') return { v: page.total };
      if (name === 'pageInfo') {
        return {
          v: wrap('PageInfo', {
            hasNextPage: page.hasNextPage,
            hasPreviousPage: false,
            startCursor: page.numbers.length > 0 ? cursorFor(page.numbers[0]) : null,
            endCursor: page.endCursor,
          }),
        };
      }
      if (name === 'edges') {
        return {
          v: nodes.map((node, index) => wrap(isIssue ? 'IssueEdge' : 'PullRequestEdge', { node, cursor: cursorFor(page.numbers[index] ?? 0) })),
        };
      }
      break;
    }
    case 'PullRequestChangedFileConnection': {
      const { changes, total } = source as { changes: FileChange[]; total: number };
      if (name === 'nodes') return { v: changes.map((change) => wrap('PullRequestChangedFile', change)) };
      if (name === 'totalCount') return { v: total };
      if (name === 'pageInfo') return { v: wrap('PageInfo', { hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }) };
      if (name === 'edges') return { v: changes.map((change) => wrap('PullRequestEdge', { node: wrap('PullRequestChangedFile', change), cursor: '' })) };
      break;
    }
    case 'PullRequestChangedFile': {
      const change = source as FileChange;
      if (name === 'path') return { v: change.path };
      if (name === 'additions' || name === 'deletions') return { v: 0 };
      if (name === 'changeType') return { v: change.status.toUpperCase() };
      break;
    }
    case 'LabelConnection': {
      const { items } = source as { items: LabelRec[] };
      if (name === 'nodes') return { v: items.map((label) => wrap('Label', label)) };
      if (name === 'totalCount') return { v: items.length };
      if (name === 'pageInfo') return { v: wrap('PageInfo', { hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }) };
      if (name === 'edges') return { v: items.map((label) => wrap('IssueEdge', { node: wrap('Label', label), cursor: '' })) };
      break;
    }
    case 'IssueCommentConnection': {
      const { repo, issue, items } = source as { repo: Repository; issue: IssueRec; items: CommentRec[] };
      if (name === 'nodes') return { v: items.map((comment) => wrap('IssueComment', { repo, issue, comment })) };
      if (name === 'totalCount') return { v: items.length };
      if (name === 'pageInfo') return { v: wrap('PageInfo', { hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }) };
      if (name === 'edges') return { v: items.map((comment) => wrap('IssueEdge', { node: wrap('IssueComment', { repo, issue, comment }), cursor: '' })) };
      break;
    }
    case 'SearchResultItemConnection': {
      if (name === 'nodes' || name === 'edges') return { v: [] };
      if (name === 'pageInfo') return { v: wrap('PageInfo', { hasNextPage: false, hasPreviousPage: false, startCursor: null, endCursor: null }) };
      return { v: 0 };
    }
    case 'PageInfo': {
      const info = source as { hasNextPage: boolean; hasPreviousPage: boolean; startCursor: string | null; endCursor: string | null };
      if (name === 'hasNextPage') return { v: info.hasNextPage };
      if (name === 'hasPreviousPage') return { v: info.hasPreviousPage };
      if (name === 'startCursor') return { v: info.startCursor };
      if (name === 'endCursor') return { v: info.endCursor };
      break;
    }
    case 'CreateIssuePayload':
    case 'CloseIssuePayload': {
      const payload = source as { issue: GObj | null };
      if (name === 'issue') return { v: payload.issue };
      if (name === 'clientMutationId') return { v: null };
      if (name === 'actor') return { v: wrap('User', { login: LOGIN }) };
      break;
    }
    case 'CreatePullRequestPayload':
    case 'MergePullRequestPayload': {
      const payload = source as { pullRequest: GObj | null };
      if (name === 'pullRequest') return { v: payload.pullRequest };
      if (name === 'clientMutationId') return { v: null };
      if (name === 'actor') return { v: wrap('User', { login: LOGIN }) };
      break;
    }
    case 'AddCommentPayload': {
      const payload = source as { commentEdge: GObj | null };
      if (name === 'commentEdge') return { v: payload.commentEdge };
      if (name === 'clientMutationId') return { v: null };
      if (name === 'subject') return { v: null };
      if (name === 'actor') return { v: wrap('User', { login: LOGIN }) };
      break;
    }
    case 'CommentEdge': {
      const edge = source as { node: GObj };
      if (name === 'node') return { v: edge.node };
      if (name === 'cursor') return { v: cursorFor(0) };
      break;
    }
    case 'IssueEdge':
    case 'PullRequestEdge': {
      const edge = source as { node: unknown; cursor: string };
      if (name === 'node') return { v: edge.node };
      if (name === 'cursor') return { v: edge.cursor };
      break;
    }
    case '__Type': {
      const typeInfo = source as { name: string };
      if (name === 'name') return { v: typeInfo.name };
      if (name === 'kind') return { v: TYPE_ENUMS[typeInfo.name] ? 'ENUM' : 'OBJECT' };
      if (name === 'description') return { v: null };
      if (name === 'fields') {
        return { v: (TYPE_FIELDS[typeInfo.name] ?? []).map((fieldName) => wrap('__Field', { name: fieldName })) };
      }
      if (name === 'enumValues') {
        return { v: (TYPE_ENUMS[typeInfo.name] ?? []).map((enumName) => wrap('__EnumValue', { name: enumName })) };
      }
      if (name === 'possibleTypes' || name === 'inputFields') return { v: [] };
      if (name === 'ofType') return { v: null };
      if (name === 'specifiedByURL') return { v: null };
      if (name === 'isOneOf') return { v: false };
      break;
    }
    case '__Field': {
      const fieldInfo = source as { name: string };
      if (name === 'name') return { v: fieldInfo.name };
      if (name === 'description') return { v: null };
      if (name === 'args') return { v: [] };
      if (name === 'type') return { v: wrap('__Type', { name: 'String' }) };
      if (name === 'isDeprecated') return { v: false };
      if (name === 'deprecationReason') return { v: null };
      break;
    }
    case '__EnumValue': {
      const enumInfo = source as { name: string };
      if (name === 'name') return { v: enumInfo.name };
      if (name === 'description') return { v: null };
      if (name === 'isDeprecated') return { v: false };
      if (name === 'deprecationReason') return { v: null };
      break;
    }
    case '__Schema': {
      if (name === 'types') {
        return { v: [...Object.keys(TYPE_FIELDS), ...Object.keys(TYPE_ENUMS)].map((typeName) => wrap('__Type', { name: typeName })) };
      }
      if (name === 'queryType') return { v: wrap('__Type', { name: 'Query' }) };
      if (name === 'mutationType') return { v: wrap('__Type', { name: 'Mutation' }) };
      if (name === 'subscriptionType') return { v: null };
      if (name === 'directives') return { v: [] };
      if (name === 'description') return { v: null };
      break;
    }
    case 'RateLimit': {
      if (name === 'cost') return { v: 1 };
      if (name === 'limit') return { v: 5000 };
      if (name === 'remaining') return { v: 4999 };
      if (name === 'used') return { v: 1 };
      if (name === 'nodeCount') return { v: 0 };
      if (name === 'resetAt') return { v: isoAt(3600) };
      break;
    }
    case 'Tree': {
      const { repo, oid } = source as { repo: Repository; oid: string };
      if (name === 'id') return { v: globalId('Tree', oid) };
      if (name === 'oid') return { v: oid };
      if (name === 'entries') {
        const tree = repo.objects.get(oid);
        const entries = tree && tree.type === 'tree' ? parseTree(tree.data) : [];
        return { v: entries.map((entry) => wrap('TreeEntry', entry)) };
      }
      break;
    }
    case 'TreeEntry': {
      const entry = source as TreeEntry;
      if (name === 'name') return { v: entry.name };
      if (name === 'path') return { v: entry.name };
      if (name === 'oid') return { v: entry.oid };
      if (name === 'type') return { v: entry.mode === '40000' ? 'tree' : 'blob' };
      if (name === 'mode') return { v: Number.parseInt(entry.mode, 10) || 0 };
      break;
    }
  }

  // A field the schema tables do not list for this type.
  ctx.errors.push({ message: `Field '${name}' doesn't exist on type '${typeName}'` });
  return { v: null, unknown: true };
}

function execSelection(typeName: string, source: unknown, fields: GField[], ctx: GContext): Json {
  const out: Json = {};
  for (const field of fields) {
    if (field.spread) {
      const fragment = ctx.fragments.get(field.spread);
      if (fragment && (fragment.typeCondition === typeName || fragment.typeCondition === 'Node')) {
        Object.assign(out, execSelection(typeName, source, fragment.selection, ctx));
      }
      continue;
    }
    if (field.fragmentType) {
      if (field.fragmentType === typeName || (field.fragmentType === 'Node' && isGObj(source))) {
        Object.assign(out, execSelection(typeName, source, field.selection ?? [], ctx));
      }
      continue;
    }
    const key = field.alias ?? field.name;
    const resolved = resolveField(typeName, isGObj(source) ? source.value : source, field, ctx);
    if (resolved.unknown) {
      out[key] = null;
      continue;
    }
    out[key] = applySelection(resolved.v, field, ctx);
  }
  return out;
}

function applySelection(value: unknown, field: GField, ctx: GContext): unknown {
  if (!field.selection) {
    if (isGObj(value)) return null;
    return value ?? null;
  }
  if (value === null || value === undefined) return null;
  if (Array.isArray(value)) return value.map((item) => applySelection(item, field, ctx));
  if (isGObj(value)) return execSelection(value.__type, value, field.selection, ctx);
  return value;
}

function executeGraphQL(body: Json): Json {
  const query = typeof body.query === 'string' ? body.query : '';
  const variables = isRecord(body.variables) ? body.variables : {};
  const operationName = typeof body.operationName === 'string' ? body.operationName : null;
  let document: GDocument;
  try {
    document = new GParser(tokenizeGraphQL(query)).parseDocument();
  } catch (err) {
    return { data: null, errors: [{ message: err instanceof Error ? err.message : 'parse error' }] };
  }
  const operation = document.operations.find((candidate) => operationName === null || candidate.name === operationName) ?? document.operations[0];
  if (!operation) return { data: null, errors: [{ message: 'No operation in the document' }] };
  const ctx: GContext = { variables, fragments: document.fragments, errors: [] };
  const rootType = operation.opType === 'mutation' ? 'Mutation' : 'Query';
  const data = execSelection(rootType, wrap(rootType, null), operation.selection, ctx);
  const result: Json = { data };
  if (ctx.errors.length > 0) result.errors = ctx.errors;
  return result;
}

function handleGraphQL(req: IncomingMessage, res: ServerResponse, raw: Buffer): void {
  if (!isAuthed(req)) {
    sendError(res, 401, 'Unauthorized');
    return;
  }
  let body: unknown;
  try {
    body = JSON.parse(raw.toString('utf8')) as unknown;
  } catch {
    sendJson(res, 400, { errors: [{ message: 'Problems parsing JSON' }] });
    return;
  }
  if (Array.isArray(body)) {
    const results = body.map((entry) => executeGraphQL(isRecord(entry) ? entry : {}));
    sendJson(res, 200, results);
    return;
  }
  if (!isRecord(body)) {
    sendJson(res, 400, { errors: [{ message: 'Expected a JSON object' }] });
    return;
  }
  sendJson(res, 200, executeGraphQL(body));
}

// ---------------------------------------------------------------------------
// MCP: the six tools github-mcp-server drives, over streamable HTTP JSON-RPC
// ---------------------------------------------------------------------------

const MCP_TOOLS: Json[] = [
  {
    name: 'create_repo',
    description: 'Create a new repository for the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'Repository name' },
        description: { type: 'string', description: 'Repository description' },
        private: { type: 'boolean', description: 'Whether the repository is private' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get details of a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        full_name: { type: 'string', description: 'Full name in owner/repo form' },
      },
      required: [],
    },
  },
  {
    name: 'create_issue',
    description: 'Create a new issue in a repository.',
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
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository, newest first.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        state: { type: 'string', description: 'Filter by state: open or closed' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request between two branches.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Pull request title' },
        head: { type: 'string', description: 'Head branch name' },
        base: { type: 'string', description: 'Base branch name' },
        body: { type: 'string', description: 'Pull request body' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge an open pull request.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        pull_number: { type: 'number', description: 'Pull request number' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

const MCP_TOOL_NAMES: ReadonlySet<string> = new Set(MCP_TOOLS.map((tool) => (tool as { name: string }).name));

function mcpRepo(args: Json): Repository | undefined {
  let name = typeof args.repo === 'string' ? args.repo : '';
  const owner = typeof args.owner === 'string' ? args.owner : LOGIN;
  if (typeof args.full_name === 'string' && args.full_name.includes('/')) {
    const [fullOwner, fullRepo] = args.full_name.split('/', 2);
    if (name === '') name = fullRepo;
    return findRepository(fullOwner, name);
  }
  return findRepository(owner, name);
}

function mcpToolResult(payload: unknown): Json {
  const text = JSON.stringify(payload);
  return { content: [{ type: 'text', text }], structuredContent: payload as Json, isError: false };
}

function mcpToolError(message: string): Json {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function callMcpTool(name: string, args: Json): Json {
  switch (name) {
    case 'create_repo': {
      const repoName = typeof args.name === 'string' ? args.name : '';
      if (repoName === '') return mcpToolError('name is required');
      if (findRepository(LOGIN, repoName)) return mcpToolError(`Repository ${repoName} already exists`);
      const repo = createRepository(repoName, {
        description: typeof args.description === 'string' ? args.description : '',
        isPrivate: args.private === true,
      });
      return mcpToolResult(repoJson(repo));
    }
    case 'get_repo': {
      const repo = mcpRepo(args);
      if (!repo) return mcpToolError('Repository not found');
      return mcpToolResult(repoJson(repo));
    }
    case 'create_issue': {
      const repo = mcpRepo(args);
      if (!repo) return mcpToolError('Repository not found');
      const issue: IssueRec = {
        number: repo.nextNumber,
        title: typeof args.title === 'string' ? args.title : '',
        body: typeof args.body === 'string' ? args.body : '',
        state: 'open',
        labels: [],
        comments: [],
      };
      repo.nextNumber += 1;
      repo.issues.set(issue.number, issue);
      repo.version += 1;
      return mcpToolResult(issueJson(repo, issue));
    }
    case 'list_issues': {
      const repo = mcpRepo(args);
      if (!repo) return mcpToolError('Repository not found');
      const state = typeof args.state === 'string' ? args.state : null;
      const issues = [...repo.issues.values()]
        .filter((issue) => state === null || issue.state === state)
        .sort((a, b) => b.number - a.number)
        .map((issue) => issueJson(repo, issue));
      return mcpToolResult(issues);
    }
    case 'create_pull_request': {
      const repo = mcpRepo(args);
      if (!repo) return mcpToolError('Repository not found');
      const head = (typeof args.head === 'string' ? args.head : '').split(':').pop() as string;
      const base = (typeof args.base === 'string' ? args.base : '').split(':').pop() as string;
      const headTip = repo.branchTip(head);
      const baseTip = repo.branchTip(base);
      if (!headTip || !baseTip) return mcpToolError('head or base branch does not exist');
      const pull: PullRec = {
        number: repo.nextNumber,
        title: typeof args.title === 'string' ? args.title : '',
        body: typeof args.body === 'string' ? args.body : '',
        head,
        base,
        baseShaAtCreate: baseTip,
        state: 'open',
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
      };
      repo.nextNumber += 1;
      repo.pulls.set(pull.number, pull);
      repo.version += 1;
      return mcpToolResult(pullJson(repo, pull));
    }
    case 'merge_pull_request': {
      const repo = mcpRepo(args);
      if (!repo) return mcpToolError('Repository not found');
      const number = typeof args.pull_number === 'number' ? args.pull_number : Number.parseInt(String(args.pull_number ?? ''), 10);
      const pull = repo.pulls.get(number);
      if (!pull) return mcpToolError('Pull request not found');
      try {
        mergePull(repo, pull);
      } catch (err) {
        if (err instanceof MergeConflictError) return mcpToolError('Pull Request is not mergeable');
        throw err;
      }
      return mcpToolResult(pullJson(repo, pull));
    }
  }
  return mcpToolError(`Unknown tool: ${name}`);
}

function rpcResult(id: unknown, result: Json): Json {
  return { jsonrpc: '2.0', id: (id ?? null) as Json, result };
}

function rpcError(id: unknown, code: number, message: string): Json {
  return { jsonrpc: '2.0', id: (id ?? null) as Json, error: { code, message } };
}

const LEGACY_PROTOCOL_VERSIONS: ReadonlySet<string> = new Set(['2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05', '2024-10-07']);

function handleMcp(req: IncomingMessage, res: ServerResponse, raw: Buffer): void {
  const authorization = req.headers.authorization;
  if (typeof authorization !== 'string' || authorization === '') {
    sendError(res, 401, 'Unauthorized');
    return;
  }
  let body: unknown;
  try {
    body = JSON.parse(raw.toString('utf8')) as unknown;
  } catch {
    sendJson(res, 400, rpcError(null, -32700, 'Parse error'));
    return;
  }
  if (!isRecord(body) || typeof body.method !== 'string') {
    sendJson(res, 400, rpcError(null, -32600, 'Invalid Request'));
    return;
  }
  const method = body.method;
  const id = body.id;
  const params = isRecord(body.params) ? body.params : {};

  if (id === undefined || id === null) {
    // A notification: acknowledge with an empty 202 and no body.
    res.writeHead(202);
    res.end();
    return;
  }

  switch (method) {
    case 'server/discover': {
      sendJson(res, 200, rpcResult(id, {
        protocolVersions: ['2026-07-28'],
        supportedVersions: ['2026-07-28'],
        capabilities: { tools: {} },
        serverInfo: { name: 'uow-forge-mcp', version: '1.0.0' },
        instructions: 'GitHub-compatible forge tools: repositories, issues, pull requests.',
      }));
      return;
    }
    case 'initialize': {
      const requested = typeof params.protocolVersion === 'string' ? params.protocolVersion : '';
      const protocolVersion = LEGACY_PROTOCOL_VERSIONS.has(requested) ? requested : '2025-11-25';
      sendJson(res, 200, rpcResult(id, {
        protocolVersion,
        capabilities: { tools: {} },
        serverInfo: { name: 'uow-forge-mcp', version: '1.0.0' },
      }));
      return;
    }
    case 'tools/list': {
      sendJson(res, 200, rpcResult(id, { tools: MCP_TOOLS }));
      return;
    }
    case 'tools/call': {
      const toolName = typeof params.name === 'string' ? params.name : '';
      const toolArgs = isRecord(params.arguments) ? params.arguments : {};
      if (!MCP_TOOL_NAMES.has(toolName)) {
        sendJson(res, 200, rpcError(id, -32602, `Unknown tool: ${toolName}`));
        return;
      }
      const schema = MCP_TOOLS.find((tool) => (tool as { name: string }).name === toolName) as {
        inputSchema: { required?: string[] };
      };
      const required = schema.inputSchema.required ?? [];
      const missing = required.filter((key) => toolArgs[key] === undefined || toolArgs[key] === null || toolArgs[key] === '');
      if (missing.length > 0) {
        sendJson(res, 200, rpcError(id, -32602, `Missing required argument: ${missing.join(', ')}`));
        return;
      }
      sendJson(res, 200, rpcResult(id, callMcpTool(toolName, toolArgs)));
      return;
    }
    case 'ping': {
      sendJson(res, 200, rpcResult(id, {}));
      return;
    }
    default: {
      sendJson(res, 200, rpcError(id, -32601, `Method not found: ${method}`));
      return;
    }
  }
}

// ---------------------------------------------------------------------------
// The HTTP router
// ---------------------------------------------------------------------------

function decodeSegments(pathname: string): string[] {
  return pathname
    .split('/')
    .filter((segment) => segment !== '')
    .map((segment) => {
      try {
        return decodeURIComponent(segment);
      } catch {
        return segment;
      }
    });
}

export function createApp(): Server {
  const server = createServer((req, res) => {
    void (async () => {
      try {
        const raw = await readBody(req);
        const url = new URL(req.url ?? '/', 'http://localhost');
        const pathname = url.pathname;
        const method = req.method ?? 'GET';

        if (method === 'GET' && pathname === '/healthz') {
          sendJson(res, 200, { ok: true });
          return;
        }

        if (pathname === '/api/graphql') {
          if (method !== 'POST') {
            sendError(res, 405, 'Method Not Allowed');
            return;
          }
          handleGraphQL(req, res, raw);
          return;
        }

        if (pathname === '/mcp') {
          handleMcp(req, res, raw);
          return;
        }

        if (pathname === '/api/v3' || pathname.startsWith('/api/v3/')) {
          if (!isAuthed(req)) {
            sendError(res, 401, 'Unauthorized');
            return;
          }
          const segments = decodeSegments(pathname).slice(2);
          routeRest(req, res, segments, url.searchParams, raw);
          return;
        }

        const gitMatch = /^\/([^/]+)\/([^/]+)\.git\/(info\/refs|git-upload-pack|git-receive-pack)$/.exec(pathname);
        if (gitMatch) {
          const owner = decodeURIComponent(gitMatch[1]);
          const repoName = decodeURIComponent(gitMatch[2]);
          const repo = findRepository(owner, repoName);
          if (!repo) {
            sendError(res, 404, 'Not Found');
            return;
          }
          const action = gitMatch[3];
          if (action === 'info/refs' && method === 'GET') {
            const service = url.searchParams.get('service') ?? '';
            if (service !== 'git-upload-pack' && service !== 'git-receive-pack') {
              sendError(res, 400, 'Unsupported service');
              return;
            }
            handleInfoRefs(req, res, repo, service);
            return;
          }
          if (action === 'git-upload-pack' && method === 'POST') {
            handleUploadPack(res, repo, raw);
            return;
          }
          if (action === 'git-receive-pack' && method === 'POST') {
            handleReceivePack(res, repo, raw);
            return;
          }
          sendError(res, 404, 'Not Found');
          return;
        }

        sendError(res, 404, 'Not Found');
      } catch (err) {
        if (!res.headersSent) {
          sendError(res, 500, err instanceof Error ? err.message : 'Internal Server Error');
        } else {
          res.end();
        }
      }
    })();
  });
  return server;
}
