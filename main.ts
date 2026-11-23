// main.ts is mend, the CLI SPEC.md specifies, and this is the kit's starting point for it (MIT). It does all ten
// sections of SPEC.md: the command line, the output and exit codes, safe paths, format detection, matching lines at
// three tiers (section 5), unified diffs (section 6), SEARCH/REPLACE blocks (section 7), V4A patches (section 8),
// JSON edits (section 9) and the all-or-nothing write (section 10). Node 22, the standard library alone; run it as
// `node main.ts [options] [PATCH]`.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands over to runner.ts
// (the last lines below): keep that hand-over and runner.ts as they are, and write the CLI.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  /** Moves a move edit made, in the patch's order: the new path and the old path. */
  readonly moves: Array<{ nw: string; old: string }> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

// ---- section 3: a file as lines, its line break, and whether it ends with one ----

interface FileModel {
  lines: string[];
  br: '\n' | '\r\n';
  finalBreak: boolean;
}

function parseFile(text: string): FileModel {
  if (text === '') return { lines: [], br: '\n', finalBreak: false };
  const nl = text.indexOf('\n');
  const br: '\n' | '\r\n' = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const finalBreak = text.endsWith(br);
  if (finalBreak) parts.pop();
  return { lines: parts, br, finalBreak };
}

function writeFileText(m: FileModel): string {
  if (m.lines.length === 0) return '';
  return m.lines.join(m.br) + (m.finalBreak ? m.br : '');
}

// ---- section 5: matching lines ----

const leadingWs = (s: string): string => /^[ \t]*/.exec(s)![0];

function normLine(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return s.replace(/[ \t]+$/, '');
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

function lineMatch(a: string, b: string, tier: number): boolean {
  return normLine(a, tier) === normLine(b, tier);
}

function occurrences(lines: string[], o: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  for (let i = from; i + o.length <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (!lineMatch(lines[i + j]!, o[j]!, tier)) { ok = false; break; }
    }
    if (ok) out.push(i);
  }
  return out;
}

function tiers(strict: boolean): number[] {
  return strict ? [0] : [0, 1, 2];
}

/** The first tier with an occurrence of O at or after `from` that `pred` accepts, and its occurrences. */
function findOccurrences(lines: string[], o: string[], strict: boolean, from: number, pred: (start: number) => boolean): { tier: number; occs: number[] } | null {
  for (const tier of tiers(strict)) {
    const occs = occurrences(lines, o, tier, from).filter(pred);
    if (occs.length > 0) return { tier, occs };
  }
  return null;
}

/** The first line at or after `from` equal to `anchor` at the first tier where one is. */
function findAnchor(lines: string[], anchor: string, strict: boolean, from: number): number | null {
  for (const tier of tiers(strict)) {
    for (let i = from; i < lines.length; i++) {
      if (lineMatch(lines[i]!, anchor, tier)) return i;
    }
  }
  return null;
}

interface BodyLine {
  kind: 'ctx' | 'old' | 'new' | 'backslash';
  text: string;
}

/** O and N of a hunk or chunk body, and which lines of N are context lines (with their index in O). */
function bodyON(body: BodyLine[]): { o: string[]; n: string[]; ctx: Map<number, number> } {
  const o: string[] = [];
  const n: string[] = [];
  const ctx = new Map<number, number>();
  for (const bl of body) {
    if (bl.kind === 'ctx') { ctx.set(n.length, o.length); o.push(bl.text); n.push(bl.text); }
    else if (bl.kind === 'old') o.push(bl.text);
    else if (bl.kind === 'new') n.push(bl.text);
  }
  return { o, n, ctx };
}

/** Whether a `\` line follows the body's last context or `+` line. */
function bodyNoEol(body: BodyLine[]): boolean {
  let last = -1;
  for (let i = 0; i < body.length; i++) {
    if (body[i]!.kind === 'ctx' || body[i]!.kind === 'new') last = i;
  }
  return last >= 0 && body[last + 1]?.kind === 'backslash';
}

/** The lines N writes when it replaces O at `at`, with section 5's context and tier-2 rules. */
function replacement(lines: string[], at: number, o: string[], n: string[], ctx: Map<number, number>, tier: number): string[] {
  const f = leadingWs(lines[at] ?? '');
  const p = leadingWs(o[0] ?? '');
  const out: string[] = [];
  for (let j = 0; j < n.length; j++) {
    if (ctx.has(j)) out.push(lines[at + ctx.get(j)!]!);
    else if (tier === 2) {
      const l = n[j]!;
      out.push(l !== '' && l.trim() !== '' && l.startsWith(p) ? f + l.slice(p.length) : l);
    } else out.push(n[j]!);
  }
  return out;
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---- section 6: unified diffs ----

interface Hunk {
  a: number;
  body: BodyLine[];
}

interface UniSection {
  oldPath: string | null | undefined;
  newPath: string | null | undefined;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  gitOld: string | undefined;
  gitNew: string | undefined;
  newFile: boolean;
  deletedFile: boolean;
  hunks: Hunk[];
}

/** A path of a `---`/`+++` line: the text after the four characters, up to the first tab, trimmed; null is /dev/null. */
function patchPath(raw: string): string | null {
  let p = raw.split('\t')[0]!.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

function bodyLine(l: string): BodyLine {
  if (l === '') return { kind: 'ctx', text: '' };
  if (l[0] === ' ') return { kind: 'ctx', text: l.slice(1) };
  if (l[0] === '-') return { kind: 'old', text: l.slice(1) };
  if (l[0] === '+') return { kind: 'new', text: l.slice(1) };
  return { kind: 'backslash', text: l.slice(1) };
}

const HUNK_HEAD = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;

/** Parse one section starting at `start`; return the index after it. */
function parseUniSection(lines: string[], start: number, sec: UniSection): number {
  let i = start;
  const n = lines.length;
  let inHeader = true;
  if (lines[i]!.startsWith('diff --git ')) i++;
  while (i < n) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) break;
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (!inHeader) break;
      sec.oldPath = patchPath(line.slice(4));
      sec.newPath = patchPath(lines[i + 1]!.slice(4));
      i += 2;
      continue;
    }
    if (inHeader && line.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
    if (inHeader && line.startsWith('+++ ')) {
      sec.newPath = patchPath(line.slice(4));
      i++;
      continue;
    }
    const hm = HUNK_HEAD.exec(line);
    if (hm) {
      inHeader = false;
      const hunk: Hunk = { a: parseInt(hm[1]!, 10), body: [] };
      i++;
      while (i < n) {
        const bl = lines[i]!;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\') || bl === '') {
          hunk.body.push(bodyLine(bl));
          i++;
        } else break;
      }
      while (hunk.body.length > 0) {
        const lastB = hunk.body[hunk.body.length - 1]!;
        if (lastB.kind === 'ctx' && lastB.text === '') hunk.body.pop();
        else break;
      }
      sec.hunks.push(hunk);
      continue;
    }
    if (line.startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
    if (inHeader) {
      if (line.startsWith('rename from ')) sec.renameFrom = line.slice('rename from '.length).trim();
      else if (line.startsWith('rename to ')) sec.renameTo = line.slice('rename to '.length).trim();
      else if (line.startsWith('new file mode')) sec.newFile = true;
      else if (line.startsWith('deleted file mode')) sec.deletedFile = true;
      i++;
      continue;
    }
    i++;
  }
  return i;
}

function applyHunks(m: FileModel, hunks: Hunk[], strict: boolean, path: string): void {
  let d = 0;
  for (const hunk of hunks) {
    const { o, n, ctx } = bodyON(hunk.body);
    const noEol = bodyNoEol(hunk.body);
    if (o.length === 0) {
      let idx = hunk.a + d;
      if (idx < 0) idx = 0;
      if (idx > m.lines.length) idx = m.lines.length;
      const atEnd = idx === m.lines.length;
      m.lines.splice(idx, 0, ...n);
      if (atEnd) m.finalBreak = !noEol;
      d += n.length;
      continue;
    }
    const found = findOccurrences(m.lines, o, strict, 0, () => true);
    if (!found) throw new Fail('no-match', path);
    const target = hunk.a - 1 + d;
    let best = found.occs[0]!;
    let bestDist = Math.abs(best - target);
    for (const pos of found.occs) {
      const dist = Math.abs(pos - target);
      if (dist < bestDist) { best = pos; bestDist = dist; }
    }
    const atEnd = best + o.length === m.lines.length;
    const repl = replacement(m.lines, best, o, n, ctx, found.tier);
    m.lines.splice(best, o.length, ...repl);
    if (atEnd) m.finalBreak = !noEol;
    d += n.length - o.length;
  }
}

function unifiedSectionEdit(sec: UniSection, strict: boolean): Edit {
  return (tree) => {
    let oldP: string | null | undefined = sec.oldPath !== undefined ? sec.oldPath : sec.renameFrom !== undefined ? sec.renameFrom : sec.gitOld;
    let newP: string | null | undefined = sec.newPath !== undefined ? sec.newPath : sec.renameTo !== undefined ? sec.renameTo : sec.gitNew;
    if (oldP === undefined) oldP = newP;
    if (newP === undefined) newP = oldP;
    if (oldP === undefined || newP === undefined) throw new Fail('unsafe', '');
    if (oldP !== null && !safe(oldP)) throw new Fail('unsafe', oldP);
    if (newP !== null && !safe(newP)) throw new Fail('unsafe', newP);
    if (oldP === null || sec.newFile) {
      const np = newP!;
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const plusLines: string[] = [];
      let lastPlus: { hunk: Hunk; idx: number } | null = null;
      for (const hunk of sec.hunks) {
        hunk.body.forEach((bl, bi) => {
          if (bl.kind === 'new') { plusLines.push(bl.text); lastPlus = { hunk, idx: bi }; }
        });
      }
      const finalBreak = lastPlus === null ? true : lastPlus.hunk.body[lastPlus.idx + 1]?.kind !== 'backslash';
      tree.now.set(np, plusLines.length === 0 ? '' : plusLines.join('\n') + (finalBreak ? '\n' : ''));
      return;
    }
    if (newP === null || sec.deletedFile) {
      const op = oldP!;
      if (tree.get(op) === null) throw new Fail('missing', op);
      tree.now.set(op, null);
      return;
    }
    if (oldP !== newP) {
      const op = oldP!;
      const np = newP!;
      const text = tree.get(op);
      if (text === null) throw new Fail('missing', op);
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const m = parseFile(text);
      applyHunks(m, sec.hunks, strict, op);
      tree.now.set(np, writeFileText(m));
      tree.now.set(op, null);
      tree.moves.push({ nw: np, old: op });
      return;
    }
    const op = oldP!;
    const text = tree.get(op);
    if (text === null) throw new Fail('missing', op);
    const m = parseFile(text);
    applyHunks(m, sec.hunks, strict, op);
    tree.now.set(op, writeFileText(m));
  };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections: UniSection[] = [];
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)$/.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const sec: UniSection = { oldPath: undefined, newPath: undefined, renameFrom: undefined, renameTo: undefined, gitOld: m[1], gitNew: m[2], newFile: false, deletedFile: false, hunks: [] };
      sections.push(sec);
      i = parseUniSection(lines, i, sec);
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      const sec: UniSection = { oldPath: undefined, newPath: undefined, renameFrom: undefined, renameTo: undefined, gitOld: undefined, gitNew: undefined, newFile: false, deletedFile: false, hunks: [] };
      sections.push(sec);
      i = parseUniSection(lines, i, sec);
      continue;
    }
    if (line.startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
    i++;
  }
  return sections.map((sec) => unifiedSectionEdit(sec, strict));
}

// ---- section 7: SEARCH/REPLACE blocks ----

function srEdit(path: string, oldLines: string[], newLines: string[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (oldLines.length === 0) {
      if (tree.get(path) !== null) throw new Fail('exists', path);
      tree.now.set(path, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
      return;
    }
    const text = tree.get(path);
    if (text === null) throw new Fail('missing', path);
    const m = parseFile(text);
    const found = findOccurrences(m.lines, oldLines, strict, 0, () => true);
    if (!found) throw new Fail('no-match', path);
    if (found.occs.length > 1) throw new Fail('ambiguous', path);
    const at = found.occs[0]!;
    const repl = replacement(m.lines, at, oldLines, newLines, new Map(), found.tier);
    m.lines.splice(at, oldLines.length, ...repl);
    tree.now.set(path, writeFileText(m));
  };
}

function srEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') { i++; continue; }
    const searchIdx = i;
    let eqIdx = -1;
    for (let j = i + 1; j < n; j++) {
      if (lines[j]!.trimEnd() === '=======') { eqIdx = j; break; }
    }
    let repIdx = -1;
    if (eqIdx >= 0) {
      for (let j = eqIdx + 1; j < n; j++) {
        if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') { repIdx = j; break; }
      }
    }
    if (eqIdx < 0 || repIdx < 0) throw new Exit2(`error: parse ${searchIdx + 1}`);
    let path: string | null = null;
    for (let j = searchIdx - 1; j > prevEnd; j--) {
      const t = lines[j]!;
      if (blank(t)) continue;
      if (t.trim().startsWith('```')) continue;
      path = t.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${searchIdx + 1}`);
      path = prevPath;
    }
    edits.push(srEdit(path, lines.slice(searchIdx + 1, eqIdx), lines.slice(eqIdx + 1, repIdx), strict));
    prevPath = path;
    prevEnd = repIdx;
    i = repIdx + 1;
  }
  return edits;
}

// ---- section 8: V4A patches ----

interface VChunk {
  anchor: string | null;
  eof: boolean;
  body: BodyLine[];
}

function v4aAddEdit(path: string, fileLines: string[]): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) !== null) throw new Fail('exists', path);
    tree.now.set(path, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
  };
}

function v4aDeleteEdit(path: string): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (tree.get(path) === null) throw new Fail('missing', path);
    tree.now.set(path, null);
  };
}

function v4aUpdateEdit(path: string, moveTo: string | null, chunks: VChunk[], strict: boolean): Edit {
  return (tree) => {
    if (!safe(path)) throw new Fail('unsafe', path);
    if (moveTo !== null && !safe(moveTo)) throw new Fail('unsafe', moveTo);
    const text = tree.get(path);
    if (text === null) throw new Fail('missing', path);
    if (moveTo !== null && tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
    const m = parseFile(text);
    let cursor = 0;
    for (const chunk of chunks) {
      if (chunk.anchor !== null) {
        const at = findAnchor(m.lines, chunk.anchor, strict, cursor);
        if (at === null) throw new Fail('no-match', path);
        cursor = at + 1;
      }
      const { o, n, ctx } = bodyON(chunk.body);
      if (o.length === 0) {
        const idx = chunk.eof ? m.lines.length : cursor;
        m.lines.splice(idx, 0, ...n);
        cursor = idx + n.length;
        continue;
      }
      const found = findOccurrences(m.lines, o, strict, cursor, (s) => !chunk.eof || s + o.length === m.lines.length);
      if (!found) throw new Fail('no-match', path);
      const at = found.occs[0]!;
      const repl = replacement(m.lines, at, o, n, ctx, found.tier);
      m.lines.splice(at, o.length, ...repl);
      cursor = at + repl.length;
    }
    const out = writeFileText(m);
    if (moveTo !== null) {
      tree.now.set(moveTo, out);
      tree.now.set(path, null);
      tree.moves.push({ nw: moveTo, old: path });
    } else {
      tree.now.set(path, out);
    }
  };
}

/** Collect a section's lines from `start` until a new section or `last`; drop trailing blank lines. */
function collectVSection(lines: string[], start: number, last: number): { body: string[]; next: number } {
  let end = start;
  while (end < last) {
    const l = lines[end]!;
    if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ')) break;
    end++;
  }
  const body = lines.slice(start, end);
  while (body.length > 0 && blank(body[body.length - 1]!)) body.pop();
  return { body, next: end };
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i]!)) { last = i; break; }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) { i++; continue; }
    if (line.startsWith('*** Add File: ')) {
      const path = line.slice('*** Add File: '.length).trim();
      const { body, next } = collectVSection(lines, i + 1, last);
      const fileLines: string[] = [];
      for (let k = 0; k < body.length; k++) {
        const bl = body[k]!;
        if (bl === '') fileLines.push('');
        else if (bl.startsWith('+')) fileLines.push(bl.slice(1));
        else throw new Exit2(`error: parse ${i + 2 + k}`);
      }
      edits.push(v4aAddEdit(path, fileLines));
      i = next;
      continue;
    }
    if (line.startsWith('*** Delete File: ')) {
      const path = line.slice('*** Delete File: '.length).trim();
      const { body, next } = collectVSection(lines, i + 1, last);
      for (let k = 0; k < body.length; k++) {
        if (!blank(body[k]!)) throw new Exit2(`error: parse ${i + 2 + k}`);
      }
      edits.push(v4aDeleteEdit(path));
      i = next;
      continue;
    }
    if (line.startsWith('*** Update File: ')) {
      const path = line.slice('*** Update File: '.length).trim();
      const { body, next } = collectVSection(lines, i + 1, last);
      const updateLineNo = i + 1;
      const bodyStartLine = i + 2;
      let moveTo: string | null = null;
      let idx = 0;
      if (body.length > 0 && body[0]!.startsWith('*** Move to: ')) {
        moveTo = body[0]!.slice('*** Move to: '.length).trim();
        idx = 1;
      }
      const chunks: VChunk[] = [];
      let cur: VChunk | null = null;
      while (idx < body.length) {
        const bl = body[idx]!;
        const lineNo = bodyStartLine + idx;
        if (bl.startsWith('@@')) {
          if (cur) chunks.push(cur);
          const anchorText = bl.slice(2).trim();
          cur = { anchor: anchorText === '' ? null : anchorText, eof: false, body: [] };
          idx++;
          continue;
        }
        if (bl === '*** End of File') {
          if (!cur) throw new Exit2(`error: parse ${lineNo}`);
          cur.eof = true;
          chunks.push(cur);
          cur = null;
          idx++;
          continue;
        }
        if (bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl === '') {
          if (!cur) cur = { anchor: null, eof: false, body: [] };
          cur.body.push(bodyLine(bl));
          idx++;
          continue;
        }
        throw new Exit2(`error: parse ${lineNo}`);
      }
      if (cur) chunks.push(cur);
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateLineNo}`);
      edits.push(v4aUpdateEdit(path, moveTo, chunks, strict));
      i = next;
      continue;
    }
    throw new Exit2(`error: parse ${i + 1}`);
  }
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits = kind === 'json' ? jsonEdits(text, lines) : kind === 'unified' ? unifiedEdits(lines, strict) : kind === 'search-replace' ? srEdits(lines, strict) : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: Array<{ key: string; line: string }> = [];
  const movedOld = new Set<string>();
  const movedNew = new Set<string>();
  for (const mv of tree.moves) {
    const wasOld = tree.original(mv.old);
    const wasNew = tree.original(mv.nw);
    const nowOld = tree.now.get(mv.old);
    const nowNew = tree.now.get(mv.nw);
    if (wasOld !== null && nowOld === null && wasNew === null && nowNew !== null) {
      rows.push({ key: mv.nw, line: `R ${mv.old} -> ${mv.nw}` });
      movedOld.add(mv.old);
      movedNew.add(mv.nw);
    }
  }
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    if (movedOld.has(p) || movedNew.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const p of [...tree.now.keys()]) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
