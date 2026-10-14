#!/usr/bin/env node
'use strict';
/*
 * mlc.js  —  迷你 ML (OCaml 風格)  ->  LBC v1 中間碼
 *
 * 用法:  node mlc.js prog.ml [-o prog.lbc]     產生 prog.lbc，用 vm.js / vm2wasm.js 執行
 *        node mlc.js prog.ml --types           只做型別檢查，並印出每個頂層定義的型別
 *        node mlc.js prog.ml --scheme          印出中間產物 (Scheme 核心)
 *        node mlc.js prog.ml --no-check        略過型別檢查
 *
 * 編譯流程:  ML --(lexer/parser)--> AST --(Hindley-Milner 型別推論)--> --(gen)--> Scheme 核心 --(lispc.js)--> LBC
 *
 * ────────────── 支援的語言 ──────────────
 *  運算式   let / let rec / and / in、fun、function、match … with (含 when 守衛)、if、tuple、list [a; b]、
 *           (e : t)、begin…end、序列 e1; e2、while / for、record {x = 1; y = 2} / {r with x = 3} / r.x
 *  樣式     變數 _ 字面值 tuple [] [a; b] h :: t Constructor (p, q) {x = p} p as x p1 | p2 (p : t)
 *  型別     type 'a t = A | B of 'a * int | …、record、type alias、型別推論 (let 多型 + value restriction)
 *  運算子   + - * / mod、+. -. *. /.、^、@、::、= <> < > <= >= ==、&& ||、:=、!、|>、@@ (可自訂運算子)
 *  函式庫   List.* Option.* String.length/concat、print_string/int/float/endline、string_of_*、ref、
 *           Printf.printf / sprintf (%d %s %f %.2f %b %5d %-5s %05d %%)，皆以 ML 寫成 (見 PRELUDE)
 *
 * ────────────── 執行期資料表示 ──────────────
 *  int/float = 數字    bool = #t/#f    string = 字串    unit = ()
 *  tuple = list        list = list     variant: C a b = (C a b)，無參數 C = (C)
 *  record = 欄位值的 list (依宣告順序)   ref = 以 closure 封裝的可變格
 *
 * ────────────── 與真正 OCaml 的差異 ──────────────
 *  - 沒有 module / functor / open、沒有 exception / try (用 failwith)、沒有 array、沒有 char
 *  - 沒有 labeled / optional 參數、沒有 GADT / 多型變體 / object、record 欄位不可 mutable (請用 ref)
 *  - 數字是 JS 的 double: int 超過 2^53 會失準；int 與 float 在執行期不分
 *  - < > <= >= 與 compare 只支援數字 (VM 無字串比較)；= 則是完整的結構相等
 */
const fs = require('fs');
const lispc = require('./lispc.js');

class MLError extends Error {}
const fail = (line, msg) => { throw new MLError(line ? `第 ${line} 行: ${msg}` : msg); };

/* ═════════════════════════ Lexer ═════════════════════════ */
const MODULES = new Set(['List', 'String', 'Option', 'Printf', 'Fun', 'Int', 'Float', 'Bool']);
const KEYWORDS = new Set(['let', 'rec', 'and', 'in', 'fun', 'function', 'match', 'with', 'if', 'then', 'else', 'type', 'of',
  'begin', 'end', 'true', 'false', 'mod', 'external', 'when', 'as', 'while', 'for', 'do', 'done', 'to', 'downto',
  'open', 'module', 'try', 'exception', 'mutable', 'lazy', 'class', 'object', 'functor', 'sig', 'struct']);
const UNSUPPORTED_KW = new Set(['open', 'module', 'try', 'exception', 'mutable', 'lazy', 'class', 'object', 'functor', 'sig', 'struct']);
const OPCH = '!$%&*+-./:<=>?@^|~';

function lex(src) {
  const toks = []; let i = 0, line = 1; const n = src.length;
  const push = (k, v) => toks.push({ k, v, line });
  while (i < n) {
    const c = src[i];
    if (c === '\n') { line++; i++; continue; }
    if (/\s/.test(c)) { i++; continue; }
    if (c === '(' && src[i + 1] === '*') {                          // 巢狀註解 (* ... *)
      let depth = 1; i += 2; const startLine = line;
      while (i < n && depth > 0) {
        if (src[i] === '\n') line++;
        if (src[i] === '(' && src[i + 1] === '*') { depth++; i += 2; }
        else if (src[i] === '*' && src[i + 1] === ')') { depth--; i += 2; }
        else i++;
      }
      if (depth > 0) fail(startLine, '註解沒有結尾');
      continue;
    }
    if (c === '"') {
      let s = ''; i++; const startLine = line;
      while (i < n && src[i] !== '"') {
        if (src[i] === '\\') {
          i++; const e = src[i];
          s += e === 'n' ? '\n' : e === 't' ? '\t' : e === 'r' ? '\r' : e === 'b' ? '\b' : e === '0' ? '\0' : e;
        } else { if (src[i] === '\n') line++; s += src[i]; }
        i++;
      }
      if (i >= n) fail(startLine, '字串沒有結尾的引號');
      i++; push('str', s); continue;
    }
    let m;
    if (/[0-9]/.test(c)) {
      m = /^\d[\d_]*(\.[\d_]*)?([eE][+-]?\d+)?/.exec(src.slice(i));
      const text = m[0].replace(/_/g, '');
      push(/[.eE]/.test(text) ? 'float' : 'int', Number(text)); i += m[0].length; continue;
    }
    if (c === "'") {
      m = /^'([a-z_][A-Za-z0-9_']*)/.exec(src.slice(i));
      if (m && !m[0].endsWith("'") && src[i + m[0].length] !== "'") { push('tyvar', m[1]); i += m[0].length; continue; }
      fail(line, '不支援 char 字面值');
    }
    if (/[A-Za-z_]/.test(c)) {
      const w = /^[A-Za-z_][A-Za-z0-9_']*/.exec(src.slice(i))[0];
      i += w.length;
      if (w === '_') { push('op', '_'); continue; }
      if (/[A-Z]/.test(w[0])) {
        if (MODULES.has(w) && src[i] === '.' && /[a-z_]/.test(src[i + 1] || '')) {
          const part = /^[a-z_][A-Za-z0-9_']*/.exec(src.slice(i + 1))[0];
          i += 1 + part.length; push('id', w + '.' + part);
        } else push('cid', w);
      } else if (KEYWORDS.has(w)) push('kw', w);
      else push('id', w);
      continue;
    }
    if (c === ';') { if (src[i + 1] === ';') { push('op', ';;'); i += 2; } else { push('op', ';'); i++; } continue; }
    if ('()[]{},'.includes(c)) { push('op', c); i++; continue; }
    if (OPCH.includes(c)) {
      let j = i; while (j < n && OPCH.includes(src[j])) j++;
      let run = src.slice(i, j);
      if (run.length > 1 && run[0] === '=' && '-!'.includes(run[1])) run = '=';       // x =-1  /  x =!r
      push('op', run); i += run.length; continue;
    }
    fail(line, `無法辨識的字元 "${c}"`);
  }
  push('eof', null);
  return toks;
}

/* ═════════════════════════ Parser ═════════════════════════ */
const E = (t, line, o) => Object.assign({ t, line }, o);
const lit = (kind, v, line) => E('lit', line, { kind, v });
const UNIT_LIT = line => lit('unit', null, line);

// 運算子優先序 (低 -> 高)
function opLevel(op) {
  if (op === '||' || op === 'or') return 0;
  if (op === '&&' || op === '&') return 1;
  if (op === '!=' || '=<>|&$'.includes(op[0])) return 2;
  if (op[0] === '@' || op[0] === '^') return 3;
  if (op === '::') return 4;
  if (op[0] === '+' || op[0] === '-') return 5;
  if (op === 'mod' || '*/%'.includes(op[0])) return 6;
  if (op.startsWith('**')) return 7;
  return -1;
}
const RIGHT_ASSOC = new Set([3, 4, 7]);

class Parser {
  constructor(toks) { this.t = toks; this.p = 0; }
  peek(k = 0) { return this.t[Math.min(this.p + k, this.t.length - 1)]; }
  next() { return this.t[this.p++]; }
  isOp(v, k = 0) { const t = this.peek(k); return t.k === 'op' && t.v === v; }
  isKw(v, k = 0) { const t = this.peek(k); return t.k === 'kw' && t.v === v; }
  describe(t) { return t.k === 'eof' ? '檔案結尾' : t.k === 'str' ? '字串' : `"${t.v}"`; }
  err(msg) { const t = this.peek(); fail(t.line, `${msg} (遇到 ${this.describe(t)})`); }
  expectOp(v) { if (!this.isOp(v)) this.err(`語法錯誤: 需要 "${v}"`); return this.next(); }
  expectKw(v) { if (!this.isKw(v)) this.err(`語法錯誤: 需要 "${v}"`); return this.next(); }
  expectId() { const t = this.peek(); if (t.k !== 'id') this.err('語法錯誤: 需要識別字'); return this.next().v; }

  /* ── 頂層 ── */
  parseProgram() {
    const items = [];
    while (this.peek().k !== 'eof') {
      if (this.isOp(';;')) { this.next(); continue; }
      items.push(this.parseItem());
    }
    return items;
  }

  parseItem() {
    const t = this.peek();
    if (t.k === 'kw' && UNSUPPORTED_KW.has(t.v)) fail(t.line, `不支援 "${t.v}"`);
    if (this.isKw('type')) return this.parseTypeDecl();
    if (this.isKw('external')) return this.parseExternal();
    if (this.isKw('let')) {
      const save = this.p; this.next();
      const rec = this.isKw('rec') ? (this.next(), true) : false;
      const binds = this.parseBindings();
      if (this.isKw('in')) { this.p = save; return { t: 'expr', line: t.line, e: this.parseSeq() }; }
      return { t: 'let', line: t.line, rec, binds };
    }
    return { t: 'expr', line: t.line, e: this.parseSeq() };
  }

  parseExternal() {
    const line = this.next().line;
    let name;
    if (this.isOp('(')) { this.next(); name = this.next().v; this.expectOp(')'); } else name = this.expectId();
    this.expectOp(':');
    const ty = this.parseType();
    this.expectOp('=');
    const s = this.next();
    if (s.k !== 'str') fail(s.line, 'external 需要字串');
    return { t: 'external', line, name, ty, cname: s.v };
  }

  /* ── 型別 ── */
  parseType() {
    const a = this.parseTupleType();
    if (this.isOp('->')) { this.next(); return { t: 'arrow', a, b: this.parseType() }; }
    return a;
  }
  parseTupleType() {
    const first = this.parseAppType();
    if (!this.isOp('*')) return first;
    const items = [first];
    while (this.isOp('*')) { this.next(); items.push(this.parseAppType()); }
    return { t: 'tuple', items };
  }
  parseAppType() {
    let ty = this.parseAtomType();
    while (this.peek().k === 'id') ty = { t: 'tname', name: this.next().v, args: [ty], line: this.peek().line };
    return ty;
  }
  parseAtomType() {
    const t = this.peek();
    if (t.k === 'tyvar') { this.next(); return { t: 'tyvar', name: t.v }; }
    if (t.k === 'id') { this.next(); return { t: 'tname', name: t.v, args: [], line: t.line }; }
    if (this.isOp('(')) {
      this.next();
      const items = [this.parseType()];
      while (this.isOp(',')) { this.next(); items.push(this.parseType()); }
      this.expectOp(')');
      if (items.length === 1) return items[0];
      const n = this.expectId();
      return { t: 'tname', name: n, args: items, line: t.line };
    }
    this.err('語法錯誤: 需要型別');
  }

  parseTypeDecl() {
    const line = this.next().line, defs = [];
    do {
      if (this.isKw('and')) this.next();
      const params = [];
      if (this.peek().k === 'tyvar') params.push(this.next().v);
      else if (this.isOp('(') && this.peek(1).k === 'tyvar') {
        this.next(); params.push(this.next().v);
        while (this.isOp(',')) { this.next(); params.push(this.next().v); }
        this.expectOp(')');
      }
      const name = this.expectId();
      this.expectOp('=');
      if (this.isOp('{')) {                                          // record
        this.next(); const fields = [];
        while (!this.isOp('}')) {
          if (this.isKw('mutable')) fail(this.peek().line, '不支援 mutable 欄位 (請用 ref)');
          const fname = this.expectId(); this.expectOp(':');
          fields.push({ name: fname, type: this.parseType() });
          if (this.isOp(';')) this.next(); else break;
        }
        this.expectOp('}');
        defs.push({ name, params, kind: 'record', fields, line });
      } else if (this.isOp('|') || this.peek().k === 'cid') {        // variant
        if (this.isOp('|')) this.next();
        const ctors = [];
        for (;;) {
          const c = this.next();
          if (c.k !== 'cid') fail(c.line, '需要建構子名稱 (大寫開頭)');
          const args = [];
          if (this.isKw('of')) { this.next(); args.push(this.parseAppType()); while (this.isOp('*')) { this.next(); args.push(this.parseAppType()); } }
          ctors.push({ name: c.v, args });
          if (this.isOp('|')) this.next(); else break;
        }
        defs.push({ name, params, kind: 'variant', ctors, line });
      } else defs.push({ name, params, kind: 'alias', type: this.parseType(), line });
    } while (this.isKw('and'));
    return { t: 'type', line, defs };
  }

  /* ── let 綁定 ── */
  startsPatAtom() {
    const t = this.peek();
    if (['id', 'int', 'float', 'str', 'cid'].includes(t.k)) return true;
    if (t.k === 'kw') return t.v === 'true' || t.v === 'false';
    return t.k === 'op' && ['(', '[', '{', '_'].includes(t.v);
  }
  parseBindings() {
    const binds = [this.parseBinding()];
    while (this.isKw('and')) { this.next(); binds.push(this.parseBinding()); }
    return binds;
  }
  parseBinding() {
    const line = this.peek().line;
    const save = this.p;
    let name = null;
    if (this.isOp('(') && (this.peek(1).k === 'op' || this.isKw('mod', 1)) && this.isOp(')', 2) && !this.isOp(')', 1)) {
      this.next(); name = this.next().v; this.next();
    } else if (this.peek().k === 'id') name = this.next().v;
    if (name !== null) {
      const params = [];
      while (this.startsPatAtom()) params.push(this.parseAtomPat());
      if (params.length || !this.isOp(',')) {
        let retTy = null;
        if (this.isOp(':')) { this.next(); retTy = this.parseType(); }
        this.expectOp('=');
        let body = this.parseSeq();
        if (retTy) body = E('ann', line, { e: body, ty: retTy });
        const expr = params.length ? E('fun', line, { params, body }) : body;
        return { pat: { t: 'pvar', name, line }, expr, line };
      }
      this.p = save;                                                 // let x, y = ... (tuple 樣式)
    }
    const pat = this.parsePat();
    if (this.isOp(':')) { this.next(); this.parseType(); }
    this.expectOp('=');
    return { pat, expr: this.parseSeq(), line };
  }

  /* ── 樣式 ── */
  parsePat() {
    let p = this.parseOrPat();
    while (this.isKw('as')) { const l = this.next().line; p = { t: 'pas', p, name: this.expectId(), line: l }; }
    return p;
  }
  parseOrPat() {
    const first = this.parseTuplePat();
    if (!this.isOp('|')) return first;
    const alts = [first];
    while (this.isOp('|')) { this.next(); alts.push(this.parseTuplePat()); }
    return { t: 'por', alts, line: first.line };
  }
  parseTuplePat() {
    const first = this.parseConsPat();
    if (!this.isOp(',')) return first;
    const items = [first];
    while (this.isOp(',')) { this.next(); items.push(this.parseConsPat()); }
    return { t: 'ptuple', items, line: first.line };
  }
  parseConsPat() {
    const h = this.parseAppPat();
    if (this.isOp('::')) { const l = this.next().line; return { t: 'pcons', h, tl: this.parseConsPat(), line: l }; }
    return h;
  }
  parseAppPat() {
    const t = this.peek();
    if (t.k === 'cid') {
      this.next();
      const arg = this.startsPatAtom() ? this.parseAtomPat() : null;
      return { t: 'pcon', name: t.v, arg, line: t.line };
    }
    return this.parseAtomPat();
  }
  parseAtomPat() {
    const t = this.next(), line = t.line;
    switch (t.k) {
      case 'id': return { t: 'pvar', name: t.v, line };
      case 'int': return { t: 'plit', kind: 'int', v: t.v, line };
      case 'float': return { t: 'plit', kind: 'float', v: t.v, line };
      case 'str': return { t: 'plit', kind: 'string', v: t.v, line };
      case 'cid': return { t: 'pcon', name: t.v, arg: null, line };
      case 'kw':
        if (t.v === 'true' || t.v === 'false') return { t: 'plit', kind: 'bool', v: t.v === 'true', line };
        break;
      case 'op':
        if (t.v === '_') return { t: 'pwild', line };
        if (t.v === '-' && (this.peek().k === 'int' || this.peek().k === 'float')) {
          const n = this.next(); return { t: 'plit', kind: n.k, v: -n.v, line };
        }
        if (t.v === '(') {
          if (this.isOp(')')) { this.next(); return { t: 'plit', kind: 'unit', v: null, line }; }
          const p = this.parsePat();
          if (this.isOp(':')) { this.next(); const ty = this.parseType(); this.expectOp(')'); return { t: 'pann', p, ty, line }; }
          this.expectOp(')'); return p;
        }
        if (t.v === '[') {
          const items = [];
          if (!this.isOp(']')) { items.push(this.parsePat()); while (this.isOp(';')) { this.next(); if (this.isOp(']')) break; items.push(this.parsePat()); } }
          this.expectOp(']'); return { t: 'plist', items, line };
        }
        if (t.v === '{') {
          const fields = [];
          while (!this.isOp('}')) {
            const name = this.expectId();
            const p = this.isOp('=') ? (this.next(), this.parsePat()) : { t: 'pvar', name, line };
            fields.push({ name, p });
            if (this.isOp(';')) this.next(); else break;
          }
          this.expectOp('}'); return { t: 'prec', fields, line };
        }
        break;
    }
    this.p--; this.err('語法錯誤: 需要樣式 (pattern)');
  }

  /* ── 運算式 ── */
  isSeqEnd() {
    const t = this.peek();
    if (t.k === 'eof') return true;
    if (t.k === 'op') return [')', ']', '}', ';;', '|'].includes(t.v);
    if (t.k === 'kw') return ['end', 'in', 'done', 'then', 'else', 'with', 'and', 'to', 'do', 'downto', 'type', 'external'].includes(t.v);
    return false;
  }
  parseSeq() {
    const a = this.parseExpr();
    if (this.isOp(';')) {
      const line = this.next().line;
      if (this.isSeqEnd()) return a;
      return E('seq', line, { a, b: this.parseSeq() });
    }
    return a;
  }
  startsExprKw() { const t = this.peek(); return t.k === 'kw' && ['let', 'fun', 'function', 'match', 'if', 'while', 'for'].includes(t.v); }
  parseExpr() {
    const t = this.peek();
    if (t.k === 'kw') {
      switch (t.v) {
        case 'let': {
          this.next();
          const rec = this.isKw('rec') ? (this.next(), true) : false;
          const binds = this.parseBindings();
          this.expectKw('in');
          return E('let', t.line, { rec, binds, body: this.parseSeq() });
        }
        case 'fun': {
          this.next(); const params = [];
          while (!this.isOp('->')) { if (!this.startsPatAtom()) this.err('語法錯誤: fun 需要參數樣式'); params.push(this.parseAtomPat()); }
          this.next();
          return E('fun', t.line, { params, body: this.parseSeq() });
        }
        case 'function': {
          this.next();
          return E('fun', t.line, { params: [{ t: 'pvar', name: '%arg', line: t.line }],
            body: E('match', t.line, { scrut: E('var', t.line, { name: '%arg' }), arms: this.parseArms() }) });
        }
        case 'match': {
          this.next();
          const scrut = this.parseSeq();
          this.expectKw('with');
          return E('match', t.line, { scrut, arms: this.parseArms() });
        }
        case 'if': {
          this.next();
          const c = this.parseExpr(); this.expectKw('then');
          const a = this.parseExpr();
          let b = null;
          if (this.isKw('else')) { this.next(); b = this.parseExpr(); }
          return E('if', t.line, { c, a, b });
        }
        case 'while': {
          this.next(); const c = this.parseSeq(); this.expectKw('do');
          const body = this.parseSeq(); this.expectKw('done');
          return E('while', t.line, { c, body });
        }
        case 'for': {
          this.next(); const v = this.expectId(); this.expectOp('=');
          const lo = this.parseExpr();
          const down = this.isKw('downto'); if (!down) this.expectKw('to'); else this.next();
          const hi = this.parseExpr(); this.expectKw('do');
          const body = this.parseSeq(); this.expectKw('done');
          return E('for', t.line, { v, lo, hi, down, body });
        }
        default: if (UNSUPPORTED_KW.has(t.v)) fail(t.line, `不支援 "${t.v}"`);
      }
    }
    return this.parseAssign();
  }
  parseArms() {
    const arms = [];
    if (this.isOp('|')) this.next();
    for (;;) {
      const line = this.peek().line;
      const pat = this.parsePat();
      let guard = null;
      if (this.isKw('when')) { this.next(); guard = this.parseExpr(); }
      this.expectOp('->');
      arms.push({ pat, guard, body: this.parseSeq(), line });
      if (this.isOp('|')) this.next(); else break;
    }
    return arms;
  }
  parseAssign() {
    const l = this.parseTuple();
    if (this.isOp(':=')) { const line = this.next().line; return E('app', line, { f: E('var', line, { name: ':=' }), args: [l, this.parseAssign()] }); }
    return l;
  }
  parseTuple() {
    const first = this.parseBin(0);
    if (!this.isOp(',')) return first;
    const items = [first];
    while (this.isOp(',')) { this.next(); items.push(this.parseBin(0)); }
    return E('tuple', first.line, { items });
  }
  binOp() {
    const t = this.peek();
    if (t.k === 'op' && !['=', ',', ';', ';;', '|', '->', ':', '.', ':=', '_', '(', ')', '[', ']', '{', '}'].includes(t.v)) return t.v;
    if (t.k === 'op' && t.v === '=') return '=';
    if (t.k === 'op' && t.v === '|') return null;
    if (t.k === 'kw' && t.v === 'mod') return 'mod';
    return null;
  }
  parseBin(level) {
    if (level > 7) return this.parseUnary();
    let left = this.parseBin(level + 1);
    for (;;) {
      const op = this.binOp();
      if (op === null || opLevel(op) !== level) break;
      const line = this.next().line;
      const right = RIGHT_ASSOC.has(level) ? this.parseBin(level) : this.parseBin(level + 1);
      left = this.mkBin(op, left, right, line);
      if (RIGHT_ASSOC.has(level)) break;
    }
    return left;
  }
  mkBin(op, l, r, line) {
    if (op === '&&' || op === '&') return E('and', line, { a: l, b: r });
    if (op === '||' || op === 'or') return E('or', line, { a: l, b: r });
    return E('app', line, { f: E('var', line, { name: op }), args: [l, r] });
  }
  parseUnary() {
    if (this.isOp('-') || this.isOp('-.')) {
      const op = this.next(), e = this.parseApp();
      if (e.t === 'lit' && (e.kind === 'int' || e.kind === 'float')) return lit(e.kind, -e.v, op.line);
      return E('app', op.line, { f: E('var', op.line, { name: op.v === '-' ? '~-' : '~-.' }), args: [e] });
    }
    if (this.startsExprKw()) return this.parseExpr();
    return this.parseApp();
  }
  startsAtom() {
    const t = this.peek();
    if (['int', 'float', 'str', 'id', 'cid'].includes(t.k)) return true;
    if (t.k === 'kw') return t.v === 'true' || t.v === 'false' || t.v === 'begin';
    return t.k === 'op' && ['(', '[', '{', '!'].includes(t.v);
  }
  parseApp() {
    const f = this.parsePostfix(), args = [];
    while (this.startsAtom()) args.push(this.parsePostfix());
    return args.length ? E('app', f.line, { f, args }) : f;
  }
  parsePostfix() {
    let e = this.parseAtom();
    while (this.isOp('.') && this.peek(1).k === 'id') {
      const line = this.next().line;
      e = E('field', line, { e, name: this.next().v });
    }
    return e;
  }
  parseAtom() {
    const t = this.next(), line = t.line;
    switch (t.k) {
      case 'int': return lit('int', t.v, line);
      case 'float': return lit('float', t.v, line);
      case 'str': return lit('string', t.v, line);
      case 'id': return E('var', line, { name: t.v });
      case 'cid': return E('con', line, { name: t.v });
      case 'kw':
        if (t.v === 'true' || t.v === 'false') return lit('bool', t.v === 'true', line);
        if (t.v === 'begin') { const e = this.parseSeq(); this.expectKw('end'); return e; }
        break;
      case 'op':
        if (t.v === '!') return E('app', line, { f: E('var', line, { name: '!' }), args: [this.parsePostfix()] });
        if (t.v === '(') {
          if (this.isOp(')')) { this.next(); return UNIT_LIT(line); }
          const o = this.peek();
          if ((o.k === 'op' || (o.k === 'kw' && o.v === 'mod')) && this.isOp(')', 1) && !this.isOp(')')) {
            this.next(); this.next(); return E('var', line, { name: o.v });         // (+)  ( * )  (::)  (mod)
          }
          const e = this.parseSeq();
          if (this.isOp(':')) { this.next(); const ty = this.parseType(); this.expectOp(')'); return E('ann', line, { e, ty }); }
          this.expectOp(')'); return e;
        }
        if (t.v === '[') {
          const items = [];
          if (!this.isOp(']')) { items.push(this.parseExpr()); while (this.isOp(';')) { this.next(); if (this.isOp(']')) break; items.push(this.parseExpr()); } }
          this.expectOp(']'); return E('list', line, { items });
        }
        if (t.v === '{') return this.parseRecord(line);
        break;
    }
    this.p--; this.err('語法錯誤: 無法解析的運算式');
  }
  parseRecord(line) {
    let base = null;
    if (!(this.peek().k === 'id' && this.isOp('=', 1))) { base = this.parsePostfix(); this.expectKw('with'); }
    const fields = [];
    while (!this.isOp('}')) {
      const name = this.expectId();
      const e = this.isOp('=') ? (this.next(), this.parseExpr()) : E('var', line, { name });
      fields.push({ name, e });
      if (this.isOp(';')) this.next(); else break;
    }
    this.expectOp('}');
    return base ? E('update', line, { base, fields }) : E('record', line, { fields });
  }
}

/* ═════════════════════════ 型別 ═════════════════════════ */
const GENERIC = 1e9;
let tvId = 0, curLevel = 0;
const newVar = () => ({ tv: true, id: tvId++, level: curLevel, link: null });
const gvar = () => ({ tv: true, id: tvId++, level: GENERIC, link: null });
const con = (name, args = []) => ({ con: name, args });
const T = { int: con('int'), float: con('float'), string: con('string'), bool: con('bool'), unit: con('unit') };
const arrow = (a, b) => con('->', [a, b]);
const tupleT = ts => con('*', ts);
const listT = t => con('list', [t]);

const prune = t => { while (t.tv && t.link) t = t.link; return t; };

function showType(t, names = new Map()) {
  const nameOf = v => {
    if (!names.has(v)) { const k = names.size; names.set(v, "'" + (k < 26 ? String.fromCharCode(97 + k) : 'a' + k)); }
    return names.get(v);
  };
  const go = (t, prec) => {
    t = prune(t);
    if (t.tv) return nameOf(t);
    if (t.con === '->') { const s = `${go(t.args[0], 1)} -> ${go(t.args[1], 0)}`; return prec > 0 ? `(${s})` : s; }
    if (t.con === '*') { const s = t.args.map(a => go(a, 2)).join(' * '); return prec > 1 ? `(${s})` : s; }
    if (!t.args.length) return t.con;
    const as = t.args.length === 1 ? go(t.args[0], 2) : `(${t.args.map(a => go(a, 0)).join(', ')})`;
    return `${as} ${t.con}`;
  };
  return go(t, 0);
}

class TypeMismatch extends Error {}
function occursAdjust(v, t) {
  t = prune(t);
  if (t.tv) { if (t === v) throw new TypeMismatch('occurs'); if (t.level > v.level) t.level = v.level; }
  else for (const a of t.args) occursAdjust(v, a);
}
function unify(a, b) {
  a = prune(a); b = prune(b);
  if (a === b) return;
  if (a.tv) { occursAdjust(a, b); a.link = b; return; }
  if (b.tv) { occursAdjust(b, a); b.link = a; return; }
  if (a.con !== b.con || a.args.length !== b.args.length) throw new TypeMismatch('clash');
  for (let i = 0; i < a.args.length; i++) unify(a.args[i], b.args[i]);
}
function instantiate(t, memo = new Map()) {
  t = prune(t);
  if (t.tv) {
    if (t.level !== GENERIC) return t;
    let v = memo.get(t); if (!v) memo.set(t, v = newVar());
    return v;
  }
  return t.args.length ? con(t.con, t.args.map(a => instantiate(a, memo))) : t;
}
function generalize(t) {
  t = prune(t);
  if (t.tv) { if (t.level > curLevel) t.level = GENERIC; } else t.args.forEach(generalize);
}
function adjustLevels(t) {
  t = prune(t);
  if (t.tv) { if (t.level !== GENERIC && t.level > curLevel) t.level = curLevel; } else t.args.forEach(adjustLevels);
}
function subst(t, map) {
  t = prune(t);
  if (t.tv) return map.get(t) || t;
  return t.args.length ? con(t.con, t.args.map(a => subst(a, map))) : t;
}

/* 型別環境 */
let TYPES, CONS, FIELDS, RECS, GT;                            // GT: 全域值 -> {type}
function resetTypeState() {
  TYPES = new Map([['int', { n: 0 }], ['float', { n: 0 }], ['string', { n: 0 }], ['bool', { n: 0 }], ['unit', { n: 0 }], ['list', { n: 1 }], ['ref', { n: 1 }]]);
  CONS = new Map(); FIELDS = new Map(); RECS = new Map(); GT = new Map();
}
const lookupT = (ch, name) => { for (let c = ch; c; c = c.parent) if (c.name === name) return c.info; return GT.get(name); };
const extendT = (ch, map) => { for (const [n, info] of map) ch = { name: n, info, parent: ch }; return ch; };

function convType(te, vars, generic) {
  switch (te.t) {
    case 'tyvar': { let v = vars.get(te.name); if (!v) { v = generic ? gvar() : newVar(); vars.set(te.name, v); } return v; }
    case 'arrow': return arrow(convType(te.a, vars, generic), convType(te.b, vars, generic));
    case 'tuple': return tupleT(te.items.map(x => convType(x, vars, generic)));
    case 'tname': {
      const def = TYPES.get(te.name);
      if (!def) fail(te.line, `未定義的型別 "${te.name}"`);
      if (te.args.length !== def.n) fail(te.line, `型別 ${te.name} 需要 ${def.n} 個型別參數，但給了 ${te.args.length} 個`);
      const args = te.args.map(a => convType(a, vars, generic));
      if (def.alias) return subst(def.alias.type, new Map(def.alias.params.map((p, i) => [p, args[i]])));
      return con(te.name, args);
    }
  }
  throw new Error('bad type expr');
}

function declareTypes(defs) {
  for (const d of defs) {
    if (TYPES.has(d.name) && ['int', 'float', 'string', 'bool', 'unit', 'list', 'ref'].includes(d.name)) fail(d.line, `不能重新定義內建型別 ${d.name}`);
    TYPES.set(d.name, { n: d.params.length });
  }
  for (const d of defs) {
    const vars = new Map(), params = d.params.map(p => { const v = gvar(); vars.set(p, v); return v; });
    if (d.kind === 'variant') {
      d.ctors.forEach(c => {
        const args = c.args.map(a => convType(a, vars, true));
        CONS.set(c.name, { name: c.name, tyName: d.name, args, arity: args.length, res: con(d.name, params), siblings: d.ctors.length });
      });
    } else if (d.kind === 'record') {
      const fields = d.fields.map(f => ({ name: f.name, type: convType(f.type, vars, true) }));
      const rec = { name: d.name, params, fields, res: con(d.name, params) };
      RECS.set(d.name, rec);
      fields.forEach((f, idx) => FIELDS.set(f.name, { rec, idx, type: f.type }));
    } else TYPES.get(d.name).alias = { params, type: convType(d.type, vars, true) };
  }
}

/* ═════════════════════════ 型別推論 ═════════════════════════ */
function unifyAt(actual, expected, node, what) {
  try { unify(actual, expected); }
  catch (e) {
    if (!(e instanceof TypeMismatch)) throw e;
    const names = new Map();
    const a = showType(actual, names), x = showType(expected, names);
    fail(node.line, `型別不符${what ? ' (' + what + ')' : ''}\n    這個運算式的型別是: ${a}\n    但此處需要:        ${x}` + (e.message === 'occurs' ? '\n    (這會造成無限型別)' : ''));
  }
}

function isValue(e) {
  switch (e.t) {
    case 'lit': case 'var': case 'con': case 'fun': return true;
    case 'tuple': case 'list': return e.items.every(isValue);
    case 'app': return e.f.t === 'con' && e.args.every(isValue);
    case 'record': return e.fields.every(f => isValue(f.e));
    case 'ann': return isValue(e.e);
    default: return false;
  }
}

const specType = s => ({ d: T.int, s: T.string, f: T.float, b: T.bool })[s];
function parseFormat(fmt, line) {
  const pieces = []; const re = /%([-0]*)(\d*)(?:\.(\d+))?([a-zA-Z%])/g; let last = 0, m;
  while ((m = re.exec(fmt))) {
    if (m.index > last) pieces.push({ lit: fmt.slice(last, m.index) });
    let conv = m[4]; if (conv === 'i') conv = 'd';
    if (conv === '%') pieces.push({ lit: '%' });
    else if ('dsfb'.includes(conv)) pieces.push({ spec: conv, left: m[1].includes('-'), zero: m[1].includes('0'), width: m[2] ? +m[2] : 0, prec: m[3] !== undefined ? +m[3] : null });
    else fail(line, `Printf 不支援 %${m[4]} (支援 %d %s %f %b %%)`);
    last = re.lastIndex;
  }
  if (last < fmt.length) pieces.push({ lit: fmt.slice(last) });
  return pieces;
}

function applyArg(tf, a, ch) {
  const ta = infer(a, ch);
  tf = prune(tf);
  if (tf.con === '->') { unifyAt(ta, tf.args[0], a, '函式參數'); return tf.args[1]; }
  if (tf.tv) { const r = newVar(); unifyAt(tf, arrow(ta, r), a); return r; }
  fail(a.line, `這個值的型別是 ${showType(tf)}，不是函式，卻被套用了參數`);
}

function instCon(ci) {
  const memo = new Map();
  return { args: ci.args.map(a => instantiate(a, memo)), res: instantiate(ci.res, memo) };
}
function instRec(rec) {
  const memo = new Map();
  return { fields: rec.fields.map(f => instantiate(f.type, memo)), res: instantiate(rec.res, memo) };
}

function infer(e, ch) {
  switch (e.t) {
    case 'lit': return { int: T.int, float: T.float, string: T.string, bool: T.bool, unit: T.unit }[e.kind];
    case 'var': {
      const info = lookupT(ch, e.name);
      if (!info) fail(e.line, `未定義的值 "${e.name}"`);
      if (info.special) fail(e.line, `${e.name} 必須以字串常值作為格式並直接套用，例如 ${e.name} "%d\\n" x`);
      return instantiate(info.type);
    }
    case 'con': {
      const ci = CONS.get(e.name);
      if (!ci) fail(e.line, `未定義的建構子 "${e.name}"`);
      const inst = instCon(ci);
      if (ci.arity === 0) return inst.res;
      if (ci.arity === 1) return arrow(inst.args[0], inst.res);
      fail(e.line, `建構子 ${e.name} 需要 ${ci.arity} 個參數，請寫成 ${e.name} (a, b, ...)`);
    }
    case 'app': {
      if (e.f.t === 'con') {
        const ci = CONS.get(e.f.name);
        if (!ci) fail(e.line, `未定義的建構子 "${e.f.name}"`);
        if (ci.arity === 0) fail(e.line, `建構子 ${e.f.name} 不接受參數`);
        if (e.args.length !== 1) fail(e.line, `建構子 ${e.f.name} 只能套用一個參數 (多個請用括號 tuple)`);
        const inst = instCon(ci), a = e.args[0];
        if (ci.arity === 1) unifyAt(infer(a, ch), inst.args[0], a, `建構子 ${ci.name} 的參數`);
        else {
          if (a.t !== 'tuple' || a.items.length !== ci.arity) fail(a.line, `建構子 ${ci.name} 需要 ${ci.arity} 個參數，請寫成 ${ci.name} (a, b, ...)`);
          a.items.forEach((x, i) => unifyAt(infer(x, ch), inst.args[i], x, `建構子 ${ci.name} 的第 ${i + 1} 個參數`));
        }
        return inst.res;
      }
      if (e.f.t === 'var') {
        const info = lookupT(ch, e.f.name);
        if (info && info.special) {
          const fmt = e.args[0];
          if (!fmt || fmt.t !== 'lit' || fmt.kind !== 'string') fail(e.line, `${e.f.name} 的第一個參數必須是字串常值格式`);
          let t = info.special === 'printf' ? T.unit : T.string;
          const pieces = parseFormat(fmt.v, e.line).filter(p => p.spec);
          for (let i = pieces.length - 1; i >= 0; i--) t = arrow(specType(pieces[i].spec), t);
          for (const a of e.args.slice(1)) {
            t = prune(t);
            if (t.con !== '->') fail(a.line, `${e.f.name} 的參數太多 (格式字串只有 ${pieces.length} 個轉換)`);
            unifyAt(infer(a, ch), t.args[0], a, `${e.f.name} 的格式參數`);
            t = t.args[1];
          }
          return t;
        }
      }
      let t = infer(e.f, ch);
      for (const a of e.args) t = applyArg(t, a, ch);
      return t;
    }
    case 'fun': {
      let ch2 = ch; const pts = [];
      for (const p of e.params) { const b = new Map(); pts.push(inferPat(p, b)); ch2 = extendT(ch2, b); }
      let t = infer(e.body, ch2);
      for (let i = pts.length - 1; i >= 0; i--) t = arrow(pts[i], t);
      return t;
    }
    case 'let': {
      const out = inferLet(e.rec, e.binds, ch);
      return infer(e.body, extendT(ch, out));
    }
    case 'if': {
      unifyAt(infer(e.c, ch), T.bool, e.c, 'if 的條件');
      const t = infer(e.a, ch);
      if (e.b) unifyAt(infer(e.b, ch), t, e.b, 'if 的 else 分支必須與 then 分支同型別');
      else unifyAt(t, T.unit, e.a, '沒有 else 的 if，then 分支必須是 unit');
      return t;
    }
    case 'match': {
      const st = infer(e.scrut, ch), rt = newVar();
      for (const arm of e.arms) {
        const b = new Map(), pt = inferPat(arm.pat, b);
        unifyAt(pt, st, arm.pat, 'match 的樣式型別必須與被匹配的值相同');
        const ch2 = extendT(ch, b);
        if (arm.guard) unifyAt(infer(arm.guard, ch2), T.bool, arm.guard, 'when 守衛');
        unifyAt(infer(arm.body, ch2), rt, arm.body, 'match 各分支必須回傳相同型別');
      }
      return rt;
    }
    case 'tuple': return tupleT(e.items.map(x => infer(x, ch)));
    case 'list': {
      const et = newVar();
      for (const x of e.items) unifyAt(infer(x, ch), et, x, 'list 的元素必須同型別');
      return listT(et);
    }
    case 'seq': infer(e.a, ch); return infer(e.b, ch);
    case 'ann': { const t = infer(e.e, ch); unifyAt(t, convType(e.ty, new Map(), false), e, '型別標註'); return t; }
    case 'and': case 'or':
      unifyAt(infer(e.a, ch), T.bool, e.a, `${e.t === 'and' ? '&&' : '||'} 的運算元`);
      unifyAt(infer(e.b, ch), T.bool, e.b, `${e.t === 'and' ? '&&' : '||'} 的運算元`);
      return T.bool;
    case 'while':
      unifyAt(infer(e.c, ch), T.bool, e.c, 'while 的條件'); infer(e.body, ch); return T.unit;
    case 'for': {
      unifyAt(infer(e.lo, ch), T.int, e.lo, 'for 的起點'); unifyAt(infer(e.hi, ch), T.int, e.hi, 'for 的終點');
      infer(e.body, extendT(ch, new Map([[e.v, { type: T.int }]]))); return T.unit;
    }
    case 'field': {
      const fi = FIELDS.get(e.name);
      if (!fi) fail(e.line, `未定義的欄位 "${e.name}"`);
      const inst = instRec(fi.rec);
      unifyAt(infer(e.e, ch), inst.res, e.e, `存取欄位 ${e.name}`);
      return inst.fields[fi.idx];
    }
    case 'record': case 'update': {
      const first = FIELDS.get(e.fields[0].name);
      if (!first) fail(e.line, `未定義的欄位 "${e.fields[0].name}"`);
      const rec = first.rec, inst = instRec(rec), seen = new Set();
      if (e.t === 'update') unifyAt(infer(e.base, ch), inst.res, e.base, 'record update 的對象');
      for (const f of e.fields) {
        const fi = FIELDS.get(f.name);
        if (!fi || fi.rec !== rec) fail(e.line, `欄位 "${f.name}" 不屬於 record 型別 ${rec.name}`);
        if (seen.has(f.name)) fail(e.line, `欄位 "${f.name}" 重複`);
        seen.add(f.name);
        unifyAt(infer(f.e, ch), inst.fields[fi.idx], f.e, `欄位 ${f.name}`);
      }
      if (e.t === 'record') {
        const missing = rec.fields.filter(f => !seen.has(f.name)).map(f => f.name);
        if (missing.length) fail(e.line, `record 缺少欄位: ${missing.join(', ')}`);
      }
      return inst.res;
    }
  }
  throw new Error('infer: 未知節點 ' + e.t);
}

function inferPat(p, b) {
  switch (p.t) {
    case 'pvar': {
      if (b.has(p.name)) fail(p.line, `變數 "${p.name}" 在同一個樣式中重複出現`);
      const t = newVar(); b.set(p.name, { type: t }); return t;
    }
    case 'pwild': return newVar();
    case 'plit': return { int: T.int, float: T.float, string: T.string, bool: T.bool, unit: T.unit }[p.kind];
    case 'ptuple': return tupleT(p.items.map(x => inferPat(x, b)));
    case 'plist': {
      const et = newVar();
      for (const x of p.items) unifyAt(inferPat(x, b), et, x, 'list 樣式的元素');
      return listT(et);
    }
    case 'pcons': {
      const h = inferPat(p.h, b), t = inferPat(p.tl, b);
      unifyAt(t, listT(h), p.tl, ':: 樣式');
      return t;
    }
    case 'pcon': {
      const ci = CONS.get(p.name);
      if (!ci) fail(p.line, `未定義的建構子 "${p.name}"`);
      const inst = instCon(ci);
      if (ci.arity === 0) { if (p.arg) fail(p.line, `建構子 ${p.name} 不接受參數`); return inst.res; }
      if (!p.arg) fail(p.line, `建構子 ${p.name} 需要 ${ci.arity} 個參數`);
      if (ci.arity === 1) unifyAt(inferPat(p.arg, b), inst.args[0], p.arg, `建構子 ${p.name} 的參數樣式`);
      else if (p.arg.t === 'ptuple' && p.arg.items.length === ci.arity)
        p.arg.items.forEach((x, i) => unifyAt(inferPat(x, b), inst.args[i], x, `建構子 ${p.name} 的第 ${i + 1} 個參數樣式`));
      else if (p.arg.t === 'pwild') { /* 全部忽略 */ }
      else fail(p.line, `建構子 ${p.name} 需要 ${ci.arity} 個參數，請寫成 ${p.name} (a, b, ...) 或 ${p.name} _`);
      return inst.res;
    }
    case 'pas': {
      const t = inferPat(p.p, b);
      if (b.has(p.name)) fail(p.line, `變數 "${p.name}" 重複出現`);
      b.set(p.name, { type: t }); return t;
    }
    case 'por': {
      const t = newVar();
      for (const alt of p.alts) {
        const b2 = new Map();
        unifyAt(inferPat(alt, b2), t, alt, 'or 樣式的各選項必須同型別');
        if (b2.size) fail(p.line, 'or 樣式 (p1 | p2) 中不可綁定變數');
      }
      return t;
    }
    case 'prec': {
      const first = FIELDS.get(p.fields[0].name);
      if (!first) fail(p.line, `未定義的欄位 "${p.fields[0].name}"`);
      const inst = instRec(first.rec);
      for (const f of p.fields) {
        const fi = FIELDS.get(f.name);
        if (!fi || fi.rec !== first.rec) fail(p.line, `欄位 "${f.name}" 不屬於 record 型別 ${first.rec.name}`);
        unifyAt(inferPat(f.p, b), inst.fields[fi.idx], f.p, `欄位 ${f.name} 的樣式`);
      }
      return inst.res;
    }
    case 'pann': { const t = inferPat(p.p, b); unifyAt(t, convType(p.ty, new Map(), false), p, '型別標註'); return t; }
  }
  throw new Error('inferPat: 未知節點 ' + p.t);
}

function inferLet(rec, binds, ch) {
  curLevel++;
  let chIn = ch; const recVars = [];
  if (rec) for (const b of binds) {
    if (b.pat.t !== 'pvar') fail(b.line, 'let rec 的左側必須是變數');
    const v = newVar(); recVars.push(v);
    chIn = { name: b.pat.name, info: { type: v }, parent: chIn };
  }
  const results = [];
  binds.forEach((b, i) => {
    const t = infer(b.expr, rec ? chIn : ch);
    let bindings;
    if (rec) { unifyAt(t, recVars[i], b.expr, `遞迴函式 ${b.pat.name}`); bindings = new Map([[b.pat.name, { type: recVars[i] }]]); }
    else { bindings = new Map(); unifyAt(t, inferPat(b.pat, bindings), b.expr, '綁定的樣式與運算式型別不符'); }
    results.push({ bindings, expr: b.expr });
  });
  curLevel--;
  const out = new Map(), allVal = results.every(r => isValue(r.expr));
  for (const r of results) {
    const val = rec ? allVal : isValue(r.expr);
    for (const [n, info] of r.bindings) { if (val) generalize(info.type); else adjustLevels(info.type); out.set(n, info); }
  }
  return out;
}

const countArrows = ty => { let n = 0; while (ty.t === 'arrow') { n++; ty = ty.b; } return n; };

function checkItem(item) {
  switch (item.t) {
    case 'type': declareTypes(item.defs); break;
    case 'external': {
      GT.set(item.name, { type: convType(item.ty, new Map(), true) });
      break;
    }
    case 'let': {
      const out = inferLet(item.rec, item.binds, null);
      for (const [n, info] of out) GT.set(n, info);
      item.types = [...out].map(([n, info]) => [n, info.type]);
      break;
    }
    case 'expr': infer(item.e, null); break;
  }
}

/* ═════════════════════════ 程式碼產生: AST -> Scheme 核心 ═════════════════════════ */
class SStr { constructor(v) { this.v = v; } }
const LBC_PRIMS = ['+', '*', '-', '/', 'quotient', 'remainder', 'modulo', '=', '<', '>', '<=', '>=', 'abs', 'min', 'max', 'zero?', 'even?',
  'odd?', 'not', 'eq?', 'eqv?', 'equal?', 'cons', 'car', 'cdr', 'cadr', 'cddr', 'caddr', 'list', 'length', 'append', 'reverse', 'null?',
  'pair?', 'number?', 'string?', 'symbol?', 'procedure?', 'string-append', 'string-length', 'number->string', 'display', 'write', 'newline', 'error',
  'sqrt', 'floor', 'ceil', 'sin', 'cos', 'atan2', 'exp', 'log', 'pow',
  'bit-and', 'bit-or', 'bit-xor', 'shift-left', 'shift-right', 'shift-right-logical',
  'compare', 'hash', 'char-code', 'char-chr', 'string-get',
  'vector', 'make-vector', 'vector-length', 'vector-ref', 'vector-set!', 'set-car!', 'set-cdr!'];
const SCHEME_KW = ['quote', 'if', 'define', 'set!', 'lambda', 'begin', 'let', 'let*', 'letrec', 'cond', 'and', 'or', 'when', 'unless', 'else'];
const RESERVED = new Set([...LBC_PRIMS, ...SCHEME_KW]);
const ident = n => { n = n.replace(/'/g, '_q'); return RESERVED.has(n) ? 'u/' + n : n; };
const NIL_Q = ['quote', []];
let tmpN = 0;
const tmp = (p = 't') => `%${p}${tmpN++}`;

function show(x) {
  if (typeof x === 'number') return String(x);
  if (typeof x === 'string') return x;
  if (x === true) return '#t';
  if (x === false) return '#f';
  if (x instanceof SStr) return JSON.stringify(x.v);
  if (Array.isArray(x)) return '(' + x.map(show).join(' ') + ')';
  throw new Error('無法輸出: ' + JSON.stringify(x));
}

let GC, IN_PRELUDE = false, USER_DEFS = new Map();               // GC: 全域值 -> {cname, arity, kind}
const lookupC = (ch, name) => { for (let c = ch; c; c = c.parent) if (c.name === name) return c.info; return GC.get(name); };
const extendC = (ch, names) => { for (const n of names) ch = { name: n, info: { cname: ident(n), arity: 0, kind: 'val' }, parent: ch }; return ch; };
const directName = info => info.kind === 'ext' ? info.cname : (info.arity >= 2 ? `${info.cname}/${info.arity}` : info.cname);

function nth(acc, i) {
  if (i === 0) return ['car', acc];
  if (i === 1) return ['cadr', acc];
  if (i === 2) return ['caddr', acc];
  let e = acc; for (let k = 0; k < i; k++) e = ['cdr', e];
  return ['car', e];
}
const curry = (names, body) => names.reduceRight((b, n) => ['lambda', [n], b], body);
const fail_match = () => ['error', new SStr('Match_failure')];
const wrapBinds = (test, binds, body) => {
  const b = binds.length ? ['let', binds, body] : body;          // 樣式綁定彼此獨立，用平行 let (只產生一個 closure)
  return test === true ? b : ['if', test, b, fail_match()];
};

/* 樣式 -> {test: 條件(或 true), binds: [[名稱, 取值運算式]], names: 綁定的 ML 變數} */
function patCompile(p, acc) {
  const tests = [], binds = [], names = [];
  const go = (p, acc) => {
    switch (p.t) {
      case 'pvar': binds.push([ident(p.name), acc]); names.push(p.name); break;
      case 'pwild': break;
      case 'plit':
        if (p.kind === 'unit') break;
        if (p.kind === 'bool') tests.push(['eq?', acc, p.v]);
        else tests.push(['equal?', acc, p.kind === 'string' ? new SStr(p.v) : p.v]);
        break;
      case 'ptuple': p.items.forEach((x, i) => go(x, nth(acc, i))); break;
      case 'plist': {
        let a = acc;
        for (const x of p.items) { tests.push(['pair?', a]); go(x, ['car', a]); a = ['cdr', a]; }
        tests.push(['null?', a]); break;
      }
      case 'pcons': tests.push(['pair?', acc]); go(p.h, ['car', acc]); go(p.tl, ['cdr', acc]); break;
      case 'pcon': {
        const ci = CONS.get(p.name);
        if (ci.siblings > 1) tests.push(['eq?', ['car', acc], ['quote', p.name]]);
        if (p.arg && p.arg.t !== 'pwild') {
          if (ci.arity === 1) go(p.arg, nth(acc, 1)); else p.arg.items.forEach((x, i) => go(x, nth(acc, i + 1)));
        }
        break;
      }
      case 'pas': binds.push([ident(p.name), acc]); names.push(p.name); go(p.p, acc); break;
      case 'por': {
        const ts = p.alts.map(a => patCompile(a, acc).test);
        if (!ts.includes(true)) tests.push(ts.length === 1 ? ts[0] : ['or', ...ts]);
        break;
      }
      case 'prec': for (const f of p.fields) go(f.p, nth(acc, FIELDS.get(f.name).idx)); break;
      case 'pann': go(p.p, acc); break;
      default: throw new Error('patCompile: ' + p.t);
    }
  };
  go(p, acc);
  return { test: tests.length === 0 ? true : tests.length === 1 ? tests[0] : ['and', ...tests], binds, names };
}

function prepParams(params, ch) {
  const names = [], pre = []; let ch2 = ch;
  for (const p of params) {
    if (p.t === 'pvar') { names.push(ident(p.name)); ch2 = extendC(ch2, [p.name]); }
    else { const t = tmp('a'); names.push(t); const pc = patCompile(p, t); pre.push(pc); ch2 = extendC(ch2, pc.names); }
  }
  return { names, ch2, wrap: body => pre.reduceRight((b, pc) => wrapBinds(pc.test, pc.binds, b), body) };
}

function genMatch(scrut, arms, ch) {
  const sc = gen(scrut, ch), compiled = arms.map(a => ({ a, pc: null }));
  let v, pre = null;
  const armVars = new Set(); arms.forEach(a => { const pc = patCompile(a.pat, '%x'); pc.names.forEach(n => armVars.add(ident(n))); });
  if (typeof sc === 'string' && !armVars.has(sc)) v = sc; else { v = tmp('m'); pre = [[v, sc]]; }
  let chain = fail_match();
  for (let i = arms.length - 1; i >= 0; i--) {
    const arm = arms[i], pc = patCompile(arm.pat, v), ch2 = extendC(ch, pc.names);
    const body = gen(arm.body, ch2), withB = x => pc.binds.length ? ['let', pc.binds, x] : x;
    if (arm.guard) {
      const g = withB(gen(arm.guard, ch2));
      chain = ['if', pc.test === true ? g : ['and', pc.test, g], withB(body), chain];
    } else chain = pc.test === true ? withB(body) : ['if', pc.test, withB(body), chain];
  }
  return pre ? ['let', pre, chain] : chain;
}

/* let 綁定 -> Scheme 綁定對。具名函式 (元數 k>=2) 產生兩個名稱:  f/k (多參數，直接呼叫用) 與 f (curried，當值用) */
function genBindings(binds, rec, ch, globalMode) {
  const infos = binds.map(b => {
    if (b.pat.t !== 'pvar') return null;
    const k = b.expr.t === 'fun' ? b.expr.params.length : 0;
    let cname;
    if (globalMode) {
      const n = b.pat.name;
      if (IN_PRELUDE) cname = 'ml/' + n;
      else { const c = USER_DEFS.get(n) || 0; USER_DEFS.set(n, c + 1); cname = ident(n) + (c ? `~${c}` : ''); }
    } else cname = ident(b.pat.name);
    return { cname, arity: k, kind: k ? 'fun' : 'val' };
  });
  const register = (c, i, b) => globalMode ? GC.set(b.pat.name, infos[i]) : { name: b.pat.name, info: infos[i], parent: c };
  let chRec = ch;
  if (rec) binds.forEach((b, i) => { const r = register(chRec, i, b); if (!globalMode) chRec = r; });
  const defs = [];
  binds.forEach((b, i) => {
    const body = rec ? chRec : ch;
    if (b.pat.t === 'pvar') {
      const info = infos[i];
      if (info.arity === 0) defs.push([info.cname, gen(b.expr, body)]);
      else {
        const { names, ch2, wrap } = prepParams(b.expr.params, body);
        const fbody = wrap(gen(b.expr.body, ch2));
        if (info.arity === 1) defs.push([info.cname, ['lambda', names, fbody]]);
        else {
          const args = names.map(() => tmp('c'));
          defs.push([`${info.cname}/${info.arity}`, ['lambda', names, fbody]], [info.cname, curry(args, [`${info.cname}/${info.arity}`, ...args])]);
        }
      }
    } else {
      const t = tmp('v'), pc = patCompile(b.pat, t);
      defs.push([t, gen(b.expr, body)]);
      if (pc.test !== true) defs.push([tmp('chk'), ['if', pc.test, 0, fail_match()]]);
      for (const [n, code] of pc.binds) defs.push([n, code]);
      pc.names.forEach(n => { const info = { cname: ident(n), arity: 0, kind: 'val' }; infos.push(info); if (globalMode) { info.cname = IN_PRELUDE ? 'ml/' + n : ident(n); GC.set(n, info); } });
    }
  });
  if (globalMode) {
    // 全域模式: 把 pattern 綁定的名稱改成全域 cname
    for (const d of defs) if (typeof d[0] === 'string' && !d[0].startsWith('%')) { /* 已是正確名稱 */ }
    if (!rec) binds.forEach((b, i) => { if (b.pat.t === 'pvar') GC.set(b.pat.name, infos[i]); });
    return { defs, ch2: ch };
  }
  let ch2 = ch;
  binds.forEach((b, i) => { if (b.pat.t === 'pvar') ch2 = { name: b.pat.name, info: infos[i], parent: ch2 }; });
  binds.forEach(b => { if (b.pat.t !== 'pvar') ch2 = extendC(ch2, patCompile(b.pat, '%x').names); });
  return { defs, ch2 };
}

function genPrintf(kind, e, ch) {
  const pieces = parseFormat(e.args[0].v, e.line), given = e.args.slice(1);
  const missing = [], codes = []; let si = 0;
  const helper = n => directName(GC.get(n));
  for (const pc of pieces) {
    if (pc.lit !== undefined) { codes.push(new SStr(pc.lit)); continue; }
    let a;
    if (si < given.length) a = gen(given[si], ch); else { a = tmp('p'); missing.push(a); }
    si++;
    let s;
    if (pc.spec === 'd') s = ['number->string', a];
    else if (pc.spec === 's') s = a;
    else if (pc.spec === 'b') s = ['if', a, new SStr('true'), new SStr('false')];
    else s = [helper('__fmt_float'), pc.prec === null ? 6 : pc.prec, a];
    if (pc.width) s = pc.left ? [helper('__pad_right'), pc.width, s] : [helper('__pad_left'), pc.width, new SStr(pc.zero ? '0' : ' '), s];
    codes.push(s);
  }
  const str = codes.length === 0 ? new SStr('') : codes.length === 1 ? codes[0] : ['string-append', ...codes];
  return curry(missing, kind === 'printf' ? ['begin', ['display', str], NIL_Q] : str);
}

function gen(e, ch) {
  switch (e.t) {
    case 'lit':
      if (e.kind === 'unit') return NIL_Q;
      if (e.kind === 'string') return new SStr(e.v);
      return e.v;
    case 'var': {
      const info = lookupC(ch, e.name);
      if (!info) return ident(e.name);
      if (info.kind === 'ext' && info.arity >= 2) { const ps = Array.from({ length: info.arity }, () => tmp('x')); return curry(ps, [info.cname, ...ps]); }
      return info.cname;
    }
    case 'con': {
      const ci = CONS.get(e.name);
      if (ci.arity === 0) return ['quote', [e.name]];
      const x = tmp('x'); return ['lambda', [x], ['list', ['quote', e.name], x]];
    }
    case 'app': {
      if (e.f.t === 'con') {
        const ci = CONS.get(e.f.name), a = e.args[0];
        return ['list', ['quote', e.f.name], ...(ci.arity === 1 ? [gen(a, ch)] : a.items.map(x => gen(x, ch)))];
      }
      if (e.f.t === 'var') {
        const info = lookupC(ch, e.f.name);
        if (info && info.special) return genPrintf(info.special, e, ch);
        const numLit = a => a.t === 'lit' && (a.kind === 'int' || a.kind === 'float');
        if (info && e.args.length === 2 && e.args.some(numLit)) {          // 與數字字面值比較: 用 = (wasm 快速路徑)
          if (info.kind === 'ext' && info.cname === 'equal?') return ['=', gen(e.args[0], ch), gen(e.args[1], ch)];
          if (info === GC.get('<>') && info.cname === 'ml/<>') return ['not', ['=', gen(e.args[0], ch), gen(e.args[1], ch)]];
        }
        if (info && info.arity >= 1 && (info.kind === 'fun' || info.kind === 'ext')) {
          const k = info.arity, d = directName(info);
          if (e.args.length >= k) {
            let call = [d, ...e.args.slice(0, k).map(a => gen(a, ch))];
            for (const a of e.args.slice(k)) call = [call, gen(a, ch)];
            return call;
          }
          const given = e.args.map(a => { const c = gen(a, ch); return (typeof c === 'string' || typeof c === 'number') ? { code: c } : { name: tmp('g'), code: c }; });
          const missing = Array.from({ length: k - e.args.length }, () => tmp('p'));
          const body = curry(missing, [d, ...given.map(g => g.name || g.code), ...missing]);
          const bs = given.filter(g => g.name).map(g => [g.name, g.code]);
          return bs.length ? ['let', bs, body] : body;
        }
      }
      let r = gen(e.f, ch);
      for (const a of e.args) r = [r, gen(a, ch)];
      return r;
    }
    case 'fun': { const { names, ch2, wrap } = prepParams(e.params, ch); return curry(names, wrap(gen(e.body, ch2))); }
    case 'let': {
      const { defs, ch2 } = genBindings(e.binds, e.rec, ch, false);
      const body = gen(e.body, ch2);
      return e.rec ? ['letrec', defs, body] : ['let*', defs, body];
    }
    case 'if': return ['if', gen(e.c, ch), gen(e.a, ch), e.b ? gen(e.b, ch) : NIL_Q];
    case 'match': return genMatch(e.scrut, e.arms, ch);
    case 'tuple': return ['list', ...e.items.map(x => gen(x, ch))];
    case 'list': return e.items.length ? ['list', ...e.items.map(x => gen(x, ch))] : NIL_Q;
    case 'seq': return ['begin', gen(e.a, ch), gen(e.b, ch)];
    case 'ann': return gen(e.e, ch);
    case 'and': return ['if', gen(e.a, ch), gen(e.b, ch), false];
    case 'or': return ['if', gen(e.a, ch), true, gen(e.b, ch)];
    case 'while': { const lp = tmp('loop'); return ['letrec', [[lp, ['lambda', [], ['if', gen(e.c, ch), ['begin', gen(e.body, ch), [lp]], NIL_Q]]]], [lp]]; }
    case 'for': {
      const lp = tmp('loop'), hi = tmp('hi'), v = ident(e.v), ch2 = extendC(ch, [e.v]);
      return ['let', [[hi, gen(e.hi, ch)]], ['letrec', [[lp, ['lambda', [v],
        ['if', [e.down ? '>=' : '<=', v, hi], ['begin', gen(e.body, ch2), [lp, [e.down ? '-' : '+', v, 1]]], NIL_Q]]]], [lp, gen(e.lo, ch)]]];
    }
    case 'field': return nth(gen(e.e, ch), FIELDS.get(e.name).idx);
    case 'record': case 'update': {
      const rec = FIELDS.get(e.fields[0].name).rec, given = new Map(e.fields.map(f => [f.name, f.e]));
      if (e.t === 'record') return ['list', ...rec.fields.map(f => gen(given.get(f.name), ch))];
      const t = tmp('r');
      return ['let', [[t, gen(e.base, ch)]], ['list', ...rec.fields.map((f, i) => given.has(f.name) ? gen(given.get(f.name), ch) : nth(t, i))]];
    }
  }
  throw new Error('gen: 未知節點 ' + e.t);
}

/* 頂層項目 -> Scheme 形式 */
function genItem(item) {
  switch (item.t) {
    case 'type': return [];
    case 'external': GC.set(item.name, { cname: item.cname, arity: countArrows(item.ty), kind: 'ext' }); return [];
    case 'expr': return [gen(item.e, null)];
    case 'let': {
      const { defs } = genBindings(item.binds, item.rec, null, true);
      return defs.map(([n, c]) => ['define', n, c]);
    }
  }
}

/* ═════════════════════════ Prelude: 以 ML 撰寫的標準函式庫 ═════════════════════════ */
const RUNTIME_HELPERS = [   // 手寫的 Scheme 輔助函式 (ref 以 closure 實作)
  ['ml/ref', ['define', 'ml/ref', ['lambda', ['v'], ['lambda', ['op', 'a'], ['if', ['eq?', 'op', 0], 'v', ['begin', ['set!', 'v', 'a'], NIL_Q]]]]]],
  ['ml/deref', ['define', 'ml/deref', ['lambda', ['r'], ['r', 0, 0]]]],
  ['ml/assign', ['define', 'ml/assign', ['lambda', ['r', 'v'], ['r', 1, 'v']]]],
  ['ml/id', ['define', 'ml/id', ['lambda', ['x'], 'x']]],
  ['ml/trunc', ['define', 'ml/trunc', ['lambda', ['x'], ['quotient', 'x', 1]]]],
];

const PRELUDE = String.raw`
type 'a option = None | Some of 'a
type ('a, 'b) result = Ok of 'a | Error of 'b

external ( + ) : int -> int -> int = "+"
external ( - ) : int -> int -> int = "-"
external ( * ) : int -> int -> int = "*"
external ( / ) : int -> int -> int = "quotient"
external ( mod ) : int -> int -> int = "remainder"
external ( ~- ) : int -> int = "-"
external ( +. ) : float -> float -> float = "+"
external ( -. ) : float -> float -> float = "-"
external ( *. ) : float -> float -> float = "*"
external ( /. ) : float -> float -> float = "/"
external ( ~-. ) : float -> float = "-"
external ( = ) : 'a -> 'a -> bool = "equal?"
external ( == ) : 'a -> 'a -> bool = "eq?"
external ( < ) : 'a -> 'a -> bool = "<"
external ( > ) : 'a -> 'a -> bool = ">"
external ( <= ) : 'a -> 'a -> bool = "<="
external ( >= ) : 'a -> 'a -> bool = ">="
external not : bool -> bool = "not"
external ( ^ ) : string -> string -> string = "string-append"
external ( @ ) : 'a list -> 'a list -> 'a list = "append"
external ( :: ) : 'a -> 'a list -> 'a list = "cons"
external fst : 'a * 'b -> 'a = "car"
external snd : 'a * 'b -> 'b = "cadr"
external ref : 'a -> 'a ref = "ml/ref"
external ( ! ) : 'a ref -> 'a = "ml/deref"
external ( := ) : 'a ref -> 'a -> unit = "ml/assign"
external failwith : string -> 'a = "error"
external abs : int -> int = "abs"
external abs_float : float -> float = "abs"
external min : 'a -> 'a -> 'a = "min"
external max : 'a -> 'a -> 'a = "max"
external float_of_int : int -> float = "ml/id"
external float : int -> float = "ml/id"
external int_of_float : float -> int = "ml/trunc"
external truncate : float -> int = "ml/trunc"
external string_of_int : int -> string = "number->string"
external __number_to_string : float -> string = "number->string"
external print_string : string -> unit = "display"
external print_newline : unit -> unit = "newline"
external String.length : string -> int = "string-length"
external List.length : 'a list -> int = "length"
external List.rev : 'a list -> 'a list = "reverse"
external List.hd : 'a list -> 'a = "car"
external List.tl : 'a list -> 'a list = "cdr"

let ( <> ) a b = not (a = b)
let ( != ) a b = not (a == b)
let ( |> ) x f = f x
let ( @@ ) f x = f x
let ignore _ = ()
let incr r = r := !r + 1
let decr r = r := !r - 1
let succ n = n + 1
let pred n = n - 1
let compare a b = if a < b then -1 else if a = b then 0 else 1
let invalid_arg s = failwith s
let assert b = if b then () else failwith "Assertion failed"
let print_endline s = print_string s; print_newline ()
let print_int n = print_string (string_of_int n)
let string_of_bool b = if b then "true" else "false"
let string_of_float x =
  if float_of_int (int_of_float x) = x then string_of_int (int_of_float x) ^ "." else __number_to_string x
let print_float x = print_string (string_of_float x)
let floor x = let t = float_of_int (int_of_float x) in if t > x then t -. 1.0 else t
let ceil x = let t = float_of_int (int_of_float x) in if t < x then t +. 1.0 else t
let sqrt x =
  if x <= 0.0 then 0.0
  else let rec go g n = if n = 0 then g else go ((g +. x /. g) /. 2.0) (n - 1) in go (x /. 2.0 +. 0.5) 60
let Fun.id x = x
let Fun.const a _ = a
let Fun.flip f a b = f b a

(* Printf 的格式化輔助 *)
let rec __repeat n s = if n <= 0 then "" else s ^ __repeat (n - 1) s
let __pad_left w c s = let k = w - String.length s in if k > 0 then __repeat k c ^ s else s
let __pad_right w s = let k = w - String.length s in if k > 0 then s ^ __repeat k " " else s
let rec __pow10 n = if n <= 0 then 1.0 else 10.0 *. __pow10 (n - 1)
let __fmt_float prec x =
  let neg = x < 0.0 in
  let ax = if neg then 0.0 -. x else x in
  let scale = __pow10 prec in
  let r = int_of_float (ax *. scale +. 0.5) in
  let s = int_of_float scale in
  let body =
    if prec = 0 then string_of_int r
    else string_of_int (r / s) ^ "." ^ __pad_left prec "0" (string_of_int (r mod s)) in
  if neg && r <> 0 then "-" ^ body else body

(* List *)
let rec List.map f l = match l with [] -> [] | x :: xs -> let y = f x in y :: List.map f xs
let List.mapi f l =
  let rec go i l = match l with [] -> [] | x :: xs -> let y = f i x in y :: go (i + 1) xs in
  go 0 l
let rec List.iter f l = match l with [] -> () | x :: xs -> f x; List.iter f xs
let List.iteri f l =
  let rec go i l = match l with [] -> () | x :: xs -> f i x; go (i + 1) xs in
  go 0 l
let rec List.fold_left f acc l = match l with [] -> acc | x :: xs -> List.fold_left f (f acc x) xs
let rec List.fold_right f l acc = match l with [] -> acc | x :: xs -> f x (List.fold_right f xs acc)
let rec List.filter p l =
  match l with [] -> [] | x :: xs -> if p x then x :: List.filter p xs else List.filter p xs
let rec List.exists p l = match l with [] -> false | x :: xs -> p x || List.exists p xs
let rec List.for_all p l = match l with [] -> true | x :: xs -> p x && List.for_all p xs
let rec List.mem x l = match l with [] -> false | y :: ys -> x = y || List.mem x ys
let rec List.nth l n =
  match l with [] -> failwith "List.nth" | x :: xs -> if n = 0 then x else List.nth xs (n - 1)
let List.append a b = a @ b
let rec List.concat ls = match ls with [] -> [] | l :: rest -> l @ List.concat rest
let List.flatten ls = List.concat ls
let List.concat_map f l = List.concat (List.map f l)
let rec List.assoc k l =
  match l with [] -> failwith "Not_found" | (a, b) :: rest -> if a = k then b else List.assoc k rest
let rec List.assoc_opt k l =
  match l with [] -> None | (a, b) :: rest -> if a = k then Some b else List.assoc_opt k rest
let rec List.find_opt p l =
  match l with [] -> None | x :: xs -> if p x then Some x else List.find_opt p xs
let List.find p l = match List.find_opt p l with Some x -> x | None -> failwith "Not_found"
let List.partition p l =
  let rec go l yes no =
    match l with [] -> (List.rev yes, List.rev no) | x :: xs -> if p x then go xs (x :: yes) no else go xs yes (x :: no) in
  go l [] []
let rec List.combine a b =
  match a, b with [], [] -> [] | x :: xs, y :: ys -> (x, y) :: List.combine xs ys | _ -> failwith "List.combine"
let rec List.split l =
  match l with [] -> ([], []) | (a, b) :: rest -> let (xs, ys) = List.split rest in (a :: xs, b :: ys)
let rec List.map2 f a b =
  match a, b with [], [] -> [] | x :: xs, y :: ys -> let z = f x y in z :: List.map2 f xs ys | _ -> failwith "List.map2"
let List.init n f =
  let rec go i = if i >= n then [] else let y = f i in y :: go (i + 1) in
  go 0
let List.filter_map f l =
  let rec go l = match l with [] -> [] | x :: xs -> (match f x with None -> go xs | Some y -> y :: go xs) in
  go l
let rec __take n l = if n <= 0 then [] else match l with [] -> [] | x :: xs -> x :: __take (n - 1) xs
let rec __drop n l = if n <= 0 then l else match l with [] -> [] | _ :: xs -> __drop (n - 1) xs
let rec __merge cmp a b =
  match a, b with
  | [], _ -> b
  | _, [] -> a
  | x :: xs, y :: ys -> if cmp x y <= 0 then x :: __merge cmp xs b else y :: __merge cmp a ys
let rec List.sort cmp l =
  let n = List.length l in
  if n < 2 then l
  else let h = n / 2 in __merge cmp (List.sort cmp (__take h l)) (List.sort cmp (__drop h l))

(* Option / String *)
let Option.map f o = match o with None -> None | Some x -> Some (f x)
let Option.bind o f = match o with None -> None | Some x -> f x
let Option.value o d = match o with None -> d | Some x -> x
let Option.get o = match o with Some x -> x | None -> failwith "Option.get"
let Option.is_some o = match o with None -> false | Some _ -> true
let Option.is_none o = match o with None -> true | Some _ -> false
let rec String.concat sep l =
  match l with [] -> "" | [x] -> x | x :: xs -> x ^ sep ^ String.concat sep xs
`;

/* ═════════════════════════ 組裝與編譯 ═════════════════════════ */
let PRELUDE_ITEMS = [];
function scanStrings(x, cb) {
  if (typeof x === 'string') cb(x); else if (Array.isArray(x)) x.forEach(y => scanStrings(y, cb));
}

function setup() {
  resetTypeState(); GC = new Map(); USER_DEFS = new Map(); PRELUDE_ITEMS = []; tmpN = 0;
  GT.set('Printf.printf', { special: 'printf' }); GT.set('Printf.sprintf', { special: 'sprintf' });
  GC.set('Printf.printf', { special: 'printf' }); GC.set('Printf.sprintf', { special: 'sprintf' });
  for (const [n, f] of RUNTIME_HELPERS) PRELUDE_ITEMS.push({ defines: [n], forms: [f] });
  IN_PRELUDE = true;
  for (const item of new Parser(lex(PRELUDE)).parseProgram()) {
    try { checkItem(item); } catch (e) { if (e instanceof MLError) throw new Error('[prelude] ' + e.message); throw e; }
    const forms = genItem(item);
    if (forms.length) PRELUDE_ITEMS.push({ defines: forms.map(f => f[1]), forms });
  }
  IN_PRELUDE = false;
}

function translate(src, opts = {}) {
  setup();
  const items = new Parser(lex(src)).parseProgram();
  const forms = [], types = [];
  for (const item of items) {
    if (!opts.noCheck) checkItem(item);
    forms.push(...genItem(item));
    if (item.t === 'let' && item.types) for (const [n, t] of item.types) types.push(`val ${n} : ${showType(t)}`);
  }
  // 依賴分析: 只輸出用到的 prelude 項目
  const defOf = new Map();
  PRELUDE_ITEMS.forEach((it, i) => it.defines.forEach(n => defOf.set(n, i)));
  const need = new Set(), work = [];
  const mark = x => scanStrings(x, s => { const i = defOf.get(s); if (i !== undefined && !need.has(i)) { need.add(i); work.push(i); } });
  mark(forms);
  while (work.length) mark(PRELUDE_ITEMS[work.pop()].forms);
  const pre = PRELUDE_ITEMS.filter((_, i) => need.has(i)).flatMap(it => it.forms);
  return { scheme: [...pre, ...forms].map(show).join('\n') + '\n', types };
}

function compile(src, opts) { return lispc.compile(translate(src, opts).scheme); }
module.exports = { compile, translate };

/* ═════════════════════════ CLI ═════════════════════════ */
if (require.main === module) {
  const args = process.argv.slice(2);
  if (!args.length) { console.error('用法: node mlc.js prog.ml [-o prog.lbc] [--types] [--scheme] [--no-check]'); process.exit(1); }
  const input = args.find((a, i) => !a.startsWith('-') && args[i - 1] !== '-o');
  const oi = args.indexOf('-o');
  const output = oi >= 0 ? args[oi + 1] : input.replace(/\.[^.]*$/, '') + '.lbc';
  try {
    const src = fs.readFileSync(input, 'utf8');
    const r = translate(src, { noCheck: args.includes('--no-check') });
    if (args.includes('--types')) console.log(r.types.join('\n'));
    else if (args.includes('--scheme')) process.stdout.write(r.scheme);
    else { fs.writeFileSync(output, lispc.compile(r.scheme)); console.error(`已編譯 ${input} -> ${output}`); }
  } catch (e) {
    if (e instanceof MLError) { console.error('編譯錯誤: ' + e.message); process.exit(1); }
    console.error('編譯錯誤: ' + e.message); process.exit(1);
  }
}
