#!/usr/bin/env node
'use strict';
/*
 * lean0c.js  —  微型 Lean4 (數學建構 + 定理證明)  ->  LBC v1 中間碼 (經 Scheme 核心 + lispc.js)
 *
 * 用法:  node lean0c.js input.l0 [-o output.lbc]      (-o - 輸出到 stdout)
 *        node lean0c.js input.l0 --elab               印出 elaboration 結果 (除錯)
 *        node vm.js output.lbc
 *
 * ───────────────────────────── 設計 ─────────────────────────────
 *  依賴型別核心: Sort (Prop : Type, Type n : Type (n+1))、Pi (codomain 為 Prop 時仍落 Prop)、
 *  Sigma、Nat (Zero/Succ/字面值/Nat.rec)、Bool (true/false/Bool.rec)、Eq (Eq/subst/rfl)。
 *  沒有 general inductive、沒有 universe 多型；And/Or/Exists/Not/False 皆以 surface def
 *  (impredicative 編碼) 提供；structure 展開為巢狀 Sigma。
 *  tactic: rfl exact apply intro rw simp induction assumption swap。
 *  證明項編譯: Nat.rec -> letrec、NatLit -> 數字、Eq.subst -> 取被代入值、rfl/證明 -> 0。
 *  VM (vm.js / vm2wasm.js) 完全不需修改。
 *
 *  架構 (LCF 式小核心拆分)：可信任的檢查只在 lean0kernel.js
 *  (subst/whnf/defeq/inferK/checkK/checkDef，無 meta、無 I/O)；
 *  本檔是 elaborator (parser、隱式參數/meta 合一、tactic、codegen、命令)，
 *  每存一個定義前以 kernel.checkDef 重查 (不合即內部錯誤)，tactic 證明則存
 *  型別 + 公理依賴。詳見 lean0kernel.js.md。
 *
 * ───────────────────────────── 語法 ─────────────────────────────
 *  版面規則: 頂層命令必須從 col 0 開始；接續行與 tactic 行須縮排。
 *  命令    := "def" 名稱 binders* [":" term] ":=" term
 *           | ("theorem"|"lemma"|"example") [名稱] [":" term] (":=" term | "by" tactics)
 *           | "axiom" 名稱 ":" term
 *           | "structure" 名稱 ":=" binder 行+
 *           | "#check" term | "#eval" term | "#print" "axioms" [名稱]
 *  binder  ::= 名稱 | "(" 名稱+ ":" term ")" | "{" 名稱+ ":" term "}"
 *  term    ::= "fun" binder+ "=>" term | ("forall"|"∀") binder+ "," term
 *            | arrow | eq
 *  arrow   ::= eq ["->" arrow]                    (* 右結合；A -> B 即 Pi _ : A, B *)
 *  eq      ::= add ["=" add]                      (* a = b 即 Eq _ a b *)
 *  add     ::= mul ["+" add] | mul ["*" ...]      (* + 即 Nat.add，* 即 Nat.mul *)
 *  atom    ::= 變數 | 數字 | "(" term ")" | "Prop" | "Type" | "_" | "rfl"
 *              | "Nat" | "Nat.zero" | "Nat.succ" | "Nat.rec"
 *              | "Bool" | "true" | "false" | "Bool.rec"
 *              | "Eq" | "Eq.subst" | "Sigma.mk" | "Sigma.fst" | "Sigma.snd"
 *  tactic  ::= "rfl" | "exact" term | "apply" term | "intro" 名稱+
 *            | "rw" "[" [rwrule {"," rwrule}] "]" | "simp" ["[" term {"," term} "]"]
 *            | "induction" 名稱 | "assumption" | "swap"
 *  rwrule  ::= ["←"] term
 *  tactic 序列以換行或 ";" 分隔 (括號內除外)。
 */
const fs = require('fs');
const lispc = require('./lispc.js');
const vm = require('./vm.js');
const kernel = require('./lean0kernel.js');

class L0Error extends Error {}
const fail = (msg) => { throw new L0Error(msg); };

/* kernel 轉接：項構造子直接共用；whnf/defeq/inferK/sortOfK 經 wrapper 注入 consts 與 flex */
const { K, SORT, fresh, freeVars, subst, piSort } = kernel;
const flex = {
  get: (id) => {
    const v = G.metas.get(id);
    return v === undefined || v === null ? undefined : v;
  },
  set: (id, t) => { G.metas.set(id, t); },
};
const W = (e, full) => kernel.whnf(e, G.consts, !!full, flex);
const D = (a, b, fuel) => kernel.defeq(a, b, G.consts, fuel || 200, flex);
const IK = (e) => kernel.inferK(e, localCtx, G.consts, flex);
const SK = (ty) => kernel.sortOfK(ty, localCtx, G.consts, flex);
const mset = (id, t) => D(K('meta', { id }), t);
function unify(a, b) {
  try { D(a, b); } catch (e) { fail('unify 失敗'); }
}

/* ═════════════════════════ Lexer (含行列) ═════════════════════════ */
function lex(src) {
  const toks = []; let i = 0, line = 1, col = 0; const n = src.length;
  const push = (k, v) => toks.push({ k, v, line, col });
  while (i < n) {
    const c = src[i];
    if (c === '\n') { push('nl', null); line++; col = 0; i++; continue; }
    if (c === ' ' || c === '\t' || c === '\r') { col++; i++; continue; }
    if (c === '-' && src[i + 1] === '-') { while (i < n && src[i] !== '\n') { i++; col++; } continue; }
    const startCol = col;
    const P = (k, v, len) => { push('x', 0); toks[toks.length - 1].k = k; toks[toks.length - 1].v = v; toks[toks.length - 1].col = startCol; i += len; col += len; };
    if (/[0-9]/.test(c)) { const m = /^\d+/.exec(src.slice(i)); P('int', Number(m[0]), m[0].length); continue; }
    if (/[A-Za-z_.]/.test(c) && /[A-Za-z_]/.test(c)) {
      const m = /^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*/.exec(src.slice(i));
      P('id', m[0], m[0].length); continue;
    }
    if (c === '#') {
      const m = /^#[A-Za-z]+/.exec(src.slice(i));
      if (!m) fail(`第 ${line} 行: 無法辨識的字元 "#"`);
      P('id', m[0], m[0].length); continue;
    }
    if (c === '∀' || c === 'λ' || c === '←' || c === '→') { P(c === '∀' ? 'forall' : c === 'λ' ? 'fun' : c === '←' ? 'larr' : 'arrow', c, 1); continue; }
    const two = src.slice(i, i + 2);
    if (two === '->' || two === '=>' || two === ':=') { P(two === '->' ? 'arrow' : two === '=>' ? 'dar' : 'asg', two, 2); continue; }
    if ('=;.,()[]{}+'.includes(c)) { P(c, c, 1); continue; }
    if (c === '*') { P('op', '*', 1); continue; }
    if (c === ':') { P(':', ':', 1); continue; }
    fail(`第 ${line} 行: 無法辨識的字元 "${c}"`);
  }
  push('eof', null);
  return toks;
}

/* ═════════════════════════ Chunker: col 0 開新命令 ═════════════════════════ */
function chunk(src) {
  const lines = src.split('\n'), chunks = [];
  let cur = null;
  lines.forEach((text, idx) => {
    if (!text.trim() || text.trim().startsWith('--')) return;
    const col = text.length - text.trimStart().length;
    if (col === 0) { cur = { lines: [], start: idx + 1 }; chunks.push(cur); }
    if (!cur) fail(`第 ${idx + 1} 行: 頂層命令必須從 col 0 開始`);
    cur.lines.push({ text, line: idx + 1 });
  });
  return chunks.map(c => ({ ...c, src: c.lines.map(l => l.text).join('\n') }));
}

/* ═════════════════════════ Surface Parser ═════════════════════════ */
const S = (t, o) => Object.assign({ t }, o);

class Parser {
  constructor(toks) { this.t = toks.filter(x => x.k !== 'nl'); this.p = 0; }
  peek(k = 0) {
    const i = this.p + k;
    if (i >= this.t.length) return { k: 'eof', v: null, line: -1, col: -1 };
    return this.t[i];
  }
  next() { return this.t[this.p++]; }
  is(v, k = 0) { const t = this.peek(k); return t.k === v || t.v === v; }
  err(m) { const t = this.peek(); fail(`第 ${t.line} 行: ${m}`); }
  expect(v) { if (!this.is(v)) this.err(`語法錯誤: 需要 "${v}"`); return this.next(); }
  expectId() { const t = this.peek(); if (t.k !== 'id') this.err('語法錯誤: 需要名稱'); return this.next(); }

  parseBinder() {
    const t = this.peek();
    if (t.k === 'id' && this.peek(1).v !== ':' && this.peek(1).k !== 'id') { this.next(); return { name: t.v, ty: null, imp: false }; }
    if (t.k === 'id') { this.next(); return { name: t.v, ty: null, imp: false }; }
    if (t.v === '(' || t.v === '{') {
      const imp = t.v === '{'; this.next();
      const names = [];
      while (this.peek().k === 'id') names.push(this.next().v);
      if (!names.length) this.err('binder 需要名稱');
      this.expect(':');
      const ty = this.parseTerm();
      this.expect(imp ? '}' : ')');
      return { names, ty, imp };
    }
    this.err('語法錯誤: 需要 binder');
  }
  parseBinders() {
    const out = [];
    for (;;) {
      const t = this.peek();
      if (t.k === 'id' && this.peek(1).v === ':') {
        const name = this.next().v; this.next();
        out.push({ name, ty: this.parseTerm(), imp: false });
      } else if (t.k === 'id' && ![':=', ':'].includes(this.peek(1).v)) out.push({ name: this.next().v, ty: null, imp: false });
      else if (t.v === '(' || t.v === '{') {
        const b = this.parseBinder();
        if (b.names) for (const name of b.names) out.push({ name, ty: b.ty, imp: b.imp });
        else out.push(b);
      } else break;
    }
    return out;
  }

  parseTerm() { return this.parseFun(); }
  parseFun() {
    let t = this.peek();
    if (t.k === 'id' && (t.v === 'fun' || t.v === 'fun!') || t.k === 'fun') { this.next(); return this.funRest(t); }
    if (t.k === 'id' && t.v === 'forall' || t.k === 'forall') { this.next(); return this.forallRest(); }
    return this.parseArrow();
  }
  funRest(t) {
    const bs = this.parseBinders();
    if (!bs.length) this.err('fun 需要參數');
    this.expect('dar');
    let body = this.parseTerm();
    for (let i = bs.length - 1; i >= 0; i--) body = S('lam', { name: bs[i].name, ty: bs[i].ty, imp: bs[i].imp, body, line: t.line });
    return body;
  }
  forallRest() {
    const bs = this.parseBinders();
    if (!bs.length) this.err('forall 需要參數');
    this.expect(',');
    let body = this.parseTerm();
    for (let i = bs.length - 1; i >= 0; i--) body = S('pi', { name: bs[i].name, dom: bs[i].ty || S('hole', {}), imp: bs[i].imp, body, line: 0 });
    return body;
  }
  parseArrow() {
    const a = this.parseEq();
    if (this.is('arrow')) { this.next(); const b = this.parseArrow(); return S('pi', { name: '_', dom: a, imp: false, body: b, line: 0 }); }
    return a;
  }
  parseEq() {
    const a = this.parseAdd();
    if (this.is('=')) { const l = this.next(); const b = this.parseAdd(); return S('eq', { a, b, line: l.line }); }
    return a;
  }
  parseAdd() {
    let l = this.parseMul();
    if (this.is('+')) { const t = this.next(); l = S('app', { f: S('app', { f: S('var', { name: 'Nat.add', line: t.line }), a: l, line: t.line }), a: this.parseAdd(), line: t.line }); }
    return l;
  }
  parseMul() {
    let l = this.parseApp();
    if (this.peek().k === 'op' && this.peek().v === '*') { const t = this.next(); l = S('app', { f: S('app', { f: S('var', { name: 'Nat.mul', line: t.line }), a: l, line: t.line }), a: this.parseMul(), line: t.line }); }
    return l;
  }
  parseApp() {
    let f = this.parseAtom();
    for (;;) {
      const t = this.peek();
      if (t.k === 'int' || t.k === 'id' || t.v === '(') f = S('app', { f, a: this.parseAtom(), line: 0 });
      else break;
    }
    return f;
  }
  parseAtom() {
    const t = this.next();
    if (t.k === 'int') return S('num', { v: t.v, line: t.line });
    if (t.k === 'id') {
      if (t.v === 'Prop') return S('sort', { u: 0, line: t.line });
      if (t.v === 'Type') return S('sort', { u: 1, line: t.line });
      if (t.v === 'rfl') return S('rfl', { line: t.line });
      if (t.v === '_') return S('hole', { line: t.line });
      return S('var', { name: t.v, line: t.line });
    }
    if (t.v === '(') { const e = this.parseTerm(); this.expect(')'); return e; }
    this.err('語法錯誤: 無法解析的運算式');
  }
}

function splitTactics(toks) {
  const out = []; let cur = [], depth = 0;
  const flush = () => { if (cur.length) out.push(cur); cur = []; };
  for (const t of toks) {
    if (['(', '[', '{'].includes(t.v)) depth++;
    if ([')', ']', '}'].includes(t.v)) depth--;
    if ((t.v === ';' || t.k === 'nl') && depth === 0) flush();
    else cur.push(t);
  }
  flush();
  return out.filter(a => a.length);
}

function parseTac(toks) {
  const p = new Parser(toks);
  const h = p.expectId();
  const R = (t, o) => S(t, o);
  if (h.v === 'rfl') return R('rfl', {});
  if (h.v === 'exact') return R('exact', { e: p.parseTerm() });
  if (h.v === 'apply') return R('apply', { e: p.parseTerm() });
  if (h.v === 'assumption') return R('assumption', {});
  if (h.v === 'swap') return R('swap', {});
  if (h.v === 'intro') {
    const names = [];
    while (p.peek().k === 'id') names.push(p.next().v);
    if (!names.length) fail('intro 需要名稱');
    return R('intro', { names });
  }
  if (h.v === 'induction') return R('induction', { name: p.expectId().v });
  if (h.v === 'rw') {
    p.expect('[');
    const rules = [];
    if (!p.is(']')) {
      for (;;) {
        let rev = false;
        if (p.peek().k === 'larr') { p.next(); rev = true; }
        rules.push({ e: p.parseTerm(), rev });
        if (p.is(',')) { p.next(); continue; }
        break;
      }
    }
    p.expect(']');
    return R('rw', { rules });
  }
  if (h.v === 'simp') {
    const lemmas = [];
    if (p.is('[')) {
      p.next();
      if (!p.is(']')) for (;;) { lemmas.push(p.parseTerm()); if (p.is(',')) { p.next(); continue; } break; }
      p.expect(']');
    }
    return R('simp', { lemmas });
  }
  fail(`未知的 tactic "${h.v}"`);
}

function parseCommand(chunk) {
  const toks = lex(chunk.src);
  const noNl = toks.filter(t => t.k !== 'nl');
  const p = new Parser(noNl);
  const head = p.expectId();
  const line = chunk.start;
  const R = (t, o) => S(t, Object.assign({ line }, o));
  if (head.v === '#check') return R('check', { e: p.parseTerm() });
  if (head.v === '#eval') return R('eval', { e: p.parseTerm() });
  if (head.v === '#print') {
    if (p.expectId().v !== 'axioms') fail('只支援 #print axioms');
    let name = null;
    if (p.peek().k === 'id') name = p.next().v;
    return R('printAx', { name });
  }
  if (head.v === 'axiom') {
    const name = p.expectId().v;
    p.expect(':');
    return R('axiom', { name, ty: p.parseTerm() });
  }
  if (head.v === 'structure') {
    const name = p.expectId().v;
    if (p.is('asg')) p.next();
    const fields = [];
    const rest = noNl.slice(p.p);
    const q = new Parser(rest);
    while (q.peek().k !== 'eof') {
      const b = q.parseBinder();
      if (b.names) for (const n of b.names) fields.push({ name: n, ty: b.ty });
      else fields.push({ name: b.name, ty: b.ty });
    }
    if (!fields.length) fail('structure 需要欄位');
    return R('struct', { name, fields });
  }
  if (['def', 'theorem', 'lemma', 'example'].includes(head.v)) {
    let name = null;
    if (p.peek().k === 'id') name = p.next().v;
    const binders = p.parseBinders();
    let ty = null;
    if (p.is(':')) { p.next(); ty = p.parseTerm(); }
    p.expect('asg');
    if (p.is('id') && p.peek().v === 'by') {
      p.next();
      let seen = 0, si = 0;
      for (; si < toks.length; si++) { if (toks[si].k !== 'nl') seen++; if (seen === p.p) break; }
      const tacs = splitTactics(toks.slice(si + 1)).map(parseTac);
      return R(head.v, { name, binders, ty, tacs });
    }
    return R(head.v, { name, binders, ty, body: p.parseTerm() });
  }
  fail(`第 ${line} 行: 未知的頂層命令 "${head.v}"`);
}

/* ═════════════════════════ Kernel ═════════════════════════ */

;


const G = { consts: new Map(), metas: new Map(), metaN: 0 };
const newMeta = () => { const id = G.metaN++; G.metas.set(id, null); return K('meta', { id }); };
const pruneM = (t) => {
  while (t && t.t === 'meta' && G.metas.get(t.id) !== null && G.metas.get(t.id) !== undefined) t = G.metas.get(t.id);
  return t;
};


/* whnf 有兩檔: lazy (預設, 供 defeq: beta/iota/zeta + 可 beta 的 delta，不動 Pi 值的套用式以保剛性)
   full (供需看穿別名處: 另展開無自由變數的 Pi/Sort 值) */


function inst(e) {
  e = pruneM(e);
  if (!e || typeof e !== 'object') return e;
  if (Array.isArray(e)) return e.map(inst);
  const o = {};
  for (const [k, v] of Object.entries(e)) o[k] = inst(v);
  return o;
}



/* ═════════════════════════ Elaborator ═════════════════════════ */
let localCtx = [];
const lookupLocal = (n) => [...localCtx].reverse().find(e => e.name === n);
const lookupConst = (n) => G.consts.get(n);

const isSort = (t) => { const w = W(inst(t), true); return w && w.t === 'sort' ? w.u : -1; };

function elabInfer(e) {
  switch (e.t) {
    case 'var': {
      const l = lookupLocal(e.name);
      if (l) return inst(l.type);
      if (e.name === 'Nat') return K('nat', {});
      if (e.name === 'Bool') return K('bool', {});
      const c = lookupConst(e.name);
      if (c) {
        if (c.kind === 'axiom' && G._axLog) G._axLog.add(e.name);
        if (c.kind === 'struct') return inst(c.expansion);
        return inst(c.type);
      }
      fail(`第 ${e.line} 行: 未定義 "${e.name}"`);
    }
    case 'num': return K('nat', {});
    case 'hole': return newMeta();
    case 'sort': return SORT(e.u + 1);
    case 'lam': fail(`第 ${e.line} 行: fun 需要期望型別或標註參數`);
    case 'pi': {
      const d = elabType(e.dom);
      const lv = SK(d);
      const nm = e.name === '_' ? fresh('x') : e.name;
      const rv = withLocal(nm, d, () => SK(elabType(e.body)));
      return SORT(piSort(lv, rv));
    }
    case 'app': return elabApp(e, null).ty;
    case 'eq': {
      const ka = elabTerm(e.a);
      const A = IK(ka);
      const b = elabCheck(e.b, A);
      return K('eq', { ty: A, lhs: ka, rhs: b });
    }
    case 'rfl': fail(`第 ${e.line} 行: rfl 需要期望型別`);
    default: fail(`elaborate: 未處理 ${e.t}`);
  }
}

function elabTerm(e) {
  switch (e.t) {
    case 'var': {
      const l = lookupLocal(e.name);
      if (l) return K('var', { name: e.name });
      if (e.name === 'Nat') return K('nat', {});
      if (e.name === 'Bool') return K('bool', {});
      const c = lookupConst(e.name);
      if (c) {
        if (c.kind === 'axiom' && G._axLog) G._axLog.add(e.name);
        if (c.kind === 'struct') return inst(c.expansion);
        return K('const', { name: e.name });
      }
      fail(`第 ${e.line} 行: 未定義 "${e.name}"`);
    }
    case 'num': return K('natlit', { v: e.v });
    case 'hole': return newMeta();
    case 'sort': return SORT(e.u);
    case 'lam': {
      const nm = e.name === '_' ? fresh('x') : e.name;
      const dom = e.ty ? elabType(e.ty) : newMeta();
      const body = withLocal(nm, dom, () => elabTerm(e.body));
      return K('lam', { name: nm, dom, body });
    }
    case 'pi': {
      const nm = e.name === '_' ? fresh('x') : e.name;
      const d = elabType(e.dom);
      const body = withLocal(nm, d, () => elabType(e.body));
      return K('pi', { name: nm, info: e.imp ? 'imp' : 'exp', dom: d, body });
    }
    case 'app': return elabApp(e, null).tm;
    case 'eq': {
      const ka = elabTerm(e.a);
      const A = IK(ka);
      return K('eq', { ty: A, lhs: ka, rhs: elabCheck(e.b, A) });
    }
    case 'rfl': return K('refl', {});
    default: fail(`elabTerm: 未處理 ${e.t}`);
  }
}

/* kernel 項的型別推論 (供 sortOf / 單遍 elaboration；僅用於已檢查過的項) */
/* Pi/Sigma 形成規則：codomain 為 Prop 必落 Prop (impredicative)；否則取 max；定義域未知且 codomain 非 Prop 則報錯 */
/* elaboration 成 kernel 後驗證形狀確為型別；含未定元則放行，由命令結束時的歧義檢查把關 */
function elabType(surface) {
  const k = elabCheck(surface, null);
  const w = W(inst(k));
  const okShape = w && ['sort', 'pi', 'sigma', 'nat', 'bool', 'eq', 'const', 'var', 'meta', 'app'].includes(w.t);
  if (!okShape) fail('此處應為型別');
  return k;
}

function withLocal(name, type, fn) {
  localCtx.push({ name, type });
  try { return fn(); } finally { localCtx.pop(); }
}

function elabCheck(e, expected, isType = false) {
  if (e.t === 'lam' && expected) {
    const w = W(inst(expected), true);
    if (w.t !== 'pi') {
      fail(`第 ${e.line} 行: fun 的期望型別不是 Pi`);
    }
    const nm = e.name === '_' ? fresh('x') : e.name;
    const dom = e.ty ? elabCheck(e.ty, w.dom) : w.dom;
    try { D(dom, w.dom); } catch (err) { fail(`第 ${e.line} 行: 參數型別不符`); }
    const body = withLocal(nm, dom, () => elabCheck(e.body, inst(subst(w.body, w.name, K('var', { name: nm })))));
    return K('lam', { name: nm, dom, body });
  }
  if (e.t === 'num' && expected) {
    const w = W(inst(expected), true);
    if (w.t === 'meta') { mset(w.id, K('nat', {})); return K('natlit', { v: e.v }); }
    if (!(w.t === 'nat' || (w.t === 'const' && w.name === 'Nat'))) fail(`第 ${e.line} 行: 數字需要 Nat 型別`);
    return K('natlit', { v: e.v });
  }
  if (e.t === 'rfl' && expected) {
    const w = W(inst(expected), true);
    if (w.t !== 'eq') fail(`第 ${e.line} 行: rfl 需要 Eq 型別`);
    try { D(w.lhs, w.rhs); } catch (err) { fail(`第 ${e.line} 行: rfl 兩邊定義上不相等`); }
    return K('refl', {});
  }
  if (e.t === 'hole' && expected) return newMeta();
  if (e.t === 'app') return elabApp(e, expected).tm;
  if (expected) {
    const inferred = elabInfer(e);
    const wExp = W(inst(expected));
    const wInf = W(inst(inferred));
    if (wExp.t === 'sort' && wInf.t !== 'sort') {
      let u = -1;
      try { u = SK(inferred); } catch (err) { fail(`第 ${e.line} 行: 此處應為型別`); }
      if (u !== -1 && u !== null && u > wExp.u) fail(`第 ${e.line} 行: universe 不合 (需要 ${showK(expected)})`);
    } else {
      try { D(inferred, expected); } catch (err) {
        fail(`第 ${e.line} 行: 型別不符 ${err.message}`);
      }
    }
  }
  return elabTerm(e);
}

function elabApp(e, expected) {
  let f = e.f, args = [];
  while (f.t === 'app') { args.unshift(f.a); f = f.f; }
  args.push(e.a);
  if (f.t === 'var' && ['Nat.rec', 'Bool.rec', 'Eq.subst'].includes(f.name)) return elabRecursor(f.name, args, expected, e.line);
  let fty = elabInfer(f);
  let fterm = elabTerm(f);
  const argv = [];
  const deferredRfl = [];
  for (const a of args) {
    fty = W(inst(fty), true);
    while (fty.t === 'pi' && fty.info === 'imp') {
      const m = newMeta();
      fterm = K('app', { f: fterm, a: m });
      fty = W(inst(subst(fty.body, fty.name, m)), true);
    }
    if (fty.t !== 'pi') fail(`第 ${e.line} 行: 參數太多 (非函數被套用)`);
    if (a.t === 'rfl' && W(inst(fty.dom)).t !== 'eq') {
      const m = newMeta();
      const dom = fty.dom;
      argv.push(m);
      fterm = K('app', { f: fterm, a: m });
      fty = W(inst(subst(fty.body, fty.name, m)));
      deferredRfl.push({ m, dom, line: a.line });
      continue;
    }
    const av = elabCheck(a, fty.dom);
    argv.push(av);
    fterm = K('app', { f: fterm, a: av });
    fty = W(inst(subst(fty.body, fty.name, av)));
  }
  while (fty.t === 'pi' && fty.info === 'imp') {
    const m = newMeta();
    fterm = K('app', { f: fterm, a: m });
    fty = W(inst(subst(fty.body, fty.name, m)), true);
  }
  if (expected) {
    const wExp = W(inst(expected));
    const wInf = W(inst(fty));
    if (wExp.t === 'sort' && wInf.t !== 'sort') {
      let u = -1;
      try { u = SK(fty); } catch (err) { fail(`第 ${e.line} 行: 此處應為型別`); }
      if (u !== -1 && u !== null && u > wExp.u) fail(`第 ${e.line} 行: universe 不合`);
    } else {
      try { D(fty, expected); } catch (err) {
        fail(`第 ${e.line} 行: 回傳型別不符`);
      }
    }
  }
  for (const d of deferredRfl) {
    const dd = W(inst(d.dom));
    if (dd.t !== 'eq') fail(`第 ${d.line} 行: rfl 需要 Eq 型別`);
    try { D(dd.lhs, dd.rhs); } catch (err) { fail(`第 ${d.line} 行: rfl 兩邊定義上不相等`); }
    mset(d.m.id, K('refl', {}), 200);
  }
  return { ty: fty, tm: fterm };
}

function elabRecursor(name, args, expected, line) {
  const natTy = K('nat', {}), boolTy = K('bool', {});
  const checkMotive = (motive, domTy, what) => {
    motive = pruneM(inst(motive));
    if (!motive || motive.t !== 'lam') fail(`第 ${line} 行: ${what} motive 必須是 fun`);
    try { D(motive.dom, domTy); } catch (err) { fail(`第 ${line} 行: ${what} motive 定義域不符`); }
    const mv = fresh('m');
    let bs = -1;
    try { bs = withLocal(mv, motive.dom, () => SK(inst(subst(motive.body, motive.name, K('var', { name: mv }))))) ; } catch (e) { bs = -1; }
    if (bs < 0) fail(`第 ${line} 行: ${what} motive 值域須為 Sort`);
    return K('pi', { name: motive.name, info: 'exp', dom: motive.dom, body: motive.body });
  };
  if (name === 'Nat.rec') {
    if (args.length !== 4) fail(`第 ${line} 行: Nat.rec 需要 4 個參數 (motive zero succ target)`);
    const motive = elabTerm(args[0]);
    const mty = checkMotive(motive, natTy, 'Nat.rec');
    const M = (x) => inst(subst(mty.body, mty.name, x));
    const zero = elabCheck(args[1], M(K('zero', {})));
    const kn = fresh('n'), ihn = fresh('ih');
    const sk = K('pi', { name: kn, info: 'exp', dom: natTy, body: K('pi', { name: ihn, info: 'exp', dom: M(K('var', { name: kn })), body: M(K('succ', { p: K('var', { name: kn }) })) }) });
    const succ = elabCheck(args[2], sk);
    const target = elabCheck(args[3], natTy);
    const res = M(target);
    if (expected) { try { D(res, expected); } catch (err) { fail(`第 ${line} 行: Nat.rec 結果型別不符`); } }
    return { ty: res, tm: K('natrec', { motive, zero, succ, target }) };
  }
  if (name === 'Bool.rec') {
    if (args.length !== 4) fail(`第 ${line} 行: Bool.rec 需要 4 個參數`);
    const motive = elabTerm(args[0]);
    const mty = checkMotive(motive, boolTy, 'Bool.rec');
    const M = (x) => inst(subst(mty.body, mty.name, x));
    const tt = elabCheck(args[1], M(K('true', {})));
    const ff = elabCheck(args[2], M(K('false', {})));
    const target = elabCheck(args[3], boolTy);
    const res = M(target);
    if (expected) { try { D(res, expected); } catch (err) { fail(`第 ${line} 行: Bool.rec 結果型別不符`); } }
    return { ty: res, tm: K('boolrec', { motive, tt, ff, target }) };
  }
  if (name === 'Eq.subst') {
    if (args.length < 2) fail(`第 ${line} 行: Eq.subst 需要 motive、等式證明與值`);
    const rest = [...args];
    let Pm = null, A = newMeta();
    if (rest.length > 2) {
      const Am = newMeta(), Sm = newMeta();
      const Pm0 = elabCheck(rest.shift(), K('pi', { name: '_', info: 'exp', dom: Am, body: Sm }));
      const unw = W(pruneM(inst(Pm0)));
      if (!unw || unw.t !== 'lam') fail(`第 ${line} 行: Eq.subst motive 必須是 fun`);
      Pm = unw;
      A = unw.dom;
      const mv = fresh('m');
      let bs = -1;
      try { bs = withLocal(mv, A, () => SK(inst(subst(unw.body, unw.name, K('var', { name: mv }))))) ; } catch (e) { bs = -1; }
      if (bs < 0) fail(`第 ${line} 行: Eq.subst motive 值域須為 Sort`);
    } else fail(`第 ${line} 行: Eq.subst 需要寫明 motive (如 Eq.subst (fun z => ...) h v)`);
    const aM = newMeta(), bM = newMeta();
    const eTm = elabCheck(rest.shift(), K('eq', { ty: A, lhs: aM, rhs: bM }));
    const A2 = inst(A), a = inst(aM), b = inst(bM);
    const hTm = elabCheck(rest.shift(), K('app', { f: Pm, a }));
    if (rest.length) fail(`第 ${line} 行: Eq.subst 參數太多`);
    const res = K('app', { f: Pm, a: b });
    if (expected) { try { D(res, expected); } catch (err) { fail(`第 ${line} 行: Eq.subst 結果型別不符`); } }
    return { ty: res, tm: K('eqrec', { motive: Pm, h: hTm, target: eTm }) };
  }
  fail('unknown recursor');
}

/* ═════════════════════════ Kernel 常數型別 ═════════════════════════ */
function kernelConsts() {
  const natTy = K('nat', {}), boolTy = K('bool', {});
  const def = (name, type, value, kind) => G.consts.set(name, { type, value: value || null, kind: kind || 'def', axioms: new Set() });
  def('Prop', SORT(1), null, 'sort');
  def('Type', SORT(2), null, 'sort');
  def('Nat', SORT(1), null, 'type');
  def('Nat.zero', natTy, K('zero', {}), 'ctor');
  def('Nat.succ', K('pi', { name: 'n', info: 'exp', dom: natTy, body: natTy }), K('lam', { name: 'n', dom: natTy, body: K('succ', { p: K('var', { name: 'n' }) }) }), 'ctor');
  def('Nat.rec', K('pi', { name: 'motive', info: 'exp', dom: K('pi', { name: '_', info: 'exp', dom: natTy, body: SORT(1) }), body: natTy }), null, 'rec');
  def('Bool', SORT(1), null, 'type');
  def('Bool.true', boolTy, K('true', {}), 'ctor');
  def('Bool.false', boolTy, K('false', {}), 'ctor');
  def('Bool.rec', boolTy, null, 'rec');
  def('Eq', K('pi', { name: 'A', info: 'imp', dom: SORT(1), body: K('pi', { name: 'a', info: 'exp', dom: K('var', { name: 'A' }), body: K('pi', { name: 'b', info: 'exp', dom: K('var', { name: 'A' }), body: SORT(0) }) }) }), null, 'type');
  def('Eq.subst', SORT(1), null, 'rec');
  def('rfl', SORT(0), null, 'ctor');
  def('Sigma', K('pi', { name: 'A', info: 'exp', dom: SORT(1), body: K('pi', { name: 'B', info: 'exp', dom: K('pi', { name: '_', info: 'exp', dom: K('var', { name: 'A' }), body: SORT(1) }), body: SORT(1) }) }), null, 'type');
  def('Sigma.mk', SORT(1), null, 'ctor');
  def('Sigma.fst', SORT(1), null, 'ctor');
  def('Sigma.snd', SORT(1), null, 'ctor');
}

/* ═════════════════════════ Prelude (surface) ═════════════════════════ */
const PRELUDE_SRC = `
def True : Prop := forall C : Prop, C -> C
def True.intro : True := fun C h => h
def False : Prop := forall C : Prop, C
def False.elim (C : Prop) (h : False) : C := h C
def Not (A : Prop) : Prop := A -> False
def And (A B : Prop) : Prop := forall C : Prop, (A -> B -> C) -> C
def And.intro {A B : Prop} (a : A) (b : B) : And A B := fun C h => h a b
def And.left {A B : Prop} (h : And A B) : A := h A (fun a b => a)
def And.right {A B : Prop} (h : And A B) : B := h B (fun a b => b)
def Or (A B : Prop) : Prop := forall C : Prop, (A -> C) -> (B -> C) -> C
def Or.inl {A B : Prop} (a : A) : Or A B := fun C h1 h2 => h1 a
def Or.inr {A B : Prop} (b : B) : Or A B := fun C h1 h2 => h2 b
def Exists (A : Type) (P : A -> Prop) : Prop := forall C : Prop, (forall x, P x -> C) -> C
def Exists.intro {A : Type} {P : A -> Prop} (x : A) (h : P x) : Exists A P := fun C k => k x h
def Nat.add (n m : Nat) : Nat := Nat.rec (fun _ => Nat) m (fun _ r => Nat.succ r) n
def Nat.mul (n m : Nat) : Nat := Nat.rec (fun _ => Nat) 0 (fun _ r => Nat.add m r) n
def Eq.symm {A : Type} {x y : A} (h : x = y) : y = x := Eq.subst (fun z => z = x) h rfl
def Eq.trans {A : Type} {x y z : A} (h1 : x = y) (h2 : y = z) : x = z := Eq.subst (fun w => x = w) h2 h1
def congrArg {A B : Type} (f : A -> B) {x y : A} (h : x = y) : f x = f y := Eq.subst (fun z => f x = f z) h rfl
`;

/* ═════════════════════════ Tactics ═════════════════════════ */
function goalType(g) { return inst(g.goal); }
function tryRfl(g) {
  const w = W(goalType(g), true);
  if (w.t !== 'eq') return false;
  try { D(w.lhs, w.rhs); return true; } catch (e) { return false; }
}
function runTac(tac, goals) {
  if (!goals.length) fail('沒有剩餘 goal');
  const save = localCtx;
  localCtx = [...goals[0].locals];
  try {
    return runTacInner(tac, goals);
  } finally {
    localCtx = save;
  }
}
function runTacInner(tac, goals) {
  const g = goals[0], rest = goals.slice(1);
  const R = (...gs) => [...gs, ...rest];
  switch (tac.t) {
    case 'rfl': {
      const w = W(goalType(g));
      if (w.t !== 'eq') fail('rfl: goal 不是等式');
      try { D(w.lhs, w.rhs); } catch (e) {
        fail(`rfl 失敗: 兩邊定義上不相等`);
      }
      return rest;
    }
    case 'exact': {
      elabCheck(tac.e, goalType(g));
      return rest;
    }
    case 'apply': {
      const fty = elabInfer(tac.e);
      let t = W(inst(fty));
      while (t.t === 'pi' && t.info === 'imp') t = W(inst(subst(t.body, t.name, newMeta())));
      const premises = [];
      t = W(inst(t));
      while (t.t === 'pi') {
        if (t.info === 'imp') { t = W(inst(subst(t.body, t.name, newMeta()))); continue; }
        const m = newMeta();
        premises.push({ dom: t.dom, meta: m });
        t = W(inst(subst(t.body, t.name, m)));
      }
      try { unify(t, goalType(g)); } catch (e) { fail(`apply 失敗: 結論無法合一`); }
      const newGoals = [];
      for (const p of premises) {
        const d = inst(p.dom);
        let s = -1;
        try { s = SK(d); } catch (e) { s = -1; }
        if (s >= 0) newGoals.push({ locals: g.locals, goal: d });
        else if (pruneM(p.meta).t === 'meta') fail('apply 失敗: 無法推斷隱含參數');
      }
      return R(...newGoals);
    }
    case 'intro': {
      let cur = g;
      const gs = [];
      void gs;
      for (const name of tac.names) {
        const w = W(goalType(cur), true);
        if (w.t !== 'pi') fail(`intro 失敗: goal 不是 Pi/forall`);
        cur = { locals: [...cur.locals, { name, type: w.dom }], goal: inst(subst(w.body, w.name, K('var', { name }))) };
      }
      return R(cur);
    }
    case 'assumption': {
      for (const l of [...g.locals].reverse()) {
        try { D(l.type, goalType(g)); return rest; } catch (e) { void e; }
      }
      fail('assumption 失敗: 上下文無符合者');
    }
    case 'swap': {
      if (goals.length < 2) fail('swap 需要至少兩個 goal');
      return [goals[1], goals[0], ...goals.slice(2)];
    }
    case 'rw': {
      let cur = goalType(g);
      for (const r of tac.rules) {
        const ht = W(elabInfer(r.e), true);
        let t = ht;
        while (t.t === 'pi') t = W(inst(subst(t.body, t.name, newMeta())));
        if (t.t !== 'eq') fail('rw 需要等式');
        let lhs = inst(t.lhs), rhs = inst(t.rhs);
        if (r.rev) { const tmp = lhs; lhs = rhs; rhs = tmp; }
        cur = rewriteOnce(cur, lhs, rhs, tac);
      }
      const w = W(cur, true);
      if (w.t === 'eq') { try { D(w.lhs, w.rhs); return rest; } catch (e) { void e; } }
      return R({ locals: g.locals, goal: cur });
    }
    case 'simp': {
      let cur = goalType(g);
      for (let round = 0; round < 64; round++) {
        let changed = false;
        for (const l of tac.lemmas) {
          const ht = W(elabInfer(l), true);
          let t = ht;
          while (t.t === 'pi') t = W(inst(subst(t.body, t.name, newMeta())));
          if (t.t !== 'eq') fail('simp 需要等式引理');
          try {
            const n2 = rewriteOnce(cur, inst(t.lhs), inst(t.rhs), tac);
            if (JSON.stringify(inst(n2)) !== JSON.stringify(inst(cur))) { cur = n2; changed = true; }
          } catch (e) { void e; }
        }
        if (!changed) break;
      }
      const w = W(cur, true);
      if (w.t === 'eq') { try { D(w.lhs, w.rhs); return rest; } catch (e) { void e; } }
      return R({ locals: g.locals, goal: cur });
    }
    case 'induction': {
      const idx = g.locals.findIndex(l => l.name === tac.name);
      if (idx < 0) fail(`induction: 上下文無 "${tac.name}"`);
      const nt = W(g.locals[idx].type, true);
      if (nt.t !== 'nat') fail('induction 只能對 Nat (需先 intro 到上下文)');
      const before = g.locals.slice(0, idx);
      const reverted = g.locals.slice(idx);
      let motive = goalType(g);
      for (let i = reverted.length - 1; i >= 0; i--) motive = K('pi', { name: reverted[i].name, info: 'exp', dom: reverted[i].type, body: motive });
      if (motive.t !== 'pi') fail('induction 內部錯誤');
      let mBase = inst(subst(motive.body, motive.name, K('zero', {})));
      const k = fresh('k'), ih = fresh('ih');
      const mAt = (n) => inst(subst(motive.body, motive.name, n));
      let mStep = K('pi', { name: ih, info: 'exp', dom: mAt(K('var', { name: k })), body: mAt(K('succ', { p: K('var', { name: k }) })) });
      for (let i = reverted.length - 1; i >= 1; i--) mStep = K('pi', { name: reverted[i].name, info: 'exp', dom: reverted[i].type, body: mStep });
      mStep = K('pi', { name: k, info: 'exp', dom: K('nat', {}), body: mStep });
      return R({ locals: before, goal: mBase }, { locals: before, goal: mStep });
    }
    default: fail(`未知的 tactic`);
  }
}
function rewriteOnce(term, lhs, rhs, tac) {
  void tac;
  term = inst(term);
  let matched = false;
  const go = (x) => {
    x = inst(x);
    const save = new Map(G.metas);
    try {
      D(x, lhs);
      matched = true;
      return inst(rhs);
    } catch (e) {
      G.metas = save;
    }
    if (!x || typeof x !== 'object') return x;
    const w = W(x);
    if (['var', 'const', 'sort', 'zero', 'true', 'false', 'refl', 'natlit', 'meta'].includes(w.t)) return x;
    const o = Array.isArray(w) ? [] : {};
    for (const [k, v] of Object.entries(w)) o[k] = v && typeof v === 'object' ? go(v) : v;
    return o;
  };
  const out = go(term);
  if (!matched) fail('rw: 找不到可改寫的子項');
  return out;
}

/* ═════════════════════════ Commands ═════════════════════════ */
const OUT = [];
const emitScheme = [];
const progDefs = [];

function elabBinders(binders, fn) {
  const flat = [];
  for (const b of binders) {
    if (b.names) for (const n of b.names) flat.push({ name: n, ty: b.ty, imp: b.imp });
    else flat.push(b);
  }
  const go = (i) => {
    if (i >= flat.length) return fn();
    const b = flat[i];
    const ty = b.ty ? elabType(b.ty) : newMeta();
    const nm = b.name === '_' ? fresh('x') : b.name;
    return withLocal(nm, ty, () => ({ name: nm, ty, rest: go(i + 1), imp: b.imp }));
  };
  return go(0);
}
function collectPis(r) {
  const ps = [];
  let cur = r;
  while (cur && cur.rest) { ps.push(cur); cur = cur.rest; }
  return { params: ps, body: cur };
}
function axiomsIn(e, acc = new Set()) {
  e = pruneM(inst(e));
  if (!e || typeof e !== 'object') return acc;
  if (e.t === 'const') {
    const c = G.consts.get(e.name);
    if (c && c.kind === 'axiom') acc.add(e.name);
  }
  for (const v of Object.values(e)) if (v && typeof v === 'object') axiomsIn(v, acc);
  return acc;
}

function doCommand(cmd) {
  const label = cmd.name || cmd.t;
  try {
    doCommandInner(cmd);
  } catch (e) {
    if (e instanceof L0Error) fail(`${e.message}【於 ${label}】`);
    if (e instanceof kernel.KError) fail(`內部錯誤 (kernel)：${e.message}【於 ${label}】`);
    throw e;
  }
}

function doCommandInner(cmd) {
  if (cmd.t === 'check') {
    const ty = elabInfer(cmd.e);
    OUT.push(`#check : ${showK(inst(ty))}`);
    return;
  }
  if (cmd.t === 'eval') {
    const v = evalKernel(cmd.e);
    OUT.push(`#eval : ${v}`);
    return;
  }
  if (cmd.t === 'printAx') {
    if (cmd.name) {
      const c = G.consts.get(cmd.name);
      if (!c) fail(`未定義 "${cmd.name}"`);
      OUT.push(`#print axioms ${cmd.name} : [${[...(c.axioms || [])].join(', ')}]`);
    } else {
      const all = [...G.consts.entries()].filter(([_, c]) => c.kind === 'axiom').map(([n]) => n);
      OUT.push(`#print axioms : [${all.join(', ')}]`);
    }
    return;
  }
  if (cmd.t === 'axiom') {
    const ty = elabType(cmd.ty);
    G.consts.set(cmd.name, { type: ty, value: null, kind: 'axiom', axioms: new Set([cmd.name]) });
    progDefs.push({ name: cmd.name, type: ty, value: null, kind: 'axiom' });
    return;
  }
  if (cmd.t === 'struct') {
    const fs = cmd.fields.map(f => ({ name: f.name, ty: elabType(f.ty) }));
    if (!fs.length) fail('structure 需要欄位');
    const sName = fresh('s');
    const last = fs.length - 1;
    const projOf = (i) => {
      let p = K('var', { name: sName });
      for (let j = 0; j < i; j++) p = K('snd', { p });
      return i === last ? p : K('fst', { p });
    };
    const typeOf = (i) => {
      let pty = full;
      for (let j = 0; j < i; j++) {
        if (!pty || pty.t !== 'sigma') fail('structure 內部錯誤');
        pty = pty.snd;
      }
      return i === last ? pty : pty.fst;
    };
    if (fs.length === 1) {
      const mkTy = K('pi', { name: fs[0].name, info: 'exp', dom: fs[0].ty, body: fs[0].ty });
      const mkVal = K('lam', { name: fs[0].name, dom: fs[0].ty, body: K('var', { name: fs[0].name }) });
      G.consts.set(cmd.name, { type: SORT(1), value: null, kind: 'struct', axioms: new Set(), expansion: fs[0].ty });
      G.consts.set(cmd.name + '.mk', { type: mkTy, value: mkVal, kind: 'def', axioms: new Set() });
      progDefs.push({ name: cmd.name + '.mk', type: mkTy, value: mkVal, kind: 'def' });
      const realTy = K('pi', { name: sName, info: 'exp', dom: fs[0].ty, body: fs[0].ty });
      const realProj = K('lam', { name: sName, dom: fs[0].ty, body: K('var', { name: sName }) });
      G.consts.set(cmd.name + '.' + fs[0].name, { type: realTy, value: realProj, kind: 'def', axioms: new Set() });
      progDefs.push({ name: cmd.name + '.' + fs[0].name, type: realTy, value: realProj, kind: 'def' });
      return;
    }
    let full = fs[fs.length - 1].ty;
    for (let i = fs.length - 2; i >= 0; i--) full = K('sigma', { name: fs[i].name, fst: fs[i].ty, snd: full });
    G.consts.set(cmd.name, { type: SORT(1), value: null, kind: 'struct', axioms: new Set(), expansion: full });
    let mkTy = full;
    for (let i = fs.length - 1; i >= 0; i--) mkTy = K('pi', { name: fs[i].name, info: 'exp', dom: fs[i].ty, body: mkTy });
    let mkVal = null;
    for (let i = fs.length - 1; i >= 0; i--) mkVal = mkVal ? K('pair', { a: K('var', { name: fs[i].name }), b: mkVal }) : K('var', { name: fs[i].name });
    for (let i = fs.length - 1; i >= 0; i--) mkVal = K('lam', { name: fs[i].name, dom: fs[i].ty, body: mkVal });
    G.consts.set(cmd.name + '.mk', { type: mkTy, value: mkVal, kind: 'def', axioms: new Set() });
    progDefs.push({ name: cmd.name + '.mk', type: mkTy, value: mkVal, kind: 'def' });
    fs.forEach((f, i) => {
      let fty = typeOf(i);
      for (let j = 0; j < i; j++) fty = subst(fty, fs[j].name, projOf(j));
      const realTy = K('pi', { name: sName, info: 'exp', dom: full, body: fty });
      const realProj = K('lam', { name: sName, dom: full, body: projOf(i) });
      G.consts.set(cmd.name + '.' + f.name, { type: realTy, value: realProj, kind: 'def', axioms: new Set() });
      progDefs.push({ name: cmd.name + '.' + f.name, type: realTy, value: realProj, kind: 'def' });
    });
    return;
  }
  const isThm = ['theorem', 'lemma', 'example'].includes(cmd.t);
  G._axLog = new Set();
  const closeOver = (params, ty, val) => {
    for (let i = params.length - 1; i >= 0; i--) {
      ty = K('pi', { name: params[i].name, info: params[i].imp ? 'imp' : 'exp', dom: params[i].ty, body: ty });
      if (val) val = K('lam', { name: params[i].name, dom: params[i].ty, body: val });
    }
    return { ty, val };
  };
  const checkNoStuckMetas = (ty, val) => {
    const bad = [];
    const go = (x) => {
      x = pruneM(inst(x));
      if (!x || typeof x !== 'object') return;
      if (x.t === 'meta') { bad.push(x.id); return; }
      for (const v of Object.values(x)) if (v && typeof v === 'object') go(v);
    };
    go(ty); if (val) go(val);
    if (bad.length) fail(`歧義: 型別含未定元 ?${bad[0]}，請加標註`);
  };
  if (cmd.body) {
    const ev = elabBinders(cmd.binders || [], () => {
      const t2 = cmd.ty ? elabType(cmd.ty) : null;
      const v2 = t2 ? elabCheck(cmd.body, t2) : elabTerm(cmd.body);
      const t3 = t2 || elabInfer(cmd.body);
      return { t: t3, v: v2 };
    });
    const c2 = collectPis(ev);
    const closed = closeOver(c2.params, c2.body.t, c2.body.v);
    checkNoStuckMetas(closed.ty, closed.val);
    const nm0 = cmd.name || fresh('example');
    const ax0 = new Set(G._axLog);
    axiomsIn(closed.val, ax0);
    const sty = inst(closed.ty), sval = closed.val && inst(closed.val);
    let rigid = false;
    try {
      let n = 0, ty = closed.ty;
      for (;;) { const w = W(ty); if (!w || w.t !== 'pi') break; n++; ty = w.body; }
      if (n > 0) { const c = W(ty); rigid = !!c && c.t === 'sort'; }
    } catch (e) { rigid = false; }
    progDefs.push({ name: nm0, type: sty, value: sval, kind: isThm ? 'thm' : 'def' });
    G.consts.set(nm0, { type: sty, value: sval, kind: isThm ? 'thm' : 'def', axioms: ax0, rigid });
    try {
      kernel.checkDef(sty, sval, G.consts);
    } catch (e) {
      G.consts.delete(nm0);
      progDefs.pop();
      if (e instanceof kernel.KError) fail(`kernel 重查失敗 (內部錯誤)：${e.message}`);
      throw e;
    }
    return;
  }
  if (cmd.tacs) {
    const ev = elabBinders(cmd.binders || [], () => {
      const t2 = elabType(cmd.ty);
      let goals = [{ locals: [...localCtx], goal: t2 }];
      for (const t of cmd.tacs) goals = runTac(t, goals);
      if (goals.length) {
        fail(`還有 ${goals.length} 個未解 goal`);
      }
      return { t: t2 };
    });
    const c2 = collectPis(ev);
    const closed = closeOver(c2.params, c2.body.t, null);
    checkNoStuckMetas(closed.ty, null);
    const nm = cmd.name || fresh('example');
    const ax = new Set(G._axLog);
    progDefs.push({ name: nm, type: closed.ty, value: K('refl', {}), kind: 'thm' });
    G.consts.set(nm, { type: closed.ty, value: K('refl', {}), kind: 'thm', axioms: ax });
    return;
  }
}

/* ═════════════════════════ 顯示 ═════════════════════════ */
function showK(e, bound = new Set()) {
  e = pruneM(inst(e));
  if (!e) return '?';
  switch (e.t) {
    case 'var': return e.name;
    case 'const': return e.name;
    case 'meta': return `?${e.id}`;
    case 'sort': return e.u === 0 ? 'Prop' : e.u === 1 ? 'Type' : `Type ${e.u}`;
    case 'nat': return 'Nat';
    case 'bool': return 'Bool';
    case 'zero': return '0';
    case 'true': return 'true';
    case 'false': return 'false';
    case 'refl': return 'rfl';
    case 'natlit': return String(e.v);
    case 'succ': return `(Nat.succ ${showK(e.p)})`;
    case 'lam': return `(fun ${e.name} => ${showK(e.body)})`;
    case 'pi': {
      const arrow = e.name === '_' || bound.has(e.name) && false;
      void arrow;
      if (e.name === '_') return `${showK(e.dom)} -> ${showK(e.body)}`;
      return `∀ ${e.name} : ${showK(e.dom)}, ${showK(e.body)}`;
    }
    case 'sigma': return `Σ ${e.name} : ${showK(e.fst)}, ${showK(e.snd)}`;
    case 'app': return `(${showK(e.f)} ${showK(e.a)})`;
    case 'pair': return `(${showK(e.a)}, ${showK(e.b)})`;
    case 'fst': return `(fst ${showK(e.p)})`;
    case 'snd': return `(snd ${showK(e.p)})`;
    case 'let': return `(let ${e.name} := …)`;
    case 'eq': return `(${showK(e.lhs)} = ${showK(e.rhs)})`;
    case 'natrec': return `(Nat.rec …)`;
    case 'boolrec': return `(Bool.rec …)`;
    case 'eqrec': return `(Eq.subst …)`;
    default: return '?';
  }
}

/* ═════════════════════════ Codegen + #eval ═════════════════════════ */
function showS(x) { return Array.isArray(x) ? '(' + x.map(showS).join(' ') + ')' : String(x); }
const tmpC = { n: 0 };

function genK(e) {
  e = pruneM(inst(e));
  switch (e.t) {
    case 'var': return e.name.replace(/'/g, '_q');
    case 'const': {
      const m = { 'Nat.zero': 0, 'Bool.true': true, 'Bool.false': false, rfl: 0 };
      if (e.name in m) return m[e.name];
      if (['Nat', 'Bool', 'Eq', 'Prop', 'Type', 'Sigma'].includes(e.name)) return 0;
      return e.name.replace(/'/g, '_q').replace(/\./g, '/');
    }
    case 'natlit': return e.v;
    case 'zero': return 0;
    case 'true': return true;
    case 'false': return false;
    case 'refl': return 0;
    case 'succ': return ['+', genK(e.p), 1];
    case 'lam': return ['lambda', [e.name.replace(/'/g, '_q')], genK(e.body)];
    case 'pair': return ['cons', genK(e.a), genK(e.b)];
    case 'fst': return ['car', genK(e.p)];
    case 'snd': return ['cdr', genK(e.p)];
    case 'let': return [['lambda', [e.name.replace(/'/g, '_q')], genK(e.body)], genK(e.val)];
    case 'natrec': {
      const lp = `%lr${tmpC.n++}`;
      return [['lambda', [], ['letrec', [[lp, ['lambda', ['k'],
        ['if', ['=', 'k', 0], genK(e.zero),
          [['lambda', ['kk'], [genK(e.succ), 'kk', [lp, ['-', 'kk', 1]]]], ['-', 'k', 1]]]]]], [lp, genK(e.target)]]]];
    }
    case 'boolrec': return ['if', genK(e.target), genK(e.tt), genK(e.ff)];
    case 'eqrec': return genK(e.h);
    case 'app': {
      const spine = [];
      let h = e;
      while (h.t === 'app') { spine.unshift(h.a); h = pruneM(inst(h.f)); }
      const nm = h.t === 'const' ? h.name : null;
      if (nm === 'Nat.succ' && spine.length === 1) return ['+', genK(spine[0]), 1];
      if (nm === 'Nat.rec' && spine.length === 4) return genK(K('natrec', { motive: spine[0], zero: spine[1], succ: spine[2], target: spine[3] }));
      if (nm === 'Bool.rec' && spine.length === 4) return genK(K('boolrec', { motive: spine[0], tt: spine[1], ff: spine[2], target: spine[3] }));
      if (nm === 'Eq.subst') return genK(spine[spine.length - 1]);
      if (nm === 'Sigma.mk' && spine.length === 2) return ['cons', genK(spine[0]), genK(spine[1])];
      if (nm === 'Sigma.fst' && spine.length === 1) return ['car', genK(spine[0])];
      if (nm === 'Sigma.snd' && spine.length === 1) return ['cdr', genK(spine[0])];
      if (nm === 'Nat.add' && spine.length === 2) {
        const lp = `%la${tmpC.n++}`;
        return [['lambda', [], ['letrec', [[lp, ['lambda', ['a', 'b'], ['if', ['=', 'a', 0], 'b', ['+', 1, [lp, ['-', 'a', 1], 'b']]]]]], [lp, genK(spine[0]), genK(spine[1])]]]];
      }
      if (nm === 'Nat.mul' && spine.length === 2) {
        const lp = `%lm${tmpC.n++}`;
        return [['lambda', [], ['letrec', [[lp, ['lambda', ['a', 'b'], ['if', ['=', 'a', 0], 0, ['+', 'b', [lp, ['-', 'a', 1], 'b']]]]]], [lp, genK(spine[0]), genK(spine[1])]]]];
      }
      let r = genK(h);
      for (const a of spine) r = [r, genK(a)];
      return r;
    }
    case 'pi': case 'sigma': case 'sort': case 'eq': case 'meta': return 0;
    default: return 0;
  }
}

function emitAll() {
  const forms = [];
  for (const d of progDefs) {
    if (d.kind === 'axiom' || !d.value) continue;
    forms.push(['define', d.name.replace(/'/g, '_q').replace(/\./g, '/'), genK(d.value)]);
  }
  return forms.map(showS).join('\n') + '\n';
}

function evalKernel(surface) {
  const ty = elabInfer(surface);
  void ty;
  const tm = elabTerm(surface);
  const scheme = emitAll() + showS(['display', genK(tm)]) + '\n' + showS(['display', '"\\n"']) + '\n';
  const lbc = lispc.compile(scheme);
  const funcs = vm.load(lbc);
  const g = funcs.get('main');
  void g;
  let out = '';
  const w = process.stdout.write.bind(process.stdout);
  process.stdout.write = (c) => { out += c; return true; };
  try { vm.run(funcs); } finally { process.stdout.write = w; }
  return out.trim();
}

/* ═════════════════════════ Main ═════════════════════════ */
function resetAll() {
  G.consts = new Map(); G.metas = new Map(); G.metaN = 0;
  localCtx = []; OUT.length = 0; progDefs.length = 0; tmpC.n = 0;
  kernelConsts();
  for (const ch of chunk(PRELUDE_SRC)) doCommand(parseCommand(ch));
}

function run(src, opts = {}) {
  resetAll();
  const cmds = chunk(src).map(parseCommand);
  for (const c of cmds) doCommand(c);
  const scheme = emitAll();
  return { out: [...OUT], scheme, lbc: lispc.compile(scheme || '(display 0)') };
}

module.exports = { run, toScheme: (s) => run(s).scheme };

/* ═════════════════════════ CLI ═════════════════════════ */
if (require.main === module) {
  const args = process.argv.slice(2);
  if (!args.length) { console.error('用法: node lean0c.js input.l0 [-o output.lbc] [--elab]'); process.exit(1); }
  const input = args.find((a, i) => !a.startsWith('-') && args[i - 1] !== '-o');
  const oi = args.indexOf('-o');
  const output = oi >= 0 ? args[oi + 1] : input.replace(/\.[^.]*$/, '') + '.lbc';
  try {
    const src = fs.readFileSync(input, 'utf8');
    if (args.includes('--elab')) {
      const r = run(src);
      process.stdout.write(r.scheme);
      if (r.out.length) console.error(r.out.join('\n'));
    } else {
      const r = run(src);
      if (r.out.length) console.error(r.out.join('\n'));
      fs.writeFileSync(output, r.lbc);
      console.error(`已編譯 ${input} -> ${output}`);
    }
  } catch (e) {
    if (e instanceof L0Error) { console.error('編譯錯誤: ' + e.message); process.exit(1); }
    if (e instanceof kernel.KError) { console.error('內部錯誤 (kernel): ' + e.message); process.exit(2); }
    console.error('編譯錯誤: ' + e.message); process.exit(1);
  }
}
