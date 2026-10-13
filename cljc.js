#!/usr/bin/env node
'use strict';
/*
 * cljc.js  —  迷你 Clojure  ->  LBC v1 中間碼
 *
 * 用法:  node cljc.js prog.clj [-o prog.lbc]      產生 prog.lbc，用 lispvm.js / vm2wasm.js 執行
 *        node cljc.js prog.clj --scheme            只印出中間產物 (Scheme 核心)，方便除錯
 *
 * 編譯流程:  Clojure --(reader)--> 資料 --(desugar)--> Scheme 核心 --(lispc.js)--> LBC
 * 標準函式庫 (map filter reduce assoc println ...) 是用 Clojure 自己寫的 prelude，
 * 只有程式用到的函式才會被編進輸出 (依賴分析)。VM 與 wasm 不需任何修改。
 *
 * ────────────── 支援的語言 ──────────────
 *  特殊形式  def defn defn- fn (含多元 arity、& rest、遞迴命名 fn) let loop recur if do quote
 *            when when-not if-not if-let when-let cond case and or -> ->> doseq dotimes for
 *            declare ns comment, #(... % %1 %2) 匿名函式, @atom
 *  解構      let / fn / loop / doseq / for 中的 [a b & rest :as all] 與 {:keys [a b] :or {...} :as m}
 *  資料型別  數字、字串、keyword、nil、true/false、list、vector [..]、map {..}
 *  函式庫    first rest next cons conj count nth get assoc dissoc keys vals contains? merge update
 *            get-in assoc-in update-in select-keys zipmap frequencies group-by into vec vector
 *            map mapv filter remove reduce range take drop take-while drop-while concat mapcat
 *            reverse last butlast sort sort-by distinct flatten partition interleave interpose
 *            some every? apply comp partial complement identity constantly str pr-str println
 *            print prn pr atom deref swap! reset! join name keyword ...
 *
 * ────────────── 資料表示 (執行期) ──────────────
 *  nil  = 符號 nil (所以 nil 與 false 都是「假」，與 Clojure 相同；空 list 為真)
 *  vector = (%vec 1 2 3)   map = (%map (k v) ...)   keyword = (%kw "name")   list = 一般 LBC list
 *
 * ────────────── 與真正 Clojure 的差異 ──────────────
 *  - 沒有 lazy seq (map/filter/range 都是 eager，所以沒有 iterate / cycle / 無限 range)
 *  - 沒有巨集 (defmacro)、沒有 set (#{})、沒有 try/catch、沒有 Java interop、沒有 ratio (/ 是浮點除法)
 *  - map 是 association list (O(n))，保持插入順序；vector 是 list，nth / get 為 O(n)
 *  - (str 'sym) 不支援 (VM 沒有 symbol->string)；keyword 的 str / name 沒問題
 *  - recur 僅限尾位置 (與 Clojure 相同，違反時編譯錯誤)
 */
const fs = require('fs');
const path = require('path');
const lispc = require('./lispc.js');

/* ═════════════════════════ Reader ═════════════════════════ */
class Sym { constructor(n) { this.name = n; } }
class Kw { constructor(n) { this.name = n; } }
class Str { constructor(v) { this.v = v; } }
class Vec { constructor(items) { this.items = items; } }
class MapLit { constructor(items) { this.items = items; } }
class SStr { constructor(v) { this.v = v; } }              // Scheme 字串
const sym = n => new Sym(n);

function readAll(src) {
  let i = 0; const n = src.length;
  const isWs = c => c === ',' || /\s/.test(c);
  function skip() {
    for (;;) {
      while (i < n && isWs(src[i])) i++;
      if (src[i] === ';') { while (i < n && src[i] !== '\n') i++; continue; }
      if (src.startsWith('#_', i)) { i += 2; readForm(); continue; }
      break;
    }
  }
  function readSeq(close) {
    const items = [];
    for (;;) {
      skip();
      if (i >= n) throw new Error(`缺少 "${close}"`);
      if (src[i] === close) { i++; return items; }
      items.push(readForm());
    }
  }
  function readString() {
    i++; let s = '';
    while (i < n && src[i] !== '"') {
      if (src[i] === '\\') {
        i++; const e = src[i];
        if (e === 'u') { s += String.fromCharCode(parseInt(src.slice(i + 1, i + 5), 16)); i += 4; }
        else s += e === 'n' ? '\n' : e === 't' ? '\t' : e === 'r' ? '\r' : e;
      } else s += src[i];
      i++;
    }
    if (i >= n) throw new Error('字串沒有結尾的引號');
    i++; return new Str(s);
  }
  function readForm() {
    skip();
    if (i >= n) throw new Error('意外的檔案結尾');
    const c = src[i];
    if (c === '(') { i++; return readSeq(')'); }
    if (c === '[') { i++; return new Vec(readSeq(']')); }
    if (c === '{') {
      i++; const items = readSeq('}');
      if (items.length % 2) throw new Error('map 字面值需要偶數個元素');
      return new MapLit(items);
    }
    if (c === ')' || c === ']' || c === '}') throw new Error(`多餘的 "${c}"`);
    if (c === "'") { i++; return [sym('quote'), readForm()]; }
    if (c === '@') { i++; return [sym('deref'), readForm()]; }
    if (c === '^') { i++; readForm(); return readForm(); }              // 忽略 metadata
    if (c === '`' || c === '~') throw new Error('不支援 syntax-quote / unquote (沒有巨集)');
    if (c === '"') return readString();
    if (c === '#') {
      if (src[i + 1] === '(') { i += 2; return anonFn(readSeq(')')); }
      if (src[i + 1] === '{') throw new Error('不支援 set 字面值 #{}');
      throw new Error('不支援的 reader macro: #' + src[i + 1]);
    }
    let j = i;
    while (j < n && !isWs(src[j]) && !'()[]{}";'.includes(src[j])) j++;
    const tok = src.slice(i, j); i = j;
    if (/^[-+]?\d+$/.test(tok) || /^[-+]?(\d+\.\d*|\.\d+|\d+)([eE][-+]?\d+)?$/.test(tok)) return Number(tok);
    if (/^[-+]?\d+\/\d+$/.test(tok)) throw new Error('不支援 ratio: ' + tok);
    if (tok[0] === ':') { if (tok[1] === ':') throw new Error('不支援 ::keyword'); return new Kw(tok.slice(1)); }
    return sym(tok);
  }
  const forms = [];
  for (;;) { skip(); if (i >= n) break; forms.push(readForm()); }
  return forms;
}

function anonFn(body) {                                    // #(+ % 1)  ->  (fn [p1] (+ p1 1))
  let maxN = 0, rest = false;
  const scan = f => {
    if (f instanceof Sym) {
      if (f.name === '%' || f.name === '%1') maxN = Math.max(maxN, 1);
      else if (f.name === '%&') rest = true;
      else if (/^%[2-9]$/.test(f.name)) maxN = Math.max(maxN, +f.name[1]);
    } else if (Array.isArray(f)) f.forEach(scan);
    else if (f instanceof Vec || f instanceof MapLit) f.items.forEach(scan);
  };
  scan(body);
  const ps = Array.from({ length: maxN }, (_, k) => sym(`p${k + 1}__`));
  const restSym = sym('rest__');
  const rep = f => {
    if (f instanceof Sym) {
      if (f.name === '%' || f.name === '%1') return ps[0];
      if (f.name === '%&') return restSym;
      if (/^%[2-9]$/.test(f.name)) return ps[+f.name[1] - 1];
      return f;
    }
    if (Array.isArray(f)) return f.map(rep);
    if (f instanceof Vec) return new Vec(f.items.map(rep));
    if (f instanceof MapLit) return new MapLit(f.items.map(rep));
    return f;
  };
  return [sym('fn'), new Vec([...ps, ...(rest ? [sym('&'), restSym] : [])]), rep(body)];
}

/* ═════════════════════════ 名稱處理 ═════════════════════════ */
const LBC_PRIMS = new Set(['+', '*', '-', '/', 'quotient', 'remainder', 'modulo', '=', '<', '>', '<=', '>=',
  'abs', 'min', 'max', 'zero?', 'even?', 'odd?', 'not', 'eq?', 'eqv?', 'equal?', 'cons', 'car', 'cdr', 'cadr',
  'cddr', 'caddr', 'list', 'length', 'append', 'reverse', 'null?', 'pair?', 'number?', 'string?', 'symbol?',
  'procedure?', 'string-append', 'string-length', 'number->string', 'display', 'write', 'newline', 'error']);
const SCHEME_KW = ['quote', 'if', 'define', 'set!', 'lambda', 'begin', 'let', 'let*', 'letrec', 'cond', 'and', 'or', 'when', 'unless', 'else'];
const RESERVED = new Set([...LBC_PRIMS, ...SCHEME_KW]);
const ALIAS = { mod: 'modulo', rem: 'remainder', quot: 'quotient', 'fn?': 'procedure?', 'identical?': 'eq?' };
const ident = n => { n = n.replace(/'/g, '_q'); return RESERVED.has(n) ? 'u/' + n : n; };

let CTX = { prelude: false, userGlobals: new Set(), coreNames: new Set() };
let gid = 0;
const tmp = (p = 't') => `%${p}${gid++}`;                    // Scheme 層暫存變數
const gsym = () => sym(`__g${gid++}`);                       // Clojure 層 gensym

class Scope {
  constructor(names = new Set(), recur = null) { this.names = names; this.recur = recur; }
  with(n) { const s = new Set(this.names); s.add(n); return new Scope(s, this.recur); }
  withRecur(r) { return new Scope(this.names, r); }
}

function resolveName(name, sc) {
  if (name.startsWith('%') && name.length > 1) return name.slice(1);           // %cons -> 原始 LBC 內建函式
  if (sc.names.has(name)) return ident(name);
  if (name.startsWith('core/')) return name;
  if (name.length > 1 && name.includes('/')) name = name.slice(name.lastIndexOf('/') + 1);   // str/join -> join
  if (CTX.userGlobals.has(name)) return ident(name);
  if (CTX.coreNames.has(name)) return 'core/' + name;
  if (ALIAS[name]) return ALIAS[name];
  if (LBC_PRIMS.has(name)) return name;
  return ident(name);
}
const isFree = (name, sc) => !sc.names.has(name) && !CTX.userGlobals.has(name);

/* ═════════════════════════ Scheme AST 工具 ═════════════════════════ */
const NILQ = ['quote', 'nil'];
const BOOLHEADS = new Set(['null?', 'pair?', 'eq?', 'equal?', 'not', '<', '>', '<=', '>=', '=', 'number?', 'string?',
  'symbol?', 'procedure?', 'zero?', 'even?', 'odd?']);
const BOOLCORE = new Set(['core/nil?', 'core/some?', 'core/empty?', 'core/contains?', 'core/every?', 'core/not=', 'core/=',
  'core/pos?', 'core/neg?', 'core/vector?', 'core/map?', 'core/list?', 'core/keyword?', 'core/identical?', 'core/seq?',
  'core/coll?', 'core/sequential?', 'core/true?', 'core/false?', 'core/not-any?', 'core/_equiv', 'core/_tag?', 'core/t?',
  'core/not', 'core/boolean', 'core/_member?']);
const isBool = x => x === true || x === false ||
  (Array.isArray(x) && typeof x[0] === 'string' && (BOOLHEADS.has(x[0]) || BOOLCORE.has(x[0]))) ||
  (Array.isArray(x) && x[0] === 'if' && isBool(x[2]) && isBool(x[3]));

function truthy(x) {                                          // Clojure 真值: 只有 nil 與 false 為假
  if (isBool(x)) return x;
  if (typeof x === 'number' || x instanceof SStr) return true;
  if (Array.isArray(x) && x[0] === 'quote') return x[1] !== 'nil';
  if (typeof x === 'string') return ['if', ['eq?', x, false], false, ['not', ['eq?', x, NILQ]]];
  return ['core/t?', x];
}

function show(x) {
  if (typeof x === 'number') return String(x);
  if (typeof x === 'string') return x;
  if (x === true) return '#t';
  if (x === false) return '#f';
  if (x instanceof SStr) return JSON.stringify(x.v);
  if (Array.isArray(x)) return '(' + x.map(show).join(' ') + ')';
  throw new Error('無法輸出: ' + JSON.stringify(x));
}

const kwData = name => ['%kw', new SStr(name)];
function datumOf(f) {                                         // quote 內的資料
  if (typeof f === 'number') return f;
  if (f instanceof Str) return new SStr(f.v);
  if (f instanceof Kw) return kwData(f.name);
  if (f instanceof Sym) return f.name === 'true' ? true : f.name === 'false' ? false : f.name.replace(/'/g, '_q');
  if (f instanceof Vec) return ['%vec', ...f.items.map(datumOf)];
  if (f instanceof MapLit) { const o = ['%map']; for (let k = 0; k < f.items.length; k += 2) o.push([datumOf(f.items[k]), datumOf(f.items[k + 1])]); return o; }
  if (Array.isArray(f)) return f.map(datumOf);
  throw new Error('無法 quote');
}
function constDatum(f) {                                      // 全為常數的集合字面值 -> datum，否則 undefined
  if (typeof f === 'number' || f instanceof Str || f instanceof Kw) return datumOf(f);
  if (f instanceof Sym && ['nil', 'true', 'false'].includes(f.name)) return datumOf(f);
  if (f instanceof Vec || f instanceof MapLit) {
    if (!f.items.every(x => constDatum(x) !== undefined)) return undefined;
    return datumOf(f);
  }
  return undefined;
}

/* ═════════════════════════ Desugar: Clojure -> Scheme 核心 ═════════════════════════ */
function ex(f, sc, tail = false) {
  if (typeof f === 'number') return f;
  if (f instanceof Str) return new SStr(f.v);
  if (f instanceof Kw) return ['quote', kwData(f.name)];
  if (f instanceof Sym) {
    if (f.name === 'nil') return NILQ;
    if (f.name === 'true') return true;
    if (f.name === 'false') return false;
    return resolveName(f.name, sc);
  }
  if (f instanceof Vec) {
    const d = constDatum(f); if (d !== undefined) return ['quote', d];
    return ['cons', ['quote', '%vec'], ['list', ...f.items.map(x => ex(x, sc))]];
  }
  if (f instanceof MapLit) {
    const d = constDatum(f); if (d !== undefined) return ['quote', d];
    const es = []; for (let k = 0; k < f.items.length; k += 2) es.push(['list', ex(f.items[k], sc), ex(f.items[k + 1], sc)]);
    return ['cons', ['quote', '%map'], ['list', ...es]];
  }
  if (Array.isArray(f)) {
    if (f.length === 0) return ['quote', []];
    const head = f[0];
    if (head instanceof Sym && !sc.names.has(head.name) && Object.prototype.hasOwnProperty.call(SPECIAL, head.name))
      return SPECIAL[head.name](f, sc, tail);
    return exCall(f, sc);
  }
  throw new Error('無法編譯: ' + JSON.stringify(f));
}

function exBody(forms, sc, tail) {
  if (forms.length === 0) return NILQ;
  const out = forms.map((x, i) => ex(x, sc, tail && i === forms.length - 1));
  return out.length === 1 ? out[0] : ['begin', ...out];
}

const isSimpleLit = f => typeof f === 'number' || f instanceof Str || f instanceof Kw ||
  (f instanceof Sym && ['nil', 'true', 'false'].includes(f.name));
const APPLY_REWRITE = {
  '+': c => ['core/_sum', c], '*': c => ['core/_product', c], max: c => ['core/_maxl', c], min: c => ['core/_minl', c],
  str: c => ['core/_str-list', c], concat: c => ['core/_concat-all', ['core/_tolist', c]], vector: c => ['core/vec', c],
  list: c => ['core/_tolist', c],
};

function exCall(f, sc) {
  const head = f[0], args = f.slice(1);
  if (head instanceof Kw) {                                   // (:k m) / (:k m default)
    return ['core/get', ex(args[0], sc), ['quote', kwData(head.name)], ...(args.length > 1 ? [ex(args[1], sc)] : [])];
  }
  if (head instanceof Sym && isFree(head.name, sc)) {
    const nm = head.name, n = args.length;
    if (nm === 'inc' && n === 1) return ['+', ex(args[0], sc), 1];
    if (nm === 'dec' && n === 1) return ['-', ex(args[0], sc), 1];
    if (nm === 'nil?' && n === 1) return ['eq?', ex(args[0], sc), NILQ];
    if (nm === 'some?' && n === 1) return ['not', ['eq?', ex(args[0], sc), NILQ]];
    if (nm === 'not' && n === 1) { const x = ex(args[0], sc); return isBool(x) ? ['not', x] : ['if', truthy(x), false, true]; }
    if ((nm === '=' || nm === 'not=') && n === 2) {
      const a = ex(args[0], sc), b = ex(args[1], sc);
      const e = (isSimpleLit(args[0]) || isSimpleLit(args[1])) ? ['equal?', a, b] : ['core/_equiv', a, b];
      return nm === '=' ? e : ['not', e];
    }
    if (nm === 'apply' && n === 2 && args[0] instanceof Sym && isFree(args[0].name, sc) && APPLY_REWRITE[args[0].name])
      return APPLY_REWRITE[args[0].name](ex(args[1], sc));
  }
  return [ex(head, sc), ...args.map(a => ex(a, sc))];
}

/* ── 解構 ── */
function destructure(p, val, sc, out) {
  if (p instanceof Sym) { out.push([ident(p.name), val]); return sc.with(p.name); }
  if (p instanceof Vec) {
    const g = tmp(); out.push([g, val]);
    const it = p.items; let i = 0;
    for (let k = 0; k < it.length; k++) {
      const x = it[k];
      if (x instanceof Sym && x.name === '&') { sc = destructure(it[k + 1], ['core/_nthrest', g, i], sc, out); k++; continue; }
      if (x instanceof Kw && x.name === 'as') { sc = destructure(it[k + 1], g, sc, out); k++; continue; }
      sc = destructure(x, ['core/nth', g, i, NILQ], sc, out); i++;
    }
    return sc;
  }
  if (p instanceof MapLit) {
    const g = tmp(); out.push([g, val]);
    const defaults = new Map();
    for (let k = 0; k < p.items.length; k += 2)
      if (p.items[k] instanceof Kw && p.items[k].name === 'or') {
        const m = p.items[k + 1];
        for (let j = 0; j < m.items.length; j += 2) defaults.set(m.items[j].name, m.items[j + 1]);
      }
    const getE = (key, name) => ['core/get', g, key, ...(name && defaults.has(name) ? [ex(defaults.get(name), sc)] : [])];
    for (let k = 0; k < p.items.length; k += 2) {
      const key = p.items[k], v = p.items[k + 1];
      if (key instanceof Kw) {
        if (key.name === 'keys') for (const s of v.items) { out.push([ident(s.name), getE(['quote', kwData(s.name)], s.name)]); sc = sc.with(s.name); }
        else if (key.name === 'as') { out.push([ident(v.name), g]); sc = sc.with(v.name); }
        else if (key.name === 'or') { /* 已處理 */ }
        else throw new Error(`不支援的解構選項 :${key.name}`);
      } else sc = destructure(key, getE(ex(v, sc), key instanceof Sym ? key.name : null), sc, out);
    }
    return sc;
  }
  throw new Error('錯誤的解構樣式');
}
function exBindings(vec, sc, out) {
  if (!(vec instanceof Vec) || vec.items.length % 2) throw new Error('binding 必須是偶數個元素的 vector');
  for (let i = 0; i < vec.items.length; i += 2) sc = destructure(vec.items[i], ex(vec.items[i + 1], sc), sc, out);
  return sc;
}

/* ── fn / loop / recur ── */
function hasRecur(f) {
  if (Array.isArray(f)) {
    if (f[0] instanceof Sym) {
      if (f[0].name === 'recur') return true;
      if (['fn', 'fn*', 'loop', 'defn', 'defn-'].includes(f[0].name)) return false;
    }
    return f.some(hasRecur);
  }
  if (f instanceof Vec || f instanceof MapLit) return f.items.some(hasRecur);
  return false;
}

function buildLambda(pv, body, sc, packed) {
  if (!(pv instanceof Vec)) throw new Error('fn 需要參數 vector');
  let items = pv.items;
  if (hasRecur(body)) {                                       // 把 body 包進 (loop [p p ...] ...) 讓 recur 有目標
    const ni = [], lb = [];
    for (const p of items) {
      if (p instanceof Sym && p.name === '&') { ni.push(p); continue; }
      if (p instanceof Sym) { ni.push(p); lb.push(p, p); } else { const g = gsym(); ni.push(g); lb.push(p, g); }
    }
    items = ni; body = [[sym('loop'), new Vec(lb), ...body]];
  }
  const k = items.findIndex(x => x instanceof Sym && x.name === '&');
  const fixed = k < 0 ? items : items.slice(0, k), restP = k < 0 ? null : items[k + 1];
  const params = [], pend = []; let sc2 = sc.withRecur(null);
  for (const p of fixed) {
    if (p instanceof Sym) { params.push(ident(p.name)); sc2 = sc2.with(p.name); }
    else { const t = tmp('a'); params.push(t); pend.push([p, t]); }
  }
  let restTemp = null;
  if (restP) { restTemp = tmp('r'); if (packed) params.push(restTemp); else params.push('.', restTemp); }
  const pre = [];
  for (const [p, t] of pend) sc2 = destructure(p, t, sc2, pre);
  if (restP) sc2 = destructure(restP, packed ? restTemp : ['if', ['null?', restTemp], NILQ, restTemp], sc2, pre);
  const bodyS = exBody(body, sc2, true);
  return { lam: ['lambda', params, pre.length ? ['let*', pre, bodyS] : bodyS], nfixed: fixed.length, hasRest: !!restP };
}

function exFn(f, sc) {
  let i = 1, self = null;
  if (f[i] instanceof Sym) { self = f[i].name; i++; }
  const scF = self ? sc.with(self) : sc;
  let lam;
  if (f[i] instanceof Vec) lam = buildLambda(f[i], f.slice(i + 1), scF, false).lam;
  else {                                                      // 多元 arity: (fn ([x] ..) ([x y] ..))
    const ars = f.slice(i).map(a => {
      if (!Array.isArray(a) || !(a[0] instanceof Vec)) throw new Error('錯誤的 fn 形式');
      return buildLambda(a[0], a.slice(1), scF, true);
    });
    const args = tmp('args'), n = tmp('n');
    const nth = (idx) => { let e = args; for (let q = 0; q < idx; q++) e = ['cdr', e]; return e; };
    let disp = ['error', new SStr('Wrong number of args passed to fn')];
    for (const a of [...ars].reverse()) {
      const callArgs = []; for (let q = 0; q < a.nfixed; q++) callArgs.push(['car', nth(q)]);
      if (a.hasRest) callArgs.push(nth(a.nfixed));
      disp = ['if', [a.hasRest ? '>=' : '=', n, a.nfixed], [a.lam, ...callArgs], disp];
    }
    lam = ['lambda', args, ['let*', [[n, ['length', args]]], disp]];
  }
  return self ? ['letrec', [[ident(self), lam]], ident(self)] : lam;
}

let lid = 0;
function exLoop(f, sc, tail) {
  const bv = f[1];
  if (!(bv instanceof Vec) || bv.items.length % 2) throw new Error('loop 的 binding 必須是偶數個元素的 vector');
  const name = `%loop${lid++}`, outer = [], vars = [], pending = [];
  let scInit = sc, scBody = sc;
  for (let q = 0; q < bv.items.length; q += 2) {
    const p = bv.items[q], init = ex(bv.items[q + 1], scInit);
    if (p instanceof Sym) { const nm = ident(p.name); outer.push([nm, init]); vars.push(nm); scInit = scInit.with(p.name); scBody = scBody.with(p.name); }
    else { const t = tmp('a'); outer.push([t, init]); vars.push(t); pending.push([p, t]); }
  }
  const inner = [];
  for (const [p, t] of pending) scBody = destructure(p, t, scBody, inner);
  scBody = scBody.withRecur({ name, n: vars.length });
  const body = exBody(f.slice(2), scBody, true);
  const lam = ['lambda', vars, inner.length ? ['let*', inner, body] : body];
  const call = ['letrec', [[name, lam]], [name, ...vars]];
  return outer.length ? ['let*', outer, call] : call;
}

/* ── 巨集式語法糖: 先改寫成 Clojure 形式，再遞迴編譯 ── */
const S = (n, ...r) => [sym(n), ...r];
const core = n => sym('core/' + n);

function parseForBindings(vec) {                              // [x xs :when p y ys ...] -> [{pat, coll, whens}]
  const it = vec.items, groups = [];
  for (let q = 0; q < it.length;) {
    const g = { pat: it[q], coll: it[q + 1], whens: [] }; q += 2;
    while (q < it.length && it[q] instanceof Kw) {
      if (it[q].name === 'when') g.whens.push(it[q + 1]);
      else throw new Error(`for / doseq 不支援 :${it[q].name}`);
      q += 2;
    }
    groups.push(g);
  }
  return groups;
}
const andOf = ws => ws.length === 1 ? ws[0] : [sym('and'), ...ws];

const SPECIAL = {
  quote: f => ['quote', datumOf(f[1])],
  if: (f, sc, tail) => ['if', truthy(ex(f[1], sc)), ex(f[2], sc, tail), f.length > 3 ? ex(f[3], sc, tail) : NILQ],
  do: (f, sc, tail) => exBody(f.slice(1), sc, tail),
  let: (f, sc, tail) => { const out = []; const sc2 = exBindings(f[1], sc, out); const b = exBody(f.slice(2), sc2, tail); return out.length ? ['let*', out, b] : b; },
  loop: exLoop,
  recur: (f, sc, tail) => {
    if (!sc.recur) throw new Error('recur 必須位於 loop 或 fn 之內');
    if (!tail) throw new Error('recur 只能出現在尾位置 (Can only recur from tail position)');
    if (f.length - 1 !== sc.recur.n) throw new Error(`recur 參數個數錯誤: 需要 ${sc.recur.n}，得到 ${f.length - 1}`);
    return [sc.recur.name, ...f.slice(1).map(a => ex(a, sc))];
  },
  fn: (f, sc) => exFn(f, sc), 'fn*': (f, sc) => exFn(f, sc),
  def: (f, sc) => {
    const nm = f[1].name, v = f.length > 3 ? f[3] : f[2];
    return ['define', CTX.prelude ? 'core/' + nm : ident(nm), f.length > 2 ? ex(v, sc) : NILQ];
  },
  defonce: (f, sc) => SPECIAL.def(f, sc),
  defn: (f, sc) => {
    const nm = f[1].name; let i = 2;
    if (f[i] instanceof Str) i++;
    if (f[i] instanceof MapLit) i++;
    return ['define', CTX.prelude ? 'core/' + nm : ident(nm), exFn([sym('fn'), ...f.slice(i)], sc)];
  },
  'defn-': (f, sc) => SPECIAL.defn(f, sc),
  declare: () => NILQ, ns: () => NILQ, require: () => NILQ, use: () => NILQ, import: () => NILQ, comment: () => NILQ,
  defmacro: () => { throw new Error('不支援 defmacro (沒有巨集)'); },
  try: () => { throw new Error('不支援 try / catch'); },
  when: (f, sc, tail) => ['if', truthy(ex(f[1], sc)), exBody(f.slice(2), sc, tail), NILQ],
  'when-not': (f, sc, tail) => ['if', truthy(ex(f[1], sc)), NILQ, exBody(f.slice(2), sc, tail)],
  'if-not': (f, sc, tail) => ['if', truthy(ex(f[1], sc)), f.length > 3 ? ex(f[3], sc, tail) : NILQ, ex(f[2], sc, tail)],
  'if-let': (f, sc, tail) => {
    const [p, test] = f[1].items, g = gsym();
    return ex(S('let', new Vec([g, test]), S('if', g, S('let', new Vec([p, g]), f[2]), ...(f.length > 3 ? [f[3]] : []))), sc, tail);
  },
  'when-let': (f, sc, tail) => {
    const [p, test] = f[1].items, g = gsym();
    return ex(S('let', new Vec([g, test]), S('when', g, S('let', new Vec([p, g]), ...f.slice(2)))), sc, tail);
  },
  cond: (f, sc, tail) => {
    if ((f.length - 1) % 2) throw new Error('cond 需要偶數個表達式');
    const build = i => {
      if (i >= f.length) return NILQ;
      const t = f[i];
      if ((t instanceof Kw && t.name === 'else') || (t instanceof Sym && t.name === 'true')) return ex(f[i + 1], sc, tail);
      return ['if', truthy(ex(t, sc)), ex(f[i + 1], sc, tail), build(i + 2)];
    };
    return build(1);
  },
  case: (f, sc, tail) => {
    const g = gsym(), rest = f.slice(2), clauses = [];
    let dflt = null;
    for (let q = 0; q < rest.length; q += 2) {
      if (q + 1 >= rest.length) { dflt = rest[q]; break; }
      const t = rest[q], tests = (Array.isArray(t) ? t : [t]).map(c => S('%equal?', g, S('quote', c)));
      clauses.push(tests.length === 1 ? tests[0] : [sym('or'), ...tests], rest[q + 1]);
    }
    clauses.push(new Kw('else'), dflt !== null ? dflt : S('%error', new Str('No matching clause')));
    return ex(S('let', new Vec([g, f[1]]), [sym('cond'), ...clauses]), sc, tail);
  },
  and: (f, sc, tail) => {
    const a = f.slice(1);
    if (a.length === 0) return true;
    if (a.length === 1) return ex(a[0], sc, tail);
    const A = ex(a[0], sc), R = SPECIAL.and([f[0], ...a.slice(1)], sc, tail);
    if (isBool(A)) return ['if', A, R, false];
    const g = tmp(); return ['let', [[g, A]], ['if', truthy(g), R, g]];
  },
  or: (f, sc, tail) => {
    const a = f.slice(1);
    if (a.length === 0) return NILQ;
    if (a.length === 1) return ex(a[0], sc, tail);
    const A = ex(a[0], sc), R = SPECIAL.or([f[0], ...a.slice(1)], sc, tail);
    if (isBool(A)) return ['if', A, true, R];
    const g = tmp(); return ['let', [[g, A]], ['if', truthy(g), g, R]];
  },
  '->': (f, sc, tail) => ex(f.slice(2).reduce((acc, s) => Array.isArray(s) ? [s[0], acc, ...s.slice(1)] : [s, acc], f[1]), sc, tail),
  '->>': (f, sc, tail) => ex(f.slice(2).reduce((acc, s) => Array.isArray(s) ? [...s, acc] : [s, acc], f[1]), sc, tail),
  dotimes: (f, sc, tail) => {
    const [i, n] = f[1].items, g = gsym();
    return ex(S('let', new Vec([g, n]), S('loop', new Vec([i, 0]), S('when', S('%<', i, g), ...f.slice(2), S('recur', S('%+', i, 1))))), sc, tail);
  },
  doseq: (f, sc, tail) => {
    const groups = parseForBindings(f[1]), body = f.slice(2);
    const build = k => {
      const g = groups[k], inner = k === groups.length - 1 ? [sym('do'), ...body] : build(k + 1);
      return S('core/_each', S('fn', new Vec([g.pat]), g.whens.length ? S('when', andOf(g.whens), inner) : inner), g.coll);
    };
    return ex(build(0), sc, tail);
  },
  for: (f, sc, tail) => {
    const groups = parseForBindings(f[1]), body = f.length > 3 ? [sym('do'), ...f.slice(2)] : f[2];
    const build = k => {
      const g = groups[k], last = k === groups.length - 1;
      const coll = g.whens.length ? S('core/filter', S('fn', new Vec([g.pat]), andOf(g.whens)), g.coll) : g.coll;
      return S(last ? 'core/map' : 'core/mapcat', S('fn', new Vec([g.pat]), last ? body : build(k + 1)), coll);
    };
    return ex(build(0), sc, tail);
  },
};

/* ═════════════════════════ Prelude (標準函式庫，以 Clojure 撰寫) ═════════════════════════
 * 慣例: %name = 直接使用 LBC 內建函式 (%cons %car %+ ...)；_name = 內部輔助函式；
 *       執行期 nil 是符號 nil，vector/map/keyword 是帶標籤的 list。 */
function applyListSrc() {
  const arg = i => `(%car ${'(%cdr '.repeat(i)}l${')'.repeat(i)})`;
  let s = '(defn _apply-list [f l]\n  (let [n (%length l)]\n    (cond\n';
  for (let n = 0; n <= 10; n++) s += `      (%= n ${n}) (f${Array.from({ length: n }, (_, i) => ' ' + arg(i)).join('')})\n`;
  return s + '      :else (%error "apply: too many arguments (max 10)"))))\n';
}

const PRELUDE = String.raw`
;; ───── 基本 ─────
(defn t? [x] (if (%eq? x false) false (%not (%eq? x nil))))
(defn nil? [x] (%eq? x nil))
(defn some? [x] (%not (%eq? x nil)))
(defn not [x] (if x false true))
(defn identity [x] x)
(defn boolean [x] (if x true false))
(defn true? [x] (%eq? x true))
(defn false? [x] (%eq? x false))
(defn inc [x] (%+ x 1))
(defn dec [x] (%- x 1))
(defn pos? [x] (%> x 0))
(defn neg? [x] (%< x 0))
(defn constantly [v] (fn [& _] v))
(defn _nn [l] (if (%null? l) nil l))

;; ───── 型別判斷 ─────
(defn _tag? [x t] (and (%pair? x) (%eq? (%car x) t)))
(defn keyword? [x] (_tag? x '%kw))
(defn vector? [x] (_tag? x '%vec))
(defn map? [x] (_tag? x '%map))
(defn list? [x] (or (%null? x) (and (%pair? x) (%not (_tag? x '%vec)) (%not (_tag? x '%map)) (%not (_tag? x '%kw)))))
(defn seq? [x] (list? x))
(defn sequential? [x] (or (list? x) (vector? x)))
(defn coll? [x] (or (list? x) (vector? x) (map? x)))
(defn name [k] (cond (keyword? k) (%car (%cdr k)) (%string? k) k :else (%error "name: unsupported argument")))
(defn keyword [s] (%list '%kw s))

;; ───── 原始 list 輔助 (操作 LBC list) ─────
(defn _map1 [f l] (if (%null? l) l (%cons (f (%car l)) (_map1 f (%cdr l)))))
(defn _filter1 [p l]
  (cond (%null? l) l
        (p (%car l)) (%cons (%car l) (_filter1 p (%cdr l)))
        :else (_filter1 p (%cdr l))))
(defn _take-raw [n l] (if (or (%<= n 0) (%null? l)) '() (%cons (%car l) (_take-raw (%- n 1) (%cdr l)))))
(defn _drop-raw [n l] (if (or (%<= n 0) (%null? l)) l (_drop-raw (%- n 1) (%cdr l))))
(defn _concat-all [cs] (if (%null? cs) '() (%append (_tolist (%car cs)) (_concat-all (%cdr cs)))))
(defn _ifn [f]
  (cond (keyword? f) (fn [m] (get m f))
        (map? f) (fn [k] (get f k))
        :else f))
(defn _each [f l]
  (let [f (_ifn f)]
    (loop [l (_tolist l)]
      (when (%pair? l) (f (%car l)) (recur (%cdr l))))))

;; ───── 序列抽象: 任何集合 -> 原始 list ─────
(defn _tolist [c]
  (cond (%null? c) c
        (%pair? c) (let [h (%car c)]
                     (cond (%eq? h '%vec) (%cdr c)
                           (%eq? h '%map) (_map1 (fn [e] (%cons '%vec e)) (%cdr c))
                           (%eq? h '%kw) (%error "keyword is not seqable")
                           :else c))
        (%eq? c nil) '()
        :else (%error "value is not seqable")))
(defn first [c] (let [l (_tolist c)] (if (%null? l) nil (%car l))))
(defn rest [c] (let [l (_tolist c)] (if (%null? l) l (%cdr l))))
(defn next [c] (_nn (rest c)))
(defn second [c] (first (rest c)))
(defn seq [c] (_nn (_tolist c)))
(defn empty? [c] (%null? (_tolist c)))
(defn cons [x c] (%cons x (_tolist c)))
(defn count [c]
  (cond (%eq? c nil) 0
        (%string? c) (%string-length c)
        (%null? c) 0
        (or (vector? c) (map? c)) (%- (%length c) 1)
        :else (%length c)))
(defn nth [c i & d]
  (loop [l (_tolist c) k i]
    (cond (%null? l) (if (nil? d) (%error "Index out of bounds") (%car d))
          (%<= k 0) (%car l)
          :else (recur (%cdr l) (%- k 1)))))
(defn _nthrest [c i] (_nn (_drop-raw i (_tolist c))))
(defn last [c]
  (let [l (_tolist c)]
    (if (%null? l) nil (loop [l l] (if (%null? (%cdr l)) (%car l) (recur (%cdr l)))))))
(defn butlast [c] (let [l (_tolist c)] (if (%null? l) nil (_nn (%reverse (%cdr (%reverse l)))))))
(defn reverse [c] (%reverse (_tolist c)))
(defn vec [c] (%cons '%vec (_tolist c)))
(defn vector [& xs] (%cons '%vec (if (nil? xs) '() xs)))
(defn peek [c] (if (vector? c) (last c) (first c)))
(defn pop [c]
  (if (vector? c) (%cons '%vec (%reverse (%cdr (%reverse (%cdr c))))) (rest c)))

;; ───── 相等 ─────
(defn _map-equiv [a b]
  (and (%= (%length a) (%length b))
       (every? (fn [e] (let [f (_entry-find (%cdr b) (%car e))]
                         (and f (_equiv (%car (%cdr e)) (%car (%cdr f))))))
               (%cdr a))))
(defn _equiv [a b]
  (cond (map? a) (and (map? b) (_map-equiv a b))
        (%pair? a) (and (%pair? b) (%not (map? b)) (_equiv (%car a) (%car b)) (_equiv (%cdr a) (%cdr b)))
        :else (%equal? a b)))
(defn = [a & more]
  (loop [l more]
    (cond (nil? l) true
          (_equiv a (%car l)) (recur (_nn (%cdr l)))
          :else false)))
(defn not= [a b] (%not (_equiv a b)))
(defn _member? [x l] (cond (%null? l) false (_equiv x (%car l)) true :else (_member? x (%cdr l))))

;; ───── conj / map 操作 ─────
(defn _conj1 [c x]
  (cond (%eq? c nil) (%list x)
        (vector? c) (%cons '%vec (%append (%cdr c) (%list x)))
        (map? c) (assoc c (first x) (second x))
        :else (%cons x c)))
(defn conj [c & xs]
  (loop [c c xs xs]
    (if (nil? xs) c (recur (_conj1 c (%car xs)) (_nn (%cdr xs))))))
(defn _entry-find [es k]
  (cond (%null? es) false
        (_equiv (%car (%car es)) k) (%car es)
        :else (_entry-find (%cdr es) k)))
(defn _set-nth [l k v]
  (cond (%null? l) (%error "assoc: index out of bounds")
        (%= k 0) (%cons v (%cdr l))
        :else (%cons (%car l) (_set-nth (%cdr l) (%- k 1) v))))
(defn _assoc1 [m k v]
  (cond (%eq? m nil) (%cons '%map (%list (%list k v)))
        (map? m) (let [es (%cdr m)]
                   (if (_entry-find es k)
                     (%cons '%map (_map1 (fn [e] (if (_equiv (%car e) k) (%list k v) e)) es))
                     (%cons '%map (%append es (%list (%list k v))))))
        (vector? m) (%cons '%vec (_set-nth (%cdr m) k v))
        :else (%error "assoc: not an associative collection")))
(defn assoc [m k v & kvs]
  (loop [m (_assoc1 m k v) kvs kvs]
    (if (nil? kvs) m (recur (_assoc1 m (%car kvs) (%car (%cdr kvs))) (_nn (%cdr (%cdr kvs)))))))
(defn _dissoc1 [m k]
  (if (map? m) (%cons '%map (_filter1 (fn [e] (%not (_equiv (%car e) k))) (%cdr m))) m))
(defn dissoc [m & ks]
  (loop [m m ks ks] (if (nil? ks) m (recur (_dissoc1 m (%car ks)) (_nn (%cdr ks))))))
(defn get [m k & d]
  (let [dv (if (nil? d) nil (%car d))]
    (cond (map? m) (let [e (_entry-find (%cdr m) k)] (if e (%car (%cdr e)) dv))
          (vector? m) (if (and (%number? k) (%>= k 0) (%< k (%- (%length m) 1))) (nth m k) dv)
          :else dv)))
(defn contains? [m k]
  (cond (map? m) (%not (%eq? (_entry-find (%cdr m) k) false))
        (vector? m) (and (%number? k) (%>= k 0) (%< k (%- (%length m) 1)))
        :else false))
(defn keys [m] (if (map? m) (_nn (_map1 %car (%cdr m))) nil))
(defn vals [m] (if (map? m) (_nn (_map1 (fn [e] (%car (%cdr e))) (%cdr m))) nil))
(defn _merge2 [a b]
  (if (nil? b) a
    (loop [a a es (%cdr b)]
      (if (%null? es) a (recur (_assoc1 a (%car (%car es)) (%car (%cdr (%car es)))) (%cdr es))))))
(defn merge [& ms]
  (loop [acc nil ms ms]
    (cond (nil? ms) acc
          (nil? acc) (recur (%car ms) (_nn (%cdr ms)))
          :else (recur (_merge2 acc (%car ms)) (_nn (%cdr ms))))))
(defn hash-map [& kvs]
  (loop [m {} kvs kvs]
    (if (nil? kvs) m (recur (_assoc1 m (%car kvs) (%car (%cdr kvs))) (_nn (%cdr (%cdr kvs)))))))
(defn update [m k f & args] (assoc m k (apply f (get m k) args)))
(defn get-in [m ks & d]
  (let [dv (if (nil? d) nil (%car d))]
    (loop [m m l (_tolist ks)]
      (cond (%null? l) m
            (not (or (map? m) (vector? m))) dv
            :else (recur (get m (%car l) dv) (%cdr l))))))
(defn assoc-in [m ks v]
  (let [l (_tolist ks)]
    (if (%null? (%cdr l))
      (assoc m (%car l) v)
      (assoc m (%car l) (assoc-in (get m (%car l)) (%cdr l) v)))))
(defn update-in [m ks f & args] (assoc-in m ks (apply f (get-in m ks) args)))
(defn select-keys [m ks]
  (reduce (fn [acc k] (if (contains? m k) (assoc acc k (get m k)) acc)) {} ks))
(defn zipmap [ks vs]
  (loop [m {} ks (_tolist ks) vs (_tolist vs)]
    (if (or (%null? ks) (%null? vs)) m (recur (_assoc1 m (%car ks) (%car vs)) (%cdr ks) (%cdr vs)))))
(defn frequencies [c] (reduce (fn [m x] (assoc m x (inc (get m x 0)))) {} c))
(defn group-by [f c]
  (let [f (_ifn f)]
    (reduce (fn [m x] (let [k (f x)] (assoc m k (conj (get m k []) x)))) {} c)))

;; ───── 序列函式 (eager) ─────
(defn map [f c & more]
  (let [f (_ifn f)]
    (if (nil? more)
      (_map1 f (_tolist c))
      (loop [a (_tolist c) b (_tolist (%car more)) acc '()]
        (if (or (%null? a) (%null? b)) (%reverse acc)
          (recur (%cdr a) (%cdr b) (%cons (f (%car a) (%car b)) acc)))))))
(defn mapv [f c] (vec (map f c)))
(defn filter [p c] (_filter1 (_ifn p) (_tolist c)))
(defn filterv [p c] (vec (filter p c)))
(defn remove [p c] (let [p (_ifn p)] (_filter1 (fn [x] (not (p x))) (_tolist c))))
(defn reduce [f a & more]
  (let [init? (%not (nil? more))
        l (_tolist (if init? (%car more) a))]
    (loop [acc (if init? a (if (%null? l) (f) (%car l)))
           l (if init? l (if (%null? l) l (%cdr l)))]
      (if (%null? l) acc (recur (f acc (%car l)) (%cdr l))))))
(defn _range [s e step]
  (cond (%= step 0) (%error "range: step must not be 0")
        :else
        (let [up (%> step 0)
              d (if up (%- e s) (%- s e))
              st (if up step (%- 0 step))
              n (if (%> d 0) (%quotient (%+ d (%- st 1)) st) 0)]
          (loop [i (%- n 1) acc '()]
            (if (%< i 0) acc (recur (%- i 1) (%cons (%+ s (%* i step)) acc)))))))
(defn range [a & more]
  (cond (nil? more) (_range 0 a 1)
        (%null? (%cdr more)) (_range a (%car more) 1)
        :else (_range a (%car more) (%car (%cdr more)))))
(defn repeat [n x] (loop [i n acc '()] (if (%<= i 0) acc (recur (%- i 1) (%cons x acc)))))
(defn take [n c] (_take-raw n (_tolist c)))
(defn drop [n c] (_drop-raw n (_tolist c)))
(defn take-while [p c]
  (let [p (_ifn p)]
    (loop [l (_tolist c) acc '()]
      (if (and (%pair? l) (p (%car l))) (recur (%cdr l) (%cons (%car l) acc)) (%reverse acc)))))
(defn drop-while [p c]
  (let [p (_ifn p)]
    (loop [l (_tolist c)] (if (and (%pair? l) (p (%car l))) (recur (%cdr l)) l))))
(defn concat [& cs] (if (nil? cs) '() (_concat-all cs)))
(defn mapcat [f c] (_concat-all (_map1 (_ifn f) (_tolist c))))
(defn into [to from] (reduce conj to from))
(defn some [p c]
  (let [p (_ifn p)]
    (loop [l (_tolist c)]
      (if (%null? l) nil (let [r (p (%car l))] (if r r (recur (%cdr l))))))))
(defn every? [p c]
  (let [p (_ifn p)]
    (loop [l (_tolist c)]
      (cond (%null? l) true (p (%car l)) (recur (%cdr l)) :else false))))
(defn not-any? [p c] (not (some p c)))
(defn distinct [c]
  (loop [l (_tolist c) acc '()]
    (cond (%null? l) (%reverse acc)
          (_member? (%car l) acc) (recur (%cdr l) acc)
          :else (recur (%cdr l) (%cons (%car l) acc)))))
(defn flatten [c]
  (_concat-all (_map1 (fn [x] (if (sequential? x) (flatten x) (%list x))) (_tolist c))))
(defn partition [n c]
  (loop [l (_tolist c) acc '()]
    (if (%< (%length l) n) (%reverse acc) (recur (_drop-raw n l) (%cons (_take-raw n l) acc)))))
(defn interleave [a b]
  (loop [a (_tolist a) b (_tolist b) acc '()]
    (if (or (%null? a) (%null? b)) (%reverse acc)
      (recur (%cdr a) (%cdr b) (%cons (%car b) (%cons (%car a) acc))))))
(defn interpose [sep c]
  (let [l (_tolist c)]
    (if (%null? l) l (%cons (%car l) (_concat-all (_map1 (fn [x] (%list sep x)) (%cdr l)))))))
(defn key [e] (first e))
(defn val [e] (second e))
(defn keep [f c] (let [f (_ifn f)] (_filter1 (fn [x] (some? x)) (_map1 f (_tolist c)))))
(defn max-key [f x & more]
  (loop [best x l more]
    (if (nil? l) best (recur (if (%> (f (%car l)) (f best)) (%car l) best) (_nn (%cdr l))))))
(defn min-key [f x & more]
  (loop [best x l more]
    (if (nil? l) best (recur (if (%< (f (%car l)) (f best)) (%car l) best) (_nn (%cdr l))))))
(defn doall [c] c)
(defn dorun [c] nil)
(defn run! [f c] (_each f c) nil)

;; ───── 排序 ─────
(defn _lt [cmp] (fn [a b] (let [r (cmp a b)] (if (%number? r) (%< r 0) (if r true false)))))
(defn _merge [lt a b]
  (cond (%null? a) b
        (%null? b) a
        (lt (%car b) (%car a)) (%cons (%car b) (_merge lt a (%cdr b)))
        :else (%cons (%car a) (_merge lt (%cdr a) b))))
(defn _msort [lt l]
  (let [n (%length l)]
    (if (%< n 2) l
      (let [h (%quotient n 2)]
        (_merge lt (_msort lt (_take-raw h l)) (_msort lt (_drop-raw h l)))))))
(defn sort [a & more]
  (if (nil? more) (_msort (fn [x y] (%< x y)) (_tolist a)) (_msort (_lt a) (_tolist (%car more)))))
(defn sort-by [kf a & more]
  (let [kf (_ifn kf)]
    (if (nil? more)
      (_msort (fn [x y] (%< (kf x) (kf y))) (_tolist a))
      (let [lt (_lt a)] (_msort (fn [x y] (lt (kf x) (kf y))) (_tolist (%car more)))))))

;; ───── 高階函式 ─────
` + applyListSrc() + String.raw`
(defn _spread [args]
  (if (%null? (%cdr args)) (_tolist (%car args)) (%cons (%car args) (_spread (%cdr args)))))
(defn apply [f & args] (_apply-list f (_spread args)))
(defn _sum [c] (loop [l (_tolist c) acc 0] (if (%null? l) acc (recur (%cdr l) (%+ acc (%car l))))))
(defn _product [c] (loop [l (_tolist c) acc 1] (if (%null? l) acc (recur (%cdr l) (%* acc (%car l))))))
(defn _maxl [c] (let [l (_tolist c)] (loop [l (%cdr l) acc (%car l)] (if (%null? l) acc (recur (%cdr l) (%max acc (%car l)))))))
(defn _minl [c] (let [l (_tolist c)] (loop [l (%cdr l) acc (%car l)] (if (%null? l) acc (recur (%cdr l) (%min acc (%car l)))))))
(defn comp [& fs]
  (if (nil? fs) (fn [x] x)
    (let [rv (%reverse fs)]
      (fn [& args]
        (loop [r (%cdr rv) acc (apply (%car rv) args)]
          (if (%null? r) acc (recur (%cdr r) ((%car r) acc))))))))
(defn partial [f & a1] (fn [& a2] (apply f (%append (_tolist a1) (_tolist a2)))))
(defn complement [f] (fn [& args] (not (apply f args))))

;; ───── 列印與字串 ─────
(defn _pr-seq [open close l readably emit]
  (emit open)
  (loop [l l first? true]
    (when (%pair? l)
      (if first? nil (emit " "))
      (_pr (%car l) readably emit)
      (recur (%cdr l) false)))
  (emit close)
  nil)
(defn _pr-map [es readably emit]
  (emit "{")
  (loop [es es first? true]
    (when (%pair? es)
      (if first? nil (emit ", "))
      (_pr (%car (%car es)) readably emit)
      (emit " ")
      (_pr (%car (%cdr (%car es))) readably emit)
      (recur (%cdr es) false)))
  (emit "}")
  nil)
(defn _pr [x readably emit]
  (cond (%eq? x nil) (emit "nil")
        (%eq? x true) (emit "true")
        (%eq? x false) (emit "false")
        (%number? x) (emit (%number->string x))
        (%string? x) (if readably (emit (%string-append "\"" x "\"")) (emit x))
        (%null? x) (emit "()")
        (%pair? x) (cond (%eq? (%car x) '%kw) (do (emit ":") (emit (%car (%cdr x))))
                         (%eq? (%car x) '%vec) (_pr-seq "[" "]" (%cdr x) readably emit)
                         (%eq? (%car x) '%map) (_pr-map (%cdr x) readably emit)
                         :else (_pr-seq "(" ")" x readably emit))
        :else (emit x)))
(defn _print-args [xs readably]
  (loop [l xs first? true]
    (when (%pair? l)
      (if first? nil (%display " "))
      (_pr (%car l) readably %display)
      (recur (%cdr l) false))))
(defn println [& xs] (_print-args xs false) (%newline) nil)
(defn print [& xs] (_print-args xs false) nil)
(defn prn [& xs] (_print-args xs true) (%newline) nil)
(defn pr [& xs] (_print-args xs true) nil)
(defn _tostr [x readably]
  (let [acc ""]
    (_pr x readably (fn [s] (%set! acc (%string-append acc (if (%string? s) s "?")))))
    acc))
(defn _str1 [x] (if (nil? x) "" (_tostr x false)))
(defn _str-list [l]
  (loop [l (_tolist l) acc ""]
    (if (%pair? l) (recur (%cdr l) (%string-append acc (_str1 (%car l)))) acc)))
(defn str [& xs] (if (nil? xs) "" (_str-list xs)))
(defn pr-str [& xs]
  (if (nil? xs) ""
    (loop [l (%cdr xs) acc (_tostr (%car xs) true)]
      (if (%pair? l) (recur (%cdr l) (%string-append acc " " (_tostr (%car l) true))) acc))))
(defn join [a & more]
  (let [sep (if (nil? more) "" a)
        l (_tolist (if (nil? more) a (%car more)))]
    (if (%null? l) ""
      (loop [acc (str (%car l)) l (%cdr l)]
        (if (%null? l) acc (recur (%string-append acc sep (str (%car l))) (%cdr l)))))))

;; ───── atom ─────
(defn atom [init]
  (let [v init]
    (fn [op x]
      (cond (%eq? op 'get) v
            (%eq? op 'set) (do (%set! v x) v)
            :else (do (%set! v (x v)) v)))))
(defn deref [a] (a 'get nil))
(defn reset! [a x] (a 'set x))
(defn swap! [a f & args] (a 'swap (fn [v] (apply f v args))))
`;

/* ═════════════════════════ 組裝 ═════════════════════════ */
const scanCore = (x, set) => {
  if (typeof x === 'string') { if (x.startsWith('core/')) set.add(x.slice(5)); }
  else if (Array.isArray(x)) x.forEach(y => scanCore(y, set));
};

let preludeCache = null;
function loadPrelude() {
  if (preludeCache) return preludeCache;
  const forms = readAll(PRELUDE);
  const names = forms.map(f => f[1].name);
  CTX = { prelude: true, userGlobals: new Set(), coreNames: new Set(names) };
  const defs = new Map();
  forms.forEach((f, i) => {
    const scheme = ex(f, new Scope(), false), deps = new Set();
    scanCore(scheme, deps);
    defs.set(names[i], { scheme, deps });
  });
  return (preludeCache = { names, defs });
}

function collectGlobals(forms) {
  const s = new Set();
  const walk = f => {
    if (!Array.isArray(f) || !(f[0] instanceof Sym)) return;
    const h = f[0].name;
    if (['def', 'defn', 'defn-', 'defonce'].includes(h) && f[1] instanceof Sym) s.add(f[1].name);
    else if (h === 'declare') f.slice(1).forEach(x => x instanceof Sym && s.add(x.name));
    else if (h === 'do') f.slice(1).forEach(walk);
  };
  forms.forEach(walk);
  return s;
}

function toScheme(src) {
  const P = loadPrelude();
  const forms = readAll(src);
  CTX = { prelude: false, userGlobals: collectGlobals(forms), coreNames: new Set(P.names) };
  const user = forms.map(f => ex(f, new Scope(), false));
  const need = new Set(), work = [];
  const add = n => { if (P.defs.has(n) && !need.has(n)) { need.add(n); work.push(n); } };
  const used = new Set(); scanCore(user, used); used.forEach(add);
  while (work.length) P.defs.get(work.pop()).deps.forEach(add);
  const pre = P.names.filter(n => need.has(n)).map(n => P.defs.get(n).scheme);
  return [...pre, ...user].map(show).join('\n') + '\n';
}

function compile(src) { return lispc.compile(toScheme(src)); }
module.exports = { compile, toScheme };

/* ═════════════════════════ CLI ═════════════════════════ */
if (require.main === module) {
  const args = process.argv.slice(2);
  if (!args.length) { console.error('用法: node cljc.js prog.clj [-o prog.lbc] [--scheme]'); process.exit(1); }
  const input = args.find((a, i) => !a.startsWith('-') && args[i - 1] !== '-o');
  const oi = args.indexOf('-o');
  const output = oi >= 0 ? args[oi + 1] : input.replace(/\.[^.]*$/, '') + '.lbc';
  try {
    const src = fs.readFileSync(input, 'utf8');
    if (args.includes('--scheme')) process.stdout.write(toScheme(src));
    else { const bc = compile(src); fs.writeFileSync(output, bc); console.error(`已編譯 ${input} -> ${output}`); }
  } catch (e) { console.error('編譯錯誤: ' + e.message); process.exit(1); }
}
