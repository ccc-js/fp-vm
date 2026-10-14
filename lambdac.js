#!/usr/bin/env node
'use strict';
/*
 * lambdac.js  —  Lambda Calculus  ->  LBC v1 中間碼 (與 lispc.js 相同格式，用 vm.js 執行)
 *
 * 用法:  node lambdac.js input.lc [-o output.lbc]      (-o - 輸出到 stdout)
 *        node vm.js output.lbc
 *
 * ───────────────────────────── 語法 ─────────────────────────────
 *  程式    := 項目 ( ";" 項目 )* [";"]            -- 註解以 -- 開頭
 *  項目    := 運算式
 *           | "let"    名稱 參數* "=" 運算式       頂層定義  (let f x y = ...;)
 *           | "letrec" 名稱 參數* "=" 運算式       頂層遞迴定義
 *
 *  運算式  := "\" 參數+ "." 運算式                 lambda  (也可寫 λ)；\x y. e 即 \x.\y. e
 *           | f a b c                               應用 (左結合、curried)
 *           | "let" x "=" e "in" e                  區域綁定 (等價於 (\x. body) e)
 *           | "letrec" x "=" e "in" e               區域遞迴綁定
 *           | "if" c "then" a "else" b
 *           | 中綴運算:  || && == != < > <= >= :: + - * / %      (優先序由低到高)
 *           | 原子
 *  原子    := 數字 | "字串" | true | false | nil | () | 'symbol | [e1, e2, ...]
 *           | 變數 | ( 運算式 ) | (+) (-) (*) ... 運算子當函式
 *
 *  基礎型態與 lispc 相同: 數字、布林、字串、符號、pair/list、空串列(nil)。
 *
 *  語意: call-by-value，所有函式都是 curried (單參數)。
 *  內建函式 (car cdr cons display ... 與 +,- 等) 也能 curried 使用:
 *     編譯器在編譯期依 arity 做 eta 展開，所以 `map (add 1) xs`、`foldl (+) 0 xs` 都行。
 *     內建函式表見下方 PRIMS (字串函式用底線: string_append, number_to_string ...)。
 */
const fs = require('fs');

/* ───────────── 內建函式表: 表面名稱 -> [VM 名稱, arity] ───────────── */
const PRIMS = new Map(Object.entries({
  '+': ['+', 2], '-': ['-', 2], '*': ['*', 2], '/': ['/', 2], '%': ['modulo', 2],
  '==': ['equal?', 2], '<': ['<', 2], '>': ['>', 2], '<=': ['<=', 2], '>=': ['>=', 2],
  '::': ['cons', 2],
  quotient: 2, remainder: 2, modulo: 2, abs: 1, min: 2, max: 2,
  not: 1, 'eq?': 2, 'equal?': 2,
  cons: 2, car: 1, cdr: 1, 'null?': 1, 'pair?': 1, 'number?': 1, 'string?': 1, 'symbol?': 1,
  'zero?': 1, 'even?': 1, 'odd?': 1,
  length: 1, append: 2, reverse: 1,
  string_append: ['string-append', 2], string_length: ['string-length', 1],
  number_to_string: ['number->string', 1],
  display: 1, write: 1, newline: 1, error: 1,           // newline 要寫成 `newline ()`
}).map(([k, v]) => [k, Array.isArray(v) ? v : [k, v]]));

const KEYWORDS = new Set(['let', 'letrec', 'in', 'if', 'then', 'else', 'true', 'false', 'nil']);
const SECTION_OPS = new Set(['+', '-', '*', '/', '%', '==', '<', '>', '<=', '>=', '::']);

let gensymN = 0;
const gensym = () => '%g' + (gensymN++);

/* ───────────── Lexer ───────────── */
function tokenize(src) {
  const toks = []; let i = 0, line = 1;
  const push = (k, v) => toks.push({ k, v, line });
  while (i < src.length) {
    const c = src[i];
    if (c === '\n') { line++; i++; continue; }
    if (/\s/.test(c)) { i++; continue; }
    if (c === '-' && src[i + 1] === '-') { while (i < src.length && src[i] !== '\n') i++; continue; }
    if (c === '"') {
      let s = ''; i++;
      while (i < src.length && src[i] !== '"') {
        if (src[i] === '\\') { i++; const e = src[i]; s += e === 'n' ? '\n' : e === 't' ? '\t' : e; }
        else { if (src[i] === '\n') line++; s += src[i]; }
        i++;
      }
      if (i >= src.length) throw new Error(`第 ${line} 行: 字串沒有結尾的引號`);
      i++; push('str', s); continue;
    }
    const rest = src.slice(i);
    let m;
    if ((m = /^\d+(\.\d+)?/.exec(rest))) { push('num', Number(m[0])); i += m[0].length; continue; }
    if (c === "'") {
      m = /^'([A-Za-z_][A-Za-z0-9_?!']*)/.exec(rest);
      if (!m) throw new Error(`第 ${line} 行: 錯誤的符號`);
      push('sym', m[1]); i += m[0].length; continue;
    }
    if ((m = /^[A-Za-z_][A-Za-z0-9_?!']*/.exec(rest))) {
      push(KEYWORDS.has(m[0]) ? 'kw' : 'id', m[0]); i += m[0].length; continue;
    }
    if (c === '\\' || c === 'λ') { push('lam'); i++; continue; }
    const two = rest.slice(0, 2);
    if (['::', '==', '!=', '<=', '>=', '&&', '||'].includes(two)) { push('op', two); i += 2; continue; }
    if ('+-*/%<>=.,;()[]'.includes(c)) { push('op', c); i++; continue; }
    throw new Error(`第 ${line} 行: 無法辨識的字元 "${c}"`);
  }
  return toks;
}

/* ───────────── Parser (產生 AST) ───────────── */
const num = v => ({ t: 'num', v });
const vr = name => ({ t: 'var', name });
const prim = (vm, args) => ({ t: 'prim', vm, args });
const lam = (param, body) => ({ t: 'lam', param, body });

const LEVELS = [
  { ops: ['||'] }, { ops: ['&&'] },
  { ops: ['==', '!=', '<', '>', '<=', '>='] },
  { ops: ['::'], right: true },
  { ops: ['+', '-'] }, { ops: ['*', '/', '%'] },
];
const OPMAP = { '+': '+', '-': '-', '*': '*', '/': '/', '%': 'modulo', '==': 'equal?',
                '<': '<', '>': '>', '<=': '<=', '>=': '>=', '::': 'cons' };

function mkBin(op, l, r) {
  if (op === '&&') return { t: 'if', c: l, a: r, b: { t: 'bool', v: false } };
  if (op === '||') { const g = gensym(); return { t: 'let', name: g, val: l, body: { t: 'if', c: vr(g), a: vr(g), b: r } }; }
  if (op === '!=') return prim('not', [prim('equal?', [l, r])]);
  return prim(OPMAP[op], [l, r]);
}

class Parser {
  constructor(toks) { this.t = toks; this.p = 0; }
  peek() { return this.t[this.p]; }
  next() { return this.t[this.p++]; }
  isOp(v) { const t = this.peek(); return !!t && t.k === 'op' && t.v === v; }
  isKw(v) { const t = this.peek(); return !!t && t.k === 'kw' && t.v === v; }
  err(msg) {
    const t = this.peek();
    throw new Error(t ? `第 ${t.line} 行: ${msg} (遇到 ${t.v === undefined ? '\\' : '"' + t.v + '"'})` : `${msg} (已到檔案結尾)`);
  }
  expectOp(v) { if (!this.isOp(v)) this.err(`需要 "${v}"`); return this.next(); }
  expectKw(v) { if (!this.isKw(v)) this.err(`需要 "${v}"`); return this.next(); }
  expectId() { const t = this.peek(); if (!t || t.k !== 'id') this.err('需要識別字'); return this.next().v; }

  parseProgram() {
    const items = [];
    while (this.peek()) {
      if (this.isOp(';')) { this.next(); continue; }
      items.push(this.parseItem());
      if (this.peek() && !this.isOp(';')) this.err('缺少 ";"');
    }
    return items;
  }

  parseBinding() {                     // 名稱 參數* = 運算式   (參數會包成 lambda)
    const name = this.expectId();
    const params = [];
    while (this.peek() && this.peek().k === 'id') params.push(this.next().v);
    this.expectOp('=');
    const val = params.reduceRight((b, p) => lam(p, b), this.parseExpr());
    return { name, val };
  }

  parseItem() {
    if (this.isKw('let') || this.isKw('letrec')) {
      const saved = this.p, rec = this.next().v === 'letrec';
      const { name, val } = this.parseBinding();
      if (this.isKw('in')) { this.p = saved; return { t: 'expr', e: this.parseExpr() }; }  // 其實是 let...in 運算式
      return { t: 'def', name, val, rec };
    }
    return { t: 'expr', e: this.parseExpr() };
  }

  parseExpr() {
    const t = this.peek();
    if (!t) this.err('運算式不完整');
    if (t.k === 'lam') {
      this.next();
      const params = [];
      while (this.peek() && this.peek().k === 'id') params.push(this.next().v);
      if (!params.length) this.err('lambda 需要至少一個參數');
      this.expectOp('.');
      return params.reduceRight((b, p) => lam(p, b), this.parseExpr());
    }
    if (this.isKw('let') || this.isKw('letrec')) {
      const rec = this.next().v === 'letrec';
      const { name, val } = this.parseBinding();
      this.expectKw('in');
      return { t: rec ? 'letrec' : 'let', name, val, body: this.parseExpr() };
    }
    if (this.isKw('if')) {
      this.next();
      const c = this.parseExpr(); this.expectKw('then');
      const a = this.parseExpr(); this.expectKw('else');
      return { t: 'if', c, a, b: this.parseExpr() };
    }
    return this.parseBin(0);
  }

  parseBin(lv) {
    if (lv >= LEVELS.length) return this.parseUnary();
    const L = LEVELS[lv];
    let left = this.parseBin(lv + 1);
    for (;;) {
      const t = this.peek();
      if (!(t && t.k === 'op' && L.ops.includes(t.v))) break;
      this.next();
      if (L.right) return mkBin(t.v, left, this.parseBin(lv));      // 右結合
      left = mkBin(t.v, left, this.parseBin(lv + 1));
    }
    return left;
  }

  startsExprKw() { return this.peek() && (this.peek().k === 'lam' || this.isKw('let') || this.isKw('letrec') || this.isKw('if')); }

  parseUnary() {
    if (this.isOp('-')) {
      this.next();
      const e = this.parseApp();
      return e.t === 'num' ? num(-e.v) : prim('-', [num(0), e]);
    }
    if (this.startsExprKw()) return this.parseExpr();
    return this.parseApp();
  }

  startsAtom() {
    const t = this.peek();
    if (!t) return false;
    if (['num', 'str', 'sym', 'id'].includes(t.k)) return true;
    if (t.k === 'kw') return ['true', 'false', 'nil'].includes(t.v);
    return t.k === 'op' && (t.v === '(' || t.v === '[');
  }

  parseApp() {
    let f = this.parseAtom();
    while (this.startsAtom()) f = { t: 'app', f, a: this.parseAtom() };
    if (this.startsExprKw()) f = { t: 'app', f, a: this.parseExpr() };   // f \x. ...  /  f if ...
    return f;
  }

  parseAtom() {
    const t = this.next();
    if (!t) this.err('運算式不完整');
    switch (t.k) {
      case 'num': return num(t.v);
      case 'str': return { t: 'str', v: t.v };
      case 'sym': return { t: 'sym', v: t.v };
      case 'id': return vr(t.v);
      case 'kw':
        if (t.v === 'true') return { t: 'bool', v: true };
        if (t.v === 'false') return { t: 'bool', v: false };
        if (t.v === 'nil') return { t: 'nil' };
        break;
      case 'op':
        if (t.v === '(') {
          if (this.isOp(')')) { this.next(); return { t: 'nil' }; }                    // ()
          const o = this.peek();
          if (o.k === 'op' && SECTION_OPS.has(o.v) && this.t[this.p + 1] && this.t[this.p + 1].v === ')' && this.t[this.p + 1].k === 'op') {
            this.p += 2; return vr(o.v);                                                  // (+)
          }
          const e = this.parseExpr(); this.expectOp(')'); return e;
        }
        if (t.v === '[') {
          const items = [];
          if (!this.isOp(']')) { items.push(this.parseExpr()); while (this.isOp(',')) { this.next(); items.push(this.parseExpr()); } }
          this.expectOp(']');
          return items.reduceRight((acc, x) => prim('cons', [x, acc]), { t: 'nil' });
        }
        break;
    }
    this.p--; this.err('無法解析的運算式');
  }
}

/* ───────────── 編譯器 (AST -> LBC) ───────────── */
function constJSON(n) {
  switch (n.t) {
    case 'num': case 'bool': return JSON.stringify(n.v);
    case 'str': return JSON.stringify(n.v);
    case 'sym': return JSON.stringify({ sym: n.v });
    case 'nil': return 'null';
  }
}

function expandPrim(name, args) {      // 將內建函式依 arity 展開 (多的參數 curried 套用，少的做 eta 展開)
  const [vm, k] = PRIMS.get(name);
  if (args.length >= k) {
    let node = prim(vm, args.slice(0, k));
    for (const a of args.slice(k)) node = { t: 'app', f: node, a };
    return node;
  }
  const given = args.map(a => ({ name: gensym(), val: a }));
  const missing = Array.from({ length: k - args.length }, gensym);
  let body = prim(vm, [...given.map(g => vr(g.name)), ...missing.map(vr)]);
  for (const m of missing.reverse()) body = lam(m, body);
  for (const g of given.reverse()) body = { t: 'app', f: lam(g.name, body), a: g.val };
  return body;
}

class Compiler {
  constructor() { this.funcs = []; this.funcN = 0; this.labelN = 0; }
  newLabel() { return 'L' + (this.labelN++); }

  compileProgram(items) {
    const main = { name: 'main', params: [], code: [] };
    this.funcs.push(main);
    const scope = new Set();                       // 已被使用者綁定的名稱 (遮蔽內建函式)
    items.forEach((it, i) => {
      if (it.t === 'def') {
        if (it.rec) scope.add(it.name);
        this.comp(it.val, main.code, false, scope, it.name);
        main.code.push(['DEF', it.name]);
        scope.add(it.name);
      } else this.comp(it.e, main.code, false, scope);
      if (i < items.length - 1) main.code.push(['POP']);
    });
    if (items.length === 0) main.code.push(['VOID']);
    main.code.push(['HALT']);
    return this.emit();
  }

  compileLam(n, scope, hint) {
    const name = `${hint || 'lambda'}#${this.funcN++}`;
    const fn = { name, params: [n.param], code: [] };
    this.funcs.push(fn);
    this.comp(n.body, fn.code, true, new Set(scope).add(n.param));
    return name;
  }

  comp(n, code, tail, scope, hint) {
    const ret = () => { if (tail) code.push(['RET']); };
    switch (n.t) {
      case 'num': case 'str': case 'bool': case 'sym': case 'nil':
        code.push(['CONST', constJSON(n)]); return ret();

      case 'var':
        if (PRIMS.has(n.name) && !scope.has(n.name)) return this.comp(expandPrim(n.name, []), code, tail, scope);
        code.push(['LOAD', n.name]); return ret();

      case 'lam':
        code.push(['CLOSURE', this.compileLam(n, scope, hint)]); return ret();

      case 'app': {                                   // 展平:  f a b c  ->  CALL 1 三次 (curried)
        const args = []; let h = n;
        while (h.t === 'app') { args.unshift(h.a); h = h.f; }
        if (h.t === 'var' && PRIMS.has(h.name) && !scope.has(h.name))
          return this.comp(expandPrim(h.name, args), code, tail, scope);
        this.comp(h, code, false, scope);
        args.forEach((a, i) => {
          this.comp(a, code, false, scope);
          code.push([tail && i === args.length - 1 ? 'TAILCALL' : 'CALL', 1]);
        });
        return;
      }

      case 'prim':
        code.push(['LOAD', n.vm]);
        for (const a of n.args) this.comp(a, code, false, scope);
        code.push([tail ? 'TAILCALL' : 'CALL', n.args.length]);
        return;

      case 'if': {
        const Lelse = this.newLabel();
        this.comp(n.c, code, false, scope);
        code.push(['JF', Lelse]);
        if (tail) {
          this.comp(n.a, code, true, scope);
          code.push(['LABEL', Lelse]);
          this.comp(n.b, code, true, scope);
        } else {
          const Lend = this.newLabel();
          this.comp(n.a, code, false, scope);
          code.push(['JMP', Lend]);
          code.push(['LABEL', Lelse]);
          this.comp(n.b, code, false, scope);
          code.push(['LABEL', Lend]);
        }
        return;
      }

      case 'let':                                     // let x = v in b   ==>   (\x. b) v
        return this.comp({ t: 'app', f: lam(n.name, n.body), a: n.val }, code, tail, scope);

      case 'letrec': {                                // 以一個 0 參數的 thunk 建立新環境，在裡面 DEF
        const thunk = { name: `letrec#${this.funcN++}`, params: [], code: [] };
        this.funcs.push(thunk);
        const sc = new Set(scope).add(n.name);
        this.comp(n.val, thunk.code, false, sc, n.name);
        thunk.code.push(['DEF', n.name], ['POP']);
        this.comp(n.body, thunk.code, true, sc);
        code.push(['CLOSURE', thunk.name]);
        code.push([tail ? 'TAILCALL' : 'CALL', 0]);
        return;
      }
    }
    throw new Error('無法編譯的節點: ' + n.t);
  }

  emit() {
    const out = ['; LBC v1 — generated by lambdac.js'];
    for (const f of this.funcs) {
      out.push(`.func ${f.name}${f.params.length ? ' ' + f.params.join(' ') : ''}`);
      for (const [op, arg] of f.code) {
        if (op === 'LABEL') out.push(`${arg}:`);
        else out.push(`  ${op}${arg === undefined ? '' : ' ' + arg}`);
      }
    }
    return out.join('\n') + '\n';
  }
}

function compile(src) { return new Compiler().compileProgram(new Parser(tokenize(src)).parseProgram()); }
module.exports = { compile };

/* ───────────── CLI ───────────── */
if (require.main === module) {
  const args = process.argv.slice(2);
  if (args.length === 0) { console.error('用法: node lambdac.js input.lc [-o output.lbc]'); process.exit(1); }
  const input = args[0];
  const oi = args.indexOf('-o');
  const output = oi >= 0 ? args[oi + 1] : input.replace(/\.[^.]*$/, '') + '.lbc';
  try {
    const bc = compile(fs.readFileSync(input, 'utf8'));
    if (output === '-') process.stdout.write(bc);
    else { fs.writeFileSync(output, bc); console.error(`已編譯 ${input} -> ${output}`); }
  } catch (e) { console.error('編譯錯誤: ' + e.message); process.exit(1); }
}