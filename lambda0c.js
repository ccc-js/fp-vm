#!/usr/bin/env node
'use strict';
/*
 * lambda0c.js  —  Church 式 Lambda Calculus  ->  LBC v1 中間碼 (經 Scheme 核心 + lispc.js，用 vm.js 執行)
 *
 * 用法:  node lambda0c.js input.l0 [-o output.lbc]      (-o - 輸出到 stdout)
 *        node lambda0c.js input.l0 --scheme             只印出中間產物 (Scheme 核心)，方便除錯
 *        node vm.js output.lbc
 *
 * ───────────────────────────── 設計 ─────────────────────────────
 *  重現 Church 1930 年代的做法:語言本身只有「命名 + 函數抽象 + 函數應用 + 整數」。
 *  沒有 if / true / false / letrec / 字串 / 串列關鍵字——
 *  TRUE、FALSE、IF、AND、PAIR、NIL…全由使用者以函數建構 (見 lambda0/ 範例)。
 *  唯一的務實放寬是有 primitive int (不必從 Church numeral 建起) 與 print (印出並換行)。
 *
 *  前綴運算子須恰接兩個原子參數 (+ x y 可，+ f x y 會把結果再應用——請加括號)；
 *  減法請用中綴 (n - 1)，前綴 (- n 1) 會被讀成 negation (與 lambdac.js 一致)；
 *  整數比較 (== != < > <= >=) 回傳「真正的 Church 布林」(可被使用者自定的 IF 應用):
 *  實作上展開為 (if (= a b) %TRUE %FALSE)，其中 %TRUE / %FALSE 是編譯器前置的
 *  普通 lambda (\x.\y.x)，if 借用 lispc 現成的特殊形式——source 語言依然純粹。
 *  VM (vm.js / vm2wasm.js) 完全不需修改。
 *
 *  求值是 call-by-value (繼承自 VM):Y 在此會無窮迴圈，請用 Z (見 03_ycombinator.l0)；
 *  Church 版 IF 的兩分支亦須包成 thunk (\d. …)，否則兩邊都先求值。
 *
 * ───────────────────────────── 語法 ─────────────────────────────
 *  程式    := 項目 ( ";" 項目 )* [";"]            -- 註解以 -- 開頭
 *  項目    := 名稱 "=" 運算式                     命名定義 (循序、不可遞迴；遞迴請用 Z)
 *           | 運算式                              求值 (如 print 42)
 *  運算式  := "\" 參數+ "." 運算式                lambda (也可寫 λ)；\x y. e 即 \x.\y. e
 *           | f a b c                             應用 (左結合；函數全為一元 curried)
 *           | 中綴: == != < > <= >= + - * / %      (優先序: 比較 < 加減 < 乘除)
 *           | 原子
 *  原子    := 整數 (十進位；負數寫 -5，函數參數中的負數須加括號 f (-5))
 *           | 變數 | "(" 運算式 ")" | print | 前綴運算子 原子 原子
 *  print   := 保留字，永遠是內建輸出 (印出並換行；定義 print 會報錯)
 *
 *  保留字 (不可定義): print display modulo
 */
const fs = require('fs');
const lispc = require('./lispc.js');

class L0Error extends Error {}
const fail = (line, msg) => { throw new L0Error(line ? `第 ${line} 行: ${msg}` : msg); };

const RESERVED_DEF = new Set(['print', 'display', 'modulo']);

/* ═════════════════════════ Lexer ═════════════════════════ */
function lex(src) {
  const toks = []; let i = 0, line = 1; const n = src.length;
  const push = (k, v) => toks.push({ k, v, line });
  while (i < n) {
    const c = src[i];
    if (c === '\n') { line++; i++; continue; }
    if (/\s/.test(c)) { i++; continue; }
    if (c === '-' && src[i + 1] === '-') { while (i < n && src[i] !== '\n') i++; continue; }
    if (/[0-9]/.test(c)) {
      const m = /^\d+/.exec(src.slice(i));
      push('int', Number(m[0])); i += m[0].length; continue;
    }
    if (/[A-Za-z_]/.test(c)) {
      const w = /^[A-Za-z_][A-Za-z0-9_]*/.exec(src.slice(i))[0];
      push('id', w); i += w.length; continue;
    }
    if (c === '\\' || c === 'λ') { push('lam', c); i += c.length; continue; }
    const two = src.slice(i, i + 2);
    if (['==', '!=', '<=', '>='].includes(two)) { push('op', two); i += 2; continue; }
    if ('=;.,()'.includes(c)) { push(c, c); i++; continue; }
    if ('+-*/%<>'.includes(c)) { push('op', c); i++; continue; }
    fail(line, `無法辨識的字元 "${c}"`);
  }
  push('eof', null);
  return toks;
}

/* ═════════════════════════ Parser (AST) ═════════════════════════ */
const num = (v, line) => ({ t: 'num', v, line });
const vr = (name, line) => ({ t: 'var', name, line });

class Parser {
  constructor(toks) { this.t = toks; this.p = 0; }
  peek(k = 0) { return this.t[Math.min(this.p + k, this.t.length - 1)]; }
  next() { return this.t[this.p++]; }
  expect(v) {
    const t = this.peek();
    if (!((t.k === 'op' || t.k === v) && t.v === v)) fail(t.line, `語法錯誤: 需要 "${v}"`);
    return this.next();
  }
  expectId() {
    const t = this.peek();
    if (t.k !== 'id') fail(t.line, '語法錯誤: 需要名稱');
    return this.next().v;
  }

  parseProgram() {
    const items = [];
    while (this.peek().k !== 'eof') {
      items.push(this.parseItem());
      if (this.peek().k !== 'eof') this.expect(';');
    }
    return items;
  }
  parseItem() {
    const t = this.peek();
    if (t.k === 'id' && this.peek(1).v === '=') {
      const line = t.line, name = this.next().v;
      this.next();
      if (RESERVED_DEF.has(name)) fail(line, `"${name}" 為保留字，請改名`);
      return { t: 'def', name, expr: this.parseExpr(), line };
    }
    return { t: 'expr', expr: this.parseExpr(), line: t.line };
  }
  parseExpr() { return this.parseLam(); }
  parseLam() {
    const t = this.peek();
    if (t.k === 'lam') {
      this.next();
      const params = [];
      for (;;) {
        const p = this.peek();
        if (p.k !== 'id') fail(p.line, '語法錯誤: lambda 需要參數名稱');
        params.push(this.next().v);
        if (this.peek().v === '.') break;
      }
      this.next();
      return { t: 'lam', params, body: this.parseExpr(), line: t.line };
    }
    return this.parseCmp();
  }
  parseCmp() {
    let l = this.parseAdd();
    for (;;) {
      const t = this.peek();
      if (t.k === 'op' && ['==', '!=', '<', '>', '<=', '>='].includes(t.v)) {
        this.next();
        l = { t: 'cmp', op: t.v, a: l, b: this.parseAdd(), line: t.line };
      } else break;
    }
    return l;
  }
  parseAdd() {
    let l = this.parseMul();
    for (;;) {
      const t = this.peek();
      if (t.k === 'op' && (t.v === '+' || t.v === '-')) {
        this.next();
        l = { t: 'prim', op: t.v, args: [l, this.parseMul()], line: t.line };
      } else break;
    }
    return l;
  }
  parseMul() {
    let l = this.parseUnary();
    for (;;) {
      const t = this.peek();
      if (t.k === 'op' && (t.v === '*' || t.v === '/' || t.v === '%')) {
        this.next();
        l = { t: 'prim', op: t.v === '%' ? 'modulo' : t.v, args: [l, this.parseUnary()], line: t.line };
      } else break;
    }
    return l;
  }
  parseUnary() {
    const t = this.peek();
    if (t.k === 'op' && t.v === '-') {
      this.next();
      const e = this.parseUnary();
      if (e.t === 'num') return num(-e.v, t.line);
      return { t: 'prim', op: '-', args: [num(0, t.line), e], line: t.line };
    }
    return this.parseApp();
  }
  parseApp() {
    const f = this.parseAtom(), args = [];
    for (;;) {
      const t = this.peek();
      if (t.k === 'int' || t.k === 'id' || t.v === '(') args.push(this.parseAtom());
      else break;
    }
    return args.length ? { t: 'app', f, args, line: f.line } : f;
  }
  parseAtom() {
    const t = this.next();
    if (t.k === 'int') return num(t.v, t.line);
    if (t.k === 'id') return vr(t.v, t.line);
    if (t.k === 'op' && t.v !== '-') {               // 前綴運算子: + x y (恰接兩個原子參數；- 除外，由一元負號處理)
      const a = this.parseAtom(), b = this.parseAtom();
      if ('+*/%'.includes(t.v)) return { t: 'prim', op: t.v === '%' ? 'modulo' : t.v, args: [a, b], line: t.line };
      return { t: 'cmp', op: t.v, a, b, line: t.line };
    }
    if (t.v === '(') {
      const e = this.parseExpr();
      this.expect(')');
      return e;
    }
    fail(t.line, '語法錯誤: 無法解析的運算式');
  }
}

/* ═════════════════════════ Codegen: AST -> Scheme 原始碼 ═════════════════════════ */
const showS = x => Array.isArray(x) ? '(' + x.map(showS).join(' ') + ')' : String(x);

function gen(e) {
  switch (e.t) {
    case 'num': return e.v;
    case 'var': return e.name === 'print' ? 'display' : e.name;
    case 'lam': return e.params.reduceRight((b, p) => ['lambda', [p], b], gen(e.body));
    case 'app': {
      if (e.f.t === 'var' && e.f.name === 'print' && e.args.length === 1)
        return ['begin', ['display', gen(e.args[0])], ['newline']];   // print 印出並換行
      return e.args.reduce((f, a) => [f, gen(a)], gen(e.f));   // 一元 curried 左結合
    }
    case 'prim': return [e.op, ...e.args.map(gen)];
    case 'cmp': {                                                        // 比較回傳 Church 布林
      const test = { '==': '=', '!=': '=', '<': '<', '>': '>', '<=': '<=', '>=': '>=' }[e.op];
      const branches = e.op === '!=' ? ['%FALSE', '%TRUE'] : ['%TRUE', '%FALSE'];
      return ['if', [test, gen(e.a), gen(e.b)], ...branches];
    }
  }
  throw new Error('gen: 未知節點 ' + e.t);
}

function toScheme(src) {
  const items = new Parser(lex(src)).parseProgram();
  const out = [
    ['define', '%TRUE', ['lambda', ['x'], ['lambda', ['y'], 'x']]],
    ['define', '%FALSE', ['lambda', ['x'], ['lambda', ['y'], 'y']]],
  ];
  for (const it of items) {
    if (it.t === 'def') out.push(['define', it.name, gen(it.expr)]);
    else out.push(gen(it.expr));
  }
  return out.map(showS).join('\n') + '\n';
}

function compile(src) { return lispc.compile(toScheme(src)); }
module.exports = { compile, toScheme };

/* ═════════════════════════ CLI ═════════════════════════ */
if (require.main === module) {
  const args = process.argv.slice(2);
  if (!args.length) { console.error('用法: node lambda0c.js input.l0 [-o output.lbc] [--scheme]'); process.exit(1); }
  const input = args.find((a, i) => !a.startsWith('-') && args[i - 1] !== '-o');
  const oi = args.indexOf('-o');
  const output = oi >= 0 ? args[oi + 1] : input.replace(/\.[^.]*$/, '') + '.lbc';
  try {
    if (args.includes('--scheme')) process.stdout.write(toScheme(fs.readFileSync(input, 'utf8')));
    else {
      const bc = compile(fs.readFileSync(input, 'utf8'));
      if (output === '-') process.stdout.write(bc);
      else { fs.writeFileSync(output, bc); console.error(`已編譯 ${input} -> ${output}`); }
    }
  } catch (e) {
    if (e instanceof L0Error) { console.error('編譯錯誤: ' + e.message); process.exit(1); }
    console.error('編譯錯誤: ' + e.message); process.exit(1);
  }
}
