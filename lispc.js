#!/usr/bin/env node
'use strict';
/*
 * lispc.js  —  迷你 Scheme 風格 Lisp  ->  中間碼 (.lbc) 編譯器
 *
 * 用法:  node lispc.js input.lisp [-o output.lbc]      (-o - 輸出到 stdout)
 *
 * ───────────────────────── 中間碼格式 (LBC v1) ─────────────────────────
 * 文字檔、一行一個項目，堆疊式 (stack-based) 虛擬機。
 *
 *   ; 註解 (必須在行首)
 *   .func NAME p1 p2 ... [. rest]   開始一個函式 (第一個必為 main)
 *   Lk:                              標籤 (函式內區域有效)
 *     OP [ARG]                       指令
 *
 * 規則: 每個「運算式」恰好在堆疊上留下 1 個值。
 *
 * 指令集:
 *   CONST <json>   推入常數。json: 數字 | true/false | "字串" | null(空串列)
 *                  | {"sym":"名稱"} | {"list":[...]}
 *   VOID           推入「未定義值」(define / set! 等的回傳)
 *   LOAD name      讀變數
 *   DEF  name      彈出值並在目前環境定義變數，推入 VOID
 *   SET  name      彈出值並修改已存在變數 (set!)，推入 VOID
 *   POP            丟棄堆疊頂端
 *   JMP  L         無條件跳躍
 *   JF   L         彈出值，若為 #f 則跳躍
 *   CLOSURE fname  以目前環境建立閉包 (fname 為 .func 名稱)
 *   CALL n         呼叫: 堆疊 [... f a1..an] -> 結果
 *   TAILCALL n     尾呼叫 (重用目前框架，達成尾遞迴最佳化)
 *   RET            從函式返回 (回傳值在堆疊頂端)
 *   HALT           結束程式
 */
const fs = require('fs');

/* ───────────── 資料型別與 Reader ───────────── */
class Sym { constructor(n) { this.name = n; } }
const symtab = new Map();
const intern = n => { let s = symtab.get(n); if (!s) symtab.set(n, s = new Sym(n)); return s; };
class Str { constructor(v) { this.v = v; } }

function tokenize(src) {
  const toks = []; let i = 0;
  while (i < src.length) {
    const c = src[i];
    if (/\s/.test(c)) { i++; continue; }
    if (c === ';') { while (i < src.length && src[i] !== '\n') i++; continue; }
    if (c === '(' || c === ')' || c === "'") { toks.push(c); i++; continue; }
    if (c === '"') {
      let s = ''; i++;
      while (i < src.length && src[i] !== '"') {
        if (src[i] === '\\') { i++; const e = src[i]; s += e === 'n' ? '\n' : e === 't' ? '\t' : e; }
        else s += src[i];
        i++;
      }
      if (i >= src.length) throw new Error('字串沒有結尾的引號');
      i++; toks.push({ str: s }); continue;
    }
    let j = i;
    while (j < src.length && !/[\s()';"]/.test(src[j])) j++;
    toks.push(src.slice(i, j)); i = j;
  }
  return toks;
}

function parse(src) {
  const toks = tokenize(src); let p = 0;
  function read() {
    if (p >= toks.length) throw new Error('意外的檔案結尾 (缺少 ")" ?)');
    const t = toks[p++];
    if (typeof t === 'object') return new Str(t.str);
    if (t === '(') {
      const lst = [];
      for (;;) {
        if (p >= toks.length) throw new Error('缺少 ")"');
        if (toks[p] === ')') { p++; break; }
        lst.push(read());
      }
      return lst;
    }
    if (t === ')') throw new Error('多餘的 ")"');
    if (t === "'") return [intern('quote'), read()];
    if (/^[-+]?(\d+\.?\d*|\.\d+)$/.test(t)) return Number(t);
    if (t === '#t' || t === '#true') return true;
    if (t === '#f' || t === '#false') return false;
    return intern(t);
  }
  const forms = [];
  while (p < toks.length) forms.push(read());
  return forms;
}

/* 把 quote 的資料轉成 JSON 常數 */
function toDatum(x) {
  if (typeof x === 'number' || typeof x === 'boolean') return x;
  if (x instanceof Str) return x.v;
  if (x instanceof Sym) return { sym: x.name };
  if (Array.isArray(x)) return x.length === 0 ? null : { list: x.map(toDatum) };
  throw new Error('無法 quote: ' + x);
}
const constJSON = x => JSON.stringify(toDatum(x));

/* ───────────── 編譯器 ───────────── */
const S = intern;
class Compiler {
  constructor() { this.funcs = []; this.labelN = 0; this.funcN = 0; this.gensymN = 0; }
  newLabel() { return 'L' + (this.labelN++); }
  gensym() { return S('%t' + (this.gensymN++)); }

  compileProgram(forms) {
    const main = { name: 'main', params: [], code: [] };
    this.funcs.push(main);
    forms.forEach((f, i) => {
      this.comp(f, main.code, false);
      if (i < forms.length - 1) main.code.push(['POP']);
    });
    if (forms.length === 0) main.code.push(['VOID']);
    main.code.push(['HALT']);
    return this.emit();
  }

  compileLambda(params, body, hint) {
    if (body.length === 0) throw new Error('lambda 的 body 不可為空');
    const name = `${hint || 'lambda'}#${this.funcN++}`;
    const ps = [];
    if (params instanceof Sym) ps.push('.', params.name);            // (lambda args ...)
    else for (const p of params) {
      if (!(p instanceof Sym)) throw new Error('參數必須是符號');
      ps.push(p.name);
    }
    const fn = { name, params: ps, code: [] };
    this.funcs.push(fn);
    this.compBody(body, fn.code, true);
    return name;
  }

  compBody(body, code, tail) {           // 序列 (begin)
    if (body.length === 0) { code.push(['VOID']); if (tail) code.push(['RET']); return; }
    body.forEach((e, i) => {
      const last = i === body.length - 1;
      this.comp(e, code, last && tail);
      if (!last) code.push(['POP']);
    });
  }

  comp(x, code, tail) {
    const ret = () => { if (tail) code.push(['RET']); };

    if (typeof x === 'number' || typeof x === 'boolean' || x instanceof Str) {
      code.push(['CONST', constJSON(x)]); return ret();
    }
    if (x instanceof Sym) { code.push(['LOAD', x.name]); return ret(); }
    if (!Array.isArray(x)) throw new Error('無法編譯: ' + x);
    if (x.length === 0) throw new Error('空的應用 ()');

    const head = x[0];
    if (head instanceof Sym) {
      switch (head.name) {
        case 'quote':
          code.push(['CONST', constJSON(x[1])]); return ret();

        case 'if': {
          const [, c, t, e] = x;
          const Lelse = this.newLabel();
          this.comp(c, code, false);
          code.push(['JF', Lelse]);
          if (tail) {                                   // 兩個分支各自 RET / TAILCALL
            this.comp(t, code, true);
            code.push(['LABEL', Lelse]);
            if (e === undefined) { code.push(['VOID']); code.push(['RET']); }
            else this.comp(e, code, true);
          } else {
            const Lend = this.newLabel();
            this.comp(t, code, false);
            code.push(['JMP', Lend]);
            code.push(['LABEL', Lelse]);
            if (e === undefined) code.push(['VOID']); else this.comp(e, code, false);
            code.push(['LABEL', Lend]);
          }
          return;
        }

        case 'define': {
          let name, valueCode;
          if (Array.isArray(x[1])) {                    // (define (f a b) body...)
            name = x[1][0].name;
            const fname = this.compileLambda(x[1].slice(1), x.slice(2), name);
            valueCode = ['CLOSURE', fname];
          } else {
            name = x[1].name;
            if (x[2] instanceof Array && x[2][0] === S('lambda')) {
              valueCode = ['CLOSURE', this.compileLambda(x[2][1], x[2].slice(2), name)];
            } else { this.comp(x[2], code, false); valueCode = null; }
          }
          if (valueCode) code.push(valueCode);
          code.push(['DEF', name]);
          return ret();
        }

        case 'set!':
          this.comp(x[2], code, false);
          code.push(['SET', x[1].name]);
          return ret();

        case 'lambda':
          code.push(['CLOSURE', this.compileLambda(x[1], x.slice(2))]);
          return ret();

        case 'begin':
          return this.compBody(x.slice(1), code, tail);

        case 'let': {
          if (x[1] instanceof Sym) {                    // 具名 let
            const name = x[1], binds = x[2];
            const vars = binds.map(b => b[0]), vals = binds.map(b => b[1]);
            const loopDef = [S('define'), name, [S('lambda'), vars, ...x.slice(3)]];
            return this.comp([[[S('lambda'), [], loopDef, name]], ...vals], code, tail);
          }
          const binds = x[1];
          return this.comp([[S('lambda'), binds.map(b => b[0]), ...x.slice(2)], ...binds.map(b => b[1])], code, tail);
        }
        case 'let*': {
          const binds = x[1];
          if (binds.length <= 1) return this.comp([S('let'), binds, ...x.slice(2)], code, tail);
          return this.comp([S('let'), [binds[0]], [S('let*'), binds.slice(1), ...x.slice(2)]], code, tail);
        }
        case 'letrec': {
          const defs = x[1].map(b => [S('define'), b[0], b[1]]);
          return this.comp([[S('lambda'), [], ...defs, ...x.slice(2)]], code, tail);
        }

        case 'cond': {
          const build = (cl) => {
            if (cl.length === 0) return undefined;
            const [test, ...body] = cl[0];
            if (test === S('else')) return [S('begin'), ...body];
            if (body.length === 0) return [S('or'), test, build(cl.slice(1)) ?? false];
            const rest = build(cl.slice(1));
            return rest === undefined ? [S('if'), test, [S('begin'), ...body]]
                                      : [S('if'), test, [S('begin'), ...body], rest];
          };
          const e = build(x.slice(1));
          if (e === undefined) { code.push(['VOID']); return ret(); }
          return this.comp(e, code, tail);
        }

        case 'and': {
          const a = x.slice(1);
          if (a.length === 0) return this.comp(true, code, tail);
          if (a.length === 1) return this.comp(a[0], code, tail);
          return this.comp([S('if'), a[0], [S('and'), ...a.slice(1)], false], code, tail);
        }
        case 'or': {
          const a = x.slice(1);
          if (a.length === 0) return this.comp(false, code, tail);
          if (a.length === 1) return this.comp(a[0], code, tail);
          const t = this.gensym();
          return this.comp([S('let'), [[t, a[0]]], [S('if'), t, t, [S('or'), ...a.slice(1)]]], code, tail);
        }
        case 'when':
          return this.comp([S('if'), x[1], [S('begin'), ...x.slice(2)]], code, tail);
        case 'unless':
          return this.comp([S('if'), [S('not'), x[1]], [S('begin'), ...x.slice(2)]], code, tail);
      }
    }

    /* 一般函式應用 */
    this.comp(head, code, false);
    const args = x.slice(1);
    for (const a of args) this.comp(a, code, false);
    code.push([tail ? 'TAILCALL' : 'CALL', args.length]);
  }

  emit() {
    const out = ['; LBC v1 — generated by lispc.js'];
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

function compile(src) { return new Compiler().compileProgram(parse(src)); }
module.exports = { compile, parse };

/* ───────────── CLI ───────────── */
if (require.main === module) {
  const args = process.argv.slice(2);
  if (args.length === 0) { console.error('用法: node lispc.js input.lisp [-o output.lbc]'); process.exit(1); }
  const input = args[0];
  const oi = args.indexOf('-o');
  const output = oi >= 0 ? args[oi + 1] : input.replace(/\.[^.]*$/, '') + '.lbc';
  try {
    const bc = compile(fs.readFileSync(input, 'utf8'));
    if (output === '-') process.stdout.write(bc);
    else { fs.writeFileSync(output, bc); console.error(`已編譯 ${input} -> ${output}`); }
  } catch (e) { console.error('編譯錯誤: ' + e.message); process.exit(1); }
}
