#!/usr/bin/env node
'use strict';
/*
 * lispvm.js  —  執行 lispc.js 產生的中間碼 (.lbc)
 * 用法:  node lispvm.js program.lbc
 * 指令集與格式請見 lispc.js 檔頭註解。
 */
const fs = require('fs');

/* ───────────── 執行期資料型別 ───────────── */
class Sym { constructor(n) { this.name = n; } }
const symtab = new Map();
const intern = n => { let s = symtab.get(n); if (!s) symtab.set(n, s = new Sym(n)); return s; };
class Pair { constructor(car, cdr) { this.car = car; this.cdr = cdr; } }   // 空串列 = null
const VOID = { void: true };
class Closure { constructor(fn, env) { this.fn = fn; this.env = env; } }
class Env {
  constructor(parent) { this.vars = new Map(); this.parent = parent; }
  lookup(name) { for (let e = this; e; e = e.parent) if (e.vars.has(name)) return e; return null; }
}

const fromDatum = d => {
  if (d === null || typeof d !== 'object') return d;
  if ('sym' in d) return intern(d.sym);
  if ('list' in d) { let r = null; for (let i = d.list.length - 1; i >= 0; i--) r = new Pair(fromDatum(d.list[i]), r); return r; }
  throw new Error('錯誤的常數: ' + JSON.stringify(d));
};
const arrayToList = a => { let r = null; for (let i = a.length - 1; i >= 0; i--) r = new Pair(a[i], r); return r; };
const listToArray = l => { const a = []; for (; l instanceof Pair; l = l.cdr) a.push(l.car); return a; };

function toStr(v, write) {
  if (v === null) return '()';
  if (v === true) return '#t';
  if (v === false) return '#f';
  if (v === VOID) return '';
  if (typeof v === 'number') return String(v);
  if (typeof v === 'string') return write ? JSON.stringify(v) : v;
  if (v instanceof Sym) return v.name;
  if (v instanceof Closure) return `#<procedure ${v.fn.name}>`;
  if (typeof v === 'function') return '#<primitive>';
  if (v instanceof Pair) {
    const parts = []; let p = v;
    for (; p instanceof Pair; p = p.cdr) parts.push(toStr(p.car, write));
    return '(' + parts.join(' ') + (p === null ? '' : ' . ' + toStr(p, write)) + ')';
  }
  return String(v);
}
const equal = (a, b) =>
  a instanceof Pair && b instanceof Pair ? equal(a.car, b.car) && equal(a.cdr, b.cdr) : a === b;

/* ───────────── 內建函式 ───────────── */
const num = (x, who) => { if (typeof x !== 'number') throw new Error(`${who}: 需要數字，得到 ${toStr(x, true)}`); return x; };
const cmp = (name, f) => (...a) => { for (let i = 0; i < a.length - 1; i++) if (!f(num(a[i], name), num(a[i + 1], name))) return false; return true; };
const out = s => process.stdout.write(s);

const primitives = {
  '+': (...a) => a.reduce((x, y) => x + num(y, '+'), 0),
  '*': (...a) => a.reduce((x, y) => x * num(y, '*'), 1),
  '-': (...a) => a.length === 1 ? -num(a[0], '-') : a.slice(1).reduce((x, y) => x - num(y, '-'), num(a[0], '-')),
  '/': (...a) => a.length === 1 ? 1 / a[0] : a.slice(1).reduce((x, y) => { if (y === 0) throw new Error('/: 除以零'); return x / y; }, a[0]),
  'quotient': (a, b) => Math.trunc(a / b),
  'remainder': (a, b) => a % b,
  'modulo': (a, b) => ((a % b) + b) % b,
  '=': cmp('=', (a, b) => a === b), '<': cmp('<', (a, b) => a < b), '>': cmp('>', (a, b) => a > b),
  '<=': cmp('<=', (a, b) => a <= b), '>=': cmp('>=', (a, b) => a >= b),
  'abs': Math.abs, 'min': Math.min, 'max': Math.max,
  'zero?': a => a === 0, 'even?': a => a % 2 === 0, 'odd?': a => Math.abs(a % 2) === 1,
  'not': a => a === false,
  'eq?': (a, b) => a === b, 'eqv?': (a, b) => a === b, 'equal?': equal,
  'cons': (a, b) => new Pair(a, b),
  'car': p => { if (!(p instanceof Pair)) throw new Error('car: 不是 pair: ' + toStr(p, true)); return p.car; },
  'cdr': p => { if (!(p instanceof Pair)) throw new Error('cdr: 不是 pair: ' + toStr(p, true)); return p.cdr; },
  'cadr': p => p.cdr.car, 'cddr': p => p.cdr.cdr, 'caddr': p => p.cdr.cdr.car,
  'list': (...a) => arrayToList(a),
  'length': l => listToArray(l).length,
  'append': (...ls) => arrayToList(ls.flatMap(listToArray)),
  'reverse': l => arrayToList(listToArray(l).reverse()),
  'null?': a => a === null,
  'pair?': a => a instanceof Pair,
  'number?': a => typeof a === 'number',
  'string?': a => typeof a === 'string',
  'symbol?': a => a instanceof Sym,
  'procedure?': a => a instanceof Closure || typeof a === 'function',
  'string-append': (...a) => a.join(''),
  'string-length': s => s.length,
  'number->string': n => String(n),
  'display': a => { out(toStr(a, false)); return VOID; },
  'write': a => { out(toStr(a, true)); return VOID; },
  'newline': () => { out('\n'); return VOID; },
  'error': (...a) => { throw new Error(a.map(x => toStr(x, false)).join(' ')); },
};

/* ───────────── 載入中間碼 ───────────── */
function load(text) {
  const funcs = new Map(); let cur = null;
  text.split('\n').forEach((raw, ln) => {
    const line = raw.trim();
    if (!line || line[0] === ';') return;
    if (line.startsWith('.func')) {
      const parts = line.split(/\s+/);
      let params = parts.slice(2), rest = null;
      const di = params.indexOf('.');
      if (di >= 0) { rest = params[di + 1]; params = params.slice(0, di); }
      cur = { name: parts[1], params, rest, code: [], labels: new Map() };
      funcs.set(cur.name, cur); return;
    }
    if (!cur) throw new Error(`第 ${ln + 1} 行: 指令不在 .func 內`);
    if (/^[A-Za-z0-9_]+:$/.test(line)) { cur.labels.set(line.slice(0, -1), cur.code.length); return; }
    const sp = line.indexOf(' ');
    const op = sp < 0 ? line : line.slice(0, sp);
    let arg = sp < 0 ? null : line.slice(sp + 1).trim();
    if (op === 'CONST') arg = fromDatum(JSON.parse(arg));
    else if (op === 'CALL' || op === 'TAILCALL') arg = Number(arg);
    cur.code.push([op, arg]);
  });
  for (const f of funcs.values()) {              // 解析標籤與函式參照
    for (const ins of f.code) {
      if (ins[0] === 'JMP' || ins[0] === 'JF') {
        const t = f.labels.get(ins[1]);
        if (t === undefined) throw new Error(`函式 ${f.name}: 找不到標籤 ${ins[1]}`);
        ins[1] = t;
      } else if (ins[0] === 'CLOSURE') {
        const t = funcs.get(ins[1]);
        if (!t) throw new Error(`找不到函式 ${ins[1]}`);
        ins[1] = t;
      }
    }
  }
  if (!funcs.has('main')) throw new Error('缺少 main 函式');
  return funcs;
}

/* ───────────── 虛擬機 ───────────── */
function run(funcs) {
  const global = new Env(null);
  for (const [k, v] of Object.entries(primitives)) global.vars.set(k, v);

  const stack = [];
  const frames = [];                              // 呼叫堆疊 (放在 heap，不吃 JS 堆疊)
  let code = funcs.get('main').code, pc = 0, env = global;

  for (;;) {
    const [op, arg] = code[pc++];
    switch (op) {
      case 'CONST': stack.push(arg); break;
      case 'VOID': stack.push(VOID); break;
      case 'LOAD': {
        const e = env.lookup(arg);
        if (!e) throw new Error('未定義的變數: ' + arg);
        stack.push(e.vars.get(arg)); break;
      }
      case 'DEF': env.vars.set(arg, stack.pop()); stack.push(VOID); break;
      case 'SET': {
        const e = env.lookup(arg);
        if (!e) throw new Error('set!: 未定義的變數: ' + arg);
        e.vars.set(arg, stack.pop()); stack.push(VOID); break;
      }
      case 'POP': stack.pop(); break;
      case 'JMP': pc = arg; break;
      case 'JF': if (stack.pop() === false) pc = arg; break;
      case 'CLOSURE': stack.push(new Closure(arg, env)); break;

      case 'CALL':
      case 'TAILCALL': {
        const args = stack.splice(stack.length - arg, arg);
        const f = stack.pop();
        if (f instanceof Closure) {
          const fn = f.fn, ne = new Env(f.env);
          const np = fn.params.length;
          if (fn.rest === null ? args.length !== np : args.length < np)
            throw new Error(`${fn.name}: 參數個數錯誤 (需要 ${np}${fn.rest ? '+' : ''}，得到 ${args.length})`);
          for (let i = 0; i < np; i++) ne.vars.set(fn.params[i], args[i]);
          if (fn.rest !== null) ne.vars.set(fn.rest, arrayToList(args.slice(np)));
          if (op === 'CALL') frames.push({ code, pc, env });   // TAILCALL: 直接取代目前框架
          code = fn.code; pc = 0; env = ne;
        } else if (typeof f === 'function') {
          stack.push(f(...args));
          if (op === 'TAILCALL') {                              // 等同 RET
            if (frames.length === 0) return stack.pop();
            ({ code, pc, env } = frames.pop());
          }
        } else throw new Error('不是可呼叫的物件: ' + toStr(f, true));
        break;
      }
      case 'RET':
        if (frames.length === 0) return stack.pop();
        ({ code, pc, env } = frames.pop());
        break;
      case 'HALT': return stack.length ? stack.pop() : VOID;
      default: throw new Error('未知的指令: ' + op);
    }
  }
}

function execute(text) { return run(load(text)); }
module.exports = { load, run, execute, toStr };

/* ───────────── CLI ───────────── */
if (require.main === module) {
  if (process.argv.length < 3) { console.error('用法: node lispvm.js program.lbc'); process.exit(1); }
  try { execute(fs.readFileSync(process.argv[2], 'utf8')); }
  catch (e) { console.error('執行錯誤: ' + e.message); process.exit(1); }
}
