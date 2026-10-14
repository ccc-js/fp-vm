#!/usr/bin/env node
'use strict';
/*
 * vm.js  —  執行 lispc.js 產生的中間碼 (.lbc)
 * 用法:  node vm.js program.lbc
 * 指令集與格式請見 lispc.js 檔頭註解。
 */
const fs = require('fs');

/* ───────────── 執行期資料型別 ───────────── */
class Sym { constructor(n) { this.name = n; } }
const symtab = new Map();
const intern = n => { let s = symtab.get(n); if (!s) symtab.set(n, s = new Sym(n)); return s; };
class Pair { constructor(car, cdr) { this.car = car; this.cdr = cdr; } }   // 空串列 = null
class Vec { constructor(a) { this.a = a; } }              // 'a array / bytes 底層 (bytes 以 Vec<int> 表示字元碼)
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
  if (v instanceof Vec) return '[|' + v.a.map(x => toStr(x, write)).join('; ') + '|]';
  return String(v);
}
const equal = (a, b) => {
  if (a instanceof Pair && b instanceof Pair) return equal(a.car, b.car) && equal(a.cdr, b.cdr);
  if (a instanceof Vec && b instanceof Vec)
    return a.a.length === b.a.length && a.a.every((x, i) => equal(x, b.a[i]));
  return a === b;
};
/* 結構比較: 數字 < 字串(char 視為 1 字元字串) < 符號 < 空串列 < 布林 < pair/list < Vec */
const cmpVal = (a, b) => {
  const rank = v =>
    typeof v === 'number' ? 0 : typeof v === 'string' ? 1 : v instanceof Sym ? 2 : v === null ? 3
    : typeof v === 'boolean' ? 4 : v instanceof Pair ? 5 : v instanceof Vec ? 6 : -1;
  const ra = rank(a), rb = rank(b);
  if (ra < 0 || rb < 0) throw new Error('compare: 不支援函式或 void 的比較');
  if (ra !== rb) return ra < rb ? -1 : 1;
  switch (ra) {
    case 0: return a < b ? -1 : a > b ? 1 : 0;
    case 1: return a < b ? -1 : a > b ? 1 : 0;
    case 2: return a.name < b.name ? -1 : a.name > b.name ? 1 : 0;
    case 3: return 0;
    case 4: return a === b ? 0 : a === false ? -1 : 1;
    case 5: { const c = cmpVal(a.car, b.car); return c !== 0 ? c : cmpVal(a.cdr, b.cdr); }
    case 6: {
      if (a.a.length !== b.a.length) return a.a.length < b.a.length ? -1 : 1;
      for (let i = 0; i < a.a.length; i++) { const c = cmpVal(a.a[i], b.a[i]); if (c !== 0) return c; }
      return 0;
    }
  }
  return 0;
};
/* 結構雜湊 (與 vm2wasm.js 的 hash 演算法相同，確保兩邊輸出一致) */
const hashVal = v => {
  const mix = h => ((h | 0) * 31 | 0) & 0x3fffffff;
  const strH = s => { let h = 0; for (let i = 0; i < s.length; i++) h = mix(h + s.charCodeAt(i)); return h; };
  const go = (v, d) => {
    if (typeof v === 'number') return mix(v | 0) ^ mix(Math.floor(Math.abs(v % 1) * 1e9));
    if (typeof v === 'string') return strH('s' + v);
    if (v instanceof Sym) return strH('k' + v.name);
    if (v === null) return 0x1a2b3c;
    if (v === true) return 0x111; if (v === false) return 0x222;
    if (d <= 0) return 0x777;
    if (v instanceof Pair) return mix(go(v.car, d - 1)) ^ (mix(go(v.cdr, d - 1)) + 0x9e37);
    if (v instanceof Vec) { let h = v.a.length; for (const x of v.a) h = mix(h) ^ go(x, d - 1); return h; }
    throw new Error('hash: 不支援函式或 void 的雜湊');
  };
  return go(v, 8);
};

/* ───────────── 內建函式 ───────────── */
const num = (x, who) => { if (typeof x !== 'number') throw new Error(`${who}: 需要數字，得到 ${toStr(x, true)}`); return x; };
const int32 = (x, who) => num(x, who) | 0;
const str = (x, who) => { if (typeof x !== 'string') throw new Error(`${who}: 需要字串，得到 ${toStr(x, true)}`); return x; };
const chr1 = (x, who) => { if (typeof x !== 'string' || x.length !== 1) throw new Error(`${who}: 需要字元，得到 ${toStr(x, true)}`); return x; };
const pair = (x, who) => { if (!(x instanceof Pair)) throw new Error(`${who}: 不是 pair: ` + toStr(x, true)); return x; };
const vec = (x, who) => { if (!(x instanceof Vec)) throw new Error(`${who}: 不是陣列，得到 ${toStr(x, true)}`); return x; };
const vecIdx = (v, i, who) => {
  const n = num(i, who);
  if (!Number.isInteger(n) || n < 0 || n >= v.a.length) throw new Error(`${who}: 索引超出範圍 ${toStr(i, true)} (長度 ${v.a.length})`);
  return n;
};
/* 比較: 數字與數字、字串與字串可比 (字串為字典序)；混合型別報錯 */
const cmp2 = (name, f) => (...a) => {
  for (let i = 0; i < a.length - 1; i++) {
    const x = a[i], y = a[i + 1];
    const ok = typeof x === 'number' && typeof y === 'number' ? f(x, y)
      : typeof x === 'string' && typeof y === 'string' ? f(x < y ? -1 : x > y ? 1 : 0, 0)
      : null;
    if (ok === null) throw new Error(`${name}: 需要兩個數字或兩個字串，得到 ${toStr(x, true)} 與 ${toStr(y, true)}`);
    if (!ok) return false;
  }
  return true;
};
const out = s => process.stdout.write(s);

const primitives = {
  '+': (...a) => a.reduce((x, y) => x + num(y, '+'), 0),
  '*': (...a) => a.reduce((x, y) => x * num(y, '*'), 1),
  '-': (...a) => a.length === 1 ? -num(a[0], '-') : a.slice(1).reduce((x, y) => x - num(y, '-'), num(a[0], '-')),
  '/': (...a) => a.length === 1 ? 1 / a[0] : a.slice(1).reduce((x, y) => { if (y === 0) throw new Error('/: 除以零'); return x / y; }, a[0]),
  'quotient': (a, b) => Math.trunc(a / b),
  'remainder': (a, b) => a % b,
  'modulo': (a, b) => ((a % b) + b) % b,
  '=': cmp2('=', (a, b) => a === b), '<': cmp2('<', (a, b) => a < b), '>': cmp2('>', (a, b) => a > b),
  '<=': cmp2('<=', (a, b) => a <= b), '>=': cmp2('>=', (a, b) => a >= b),
  'abs': Math.abs, 'min': Math.min, 'max': Math.max,
  'sqrt': a => Math.sqrt(num(a, 'sqrt')), 'floor': a => Math.floor(num(a, 'floor')), 'ceil': a => Math.ceil(num(a, 'ceil')),
  'sin': a => Math.sin(num(a, 'sin')), 'cos': a => Math.cos(num(a, 'cos')),
  'atan2': (y, x) => Math.atan2(num(y, 'atan2'), num(x, 'atan2')),
  'exp': a => Math.exp(num(a, 'exp')), 'log': a => Math.log(num(a, 'log')), 'pow': (a, b) => Math.pow(num(a, 'pow'), num(b, 'pow')),
  'bit-and': (a, b) => int32(a, 'bit-and') & int32(b, 'bit-and'),
  'bit-or': (a, b) => int32(a, 'bit-or') | int32(b, 'bit-or'),
  'bit-xor': (a, b) => int32(a, 'bit-xor') ^ int32(b, 'bit-xor'),
  'shift-left': (a, b) => int32(a, 'shift-left') << (int32(b, 'shift-left') & 31),
  'shift-right': (a, b) => int32(a, 'shift-right') >> (int32(b, 'shift-right') & 31),
  'shift-right-logical': (a, b) => int32(a, 'shift-right-logical') >>> (int32(b, 'shift-right-logical') & 31),
  'compare': (a, b) => cmpVal(a, b),
  'hash': a => hashVal(a),
  'char-code': c => chr1(c, 'char-code').codePointAt(0),
  'char-chr': n => {
    n = num(n, 'char-chr');
    if (!Number.isInteger(n) || n < 0 || n > 0x10ffff) throw new Error(`char-chr: 字元碼超出範圍 ${toStr(n, true)}`);
    return String.fromCodePoint(n);
  },
  'string-get': (s, i) => {
    s = str(s, 'string-get'); i = num(i, 'string-get');
    if (!Number.isInteger(i) || i < 0 || i >= s.length) throw new Error(`string-get: 索引超出範圍 ${toStr(i, true)} (長度 ${s.length})`);
    return s[i];
  },
  'vector': (...a) => new Vec(a),
  'make-vector': (n, x) => {
    n = num(n, 'make-vector');
    if (!Number.isInteger(n) || n < 0) throw new Error(`make-vector: 長度錯誤 ${toStr(n, true)}`);
    return new Vec(Array(n).fill(x));
  },
  'vector-length': v => vec(v, 'vector-length').a.length,
  'vector-ref': (v, i) => { v = vec(v, 'vector-ref'); return v.a[vecIdx(v, i, 'vector-ref')]; },
  'vector-set!': (v, i, x) => { v = vec(v, 'vector-set!'); v.a[vecIdx(v, i, 'vector-set!')] = x; return VOID; },
  'set-car!': (p, x) => { pair(p, 'set-car!').car = x; return VOID; },
  'set-cdr!': (p, x) => { pair(p, 'set-cdr!').cdr = x; return VOID; },
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
  if (process.argv.length < 3) { console.error('用法: node vm.js program.lbc'); process.exit(1); }
  try { execute(fs.readFileSync(process.argv[2], 'utf8')); }
  catch (e) { console.error('執行錯誤: ' + e.message); process.exit(1); }
}
