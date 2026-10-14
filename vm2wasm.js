#!/usr/bin/env node
'use strict';
/*
 * vm2wasm.js  —  LBC v1 中間碼 (.lbc)  ->  WebAssembly (.wasm)
 *
 * 用法:
 *   node vm2wasm.js prog.lbc [-o prog.wasm]     編譯成 wasm (預設輸出 prog.wasm)
 *   node vm2wasm.js prog.lbc --run              編譯並執行
 *   node vm2wasm.js prog.wasm                   直接執行 wasm
 *
 * 需要支援 WebAssembly tail-call 的 Node.js (v20+)。不依賴任何 npm 套件，
 * .wasm 二進位檔是由本檔內建的小型組譯器直接產生的。
 *
 * ═════════════════════════════ 設計 ═════════════════════════════
 * 【值的表示】 所有 Lisp 值都是一個 i32:
 *    - 最低位 = 1 : 小整數 (31-bit)，值 = v >> 1
 *    - 最低位 = 0 : 指向線性記憶體物件的指標 (4 byte 對齊)，物件第一個 word 是 tag
 *        FLOAT   [1][pad][f64]            (非小整數的數字)
 *        STRING  [2][len][utf8 bytes...]
 *        SYMBOL  [3][字串物件指標]           (編譯期 intern，eq? 可用指標比較)
 *        PAIR    [4][car][cdr]
 *        CLOSURE [5][函式表索引][env]
 *        PRIM    [6][內建函式編號]
 *      固定位址的單例: NIL=8  VOID=16  TRUE=24  FALSE=32
 *
 * 【記憶體配置】
 *    0..63        保留 (NIL/VOID/TRUE/FALSE 在 8,16,24,32)
 *    64..1087     ARGBUF  呼叫引數緩衝區 (最多 256 個引數)
 *    1088..       GLOBALS 全域變數表: 每個變數名稱一個 slot (0 = 未定義)
 *    之後         靜態資料 (字串/符號/常數/內建函式物件) -> 再來是 heap (bump allocator，無 GC)
 *
 * 【環境】 區域環境 = [parent][bindings]，binding = [name_id][value][next]；
 *    env = 0 代表全域環境 (直接用 GLOBALS 表)。變數名稱在編譯期轉為 name_id，
 *    LOAD/DEF/SET 在執行期沿著環境鏈查找，語意與 vm.js 完全相同。
 *
 * 【函式】 每個 .func 編譯成一個 wasm 函式 (env:i32, argc:i32) -> i32，放在 funcref table。
 *    - 堆疊機的運算元堆疊在編譯期靜態對應到 wasm local (s0, s1, ...)；
 *    - 跳躍用「loop + br_table」的基本區塊分派；
 *    - CALL 以 call_indirect 實作，TAILCALL 以 return_call(_indirect) 實作 -> 真正的尾呼叫最佳化；
 *    - 引數經由 ARGBUF 傳遞，被呼叫者進入時立即綁定到新環境。
 *
 * 【Runtime】 alloc / 環境操作 / closure / call 分派 全部是 wasm 函式 (本檔產生)；
 *    只有內建函式 (+ car display ...) 與錯誤回報由宿主 JS 提供 (import "env")。
 */
const fs = require('fs');
const { Worker, isMainThread, workerData, parentPort } = require('worker_threads');

/* ───────────── 常數 ───────────── */
const TAG = { FLOAT: 1, STR: 2, SYM: 3, PAIR: 4, CLOSURE: 5, PRIM: 6, NIL: 7, VOID: 8, TRUE: 9, FALSE: 10, VEC: 11 };
const NIL = 8, VOID = 16, TRUE = 24, FALSE = 32;
const ARGBUF = 64, ARGMAX = 256, GBASE = ARGBUF + 4 * ARGMAX;
const MAX_PAGES = 30000;                       // ~1.9GB，避免位址超過 2^31

const PRIM_NAMES = ['+', '*', '-', '/', 'quotient', 'remainder', 'modulo', '=', '<', '>', '<=', '>=',
  'abs', 'min', 'max', 'zero?', 'even?', 'odd?', 'not', 'eq?', 'eqv?', 'equal?',
  'cons', 'car', 'cdr', 'cadr', 'cddr', 'caddr', 'list', 'length', 'append', 'reverse',
  'null?', 'pair?', 'number?', 'string?', 'symbol?', 'procedure?',
  'string-append', 'string-length', 'number->string', 'display', 'write', 'newline', 'error',
  'sqrt', 'floor', 'ceil', 'sin', 'cos', 'atan2', 'exp', 'log', 'pow',
  'bit-and', 'bit-or', 'bit-xor', 'shift-left', 'shift-right', 'shift-right-logical',
  'compare', 'hash', 'char-code', 'char-chr', 'string-get',
  'vector', 'make-vector', 'vector-length', 'vector-ref', 'vector-set!', 'set-car!', 'set-cdr!'];

/* ───────────── wasm 二進位組譯小工具 ───────────── */
const uleb = n => { n = BigInt(n); const o = []; do { let b = Number(n & 0x7fn); n >>= 7n; if (n) b |= 0x80; o.push(b); } while (n); return o; };
const sleb = n => {
  n = BigInt(n); const o = [];
  for (;;) {
    const b = Number(n & 0x7fn); n >>= 7n;
    if ((n === 0n && !(b & 0x40)) || (n === -1n && (b & 0x40))) { o.push(b); return o; }
    o.push(b | 0x80);
  }
};
const fl = a => a.flat(Infinity);
const vec = items => [...uleb(items.length), ...fl(items)];
const bytesOfStr = s => [...Buffer.from(s, 'utf8')];
const name = s => { const b = bytesOfStr(s); return [...uleb(b.length), ...b]; };
const section = (id, body) => [id, ...uleb(body.length), ...body];

// 以「折疊式」寫法產生指令 (運算元在前，操作碼在後)
const c = n => [0x41, ...sleb(n)];                        // i32.const
const lg = i => [0x20, ...uleb(i)];                       // local.get
const ls = (i, v) => [...fl(v), 0x21, ...uleb(i)];        // local.set
const gg = i => [0x23, ...uleb(i)];                       // global.get
const gs = (i, v) => [...fl(v), 0x24, ...uleb(i)];        // global.set
const ld = (a, off = 0) => [...fl(a), 0x28, 2, ...uleb(off)];            // i32.load
const st = (a, v, off = 0) => [...fl(a), ...fl(v), 0x36, 2, ...uleb(off)]; // i32.store
const bin = op => (a, b) => [...fl(a), ...fl(b), op];
const eq = bin(0x46), ne = bin(0x47), lts = bin(0x48), ltu = bin(0x49), gts = bin(0x4a), gtu = bin(0x4b), leS = bin(0x4c), geS = bin(0x4e);
const or = bin(0x72), add = bin(0x6a), sub = bin(0x6b), mul = bin(0x6c), divS = bin(0x6d), remS = bin(0x6f), and = bin(0x71), shl = bin(0x74), shrS = bin(0x75), shru = bin(0x76);
const eqz = a => [...fl(a), 0x45];
const call = (f, ...args) => [...fl(args), 0x10, ...uleb(f)];
const UNREACH = [0x00];
const ret = v => [...fl(v), 0x0f];
const if_ = (cond, th, el) => [...fl(cond), 0x04, 0x40, ...fl(th), ...(el ? [0x05, ...fl(el)] : []), 0x0b];
const block = (...b) => [0x02, 0x40, ...fl(b), 0x0b];
const loop = (...b) => [0x03, 0x40, ...fl(b), 0x0b];
const br = d => [0x0c, ...uleb(d)];
const brIf = (cond, d) => [...fl(cond), 0x0d, ...uleb(d)];
const memSize = [0x3f, 0x00];
const memGrow = x => [...fl(x), 0x40, 0x00];
const callIndirect = (args, idx) => [...fl(args), ...fl(idx), 0x11, 0, 0];          // type 0, table 0
const retCallIndirect = (args, idx) => [...fl(args), ...fl(idx), 0x13, 0, 0];

/* 型別: 0 = (i32,i32)->i32   1 = (i32,i32,i32)->()   2 = (i32)->i32 */
const T_FN = 0, T_V3 = 1, T_1 = 2;
/* 函式索引: 0,1 為 import；其後為 runtime helper；最後才是 LBC 函式 */
const F_PRIM = 0, F_ERR = 1, F_ALLOC = 2, F_ENVNEW = 3, F_ENVPUSH = 4, F_SLOT = 5, F_LOAD = 6,
  F_DEF = 7, F_SET = 8, F_MKCLOS = 9, F_CALL = 10, F_TAIL = 11, F_CONS = 12, F_REST = 13, F_FAST = 14, F_FIRST = 15;
/* err(kind,a,b) 的種類 */
const E_UNBOUND = 1, E_ARITY = 2, E_NOTFN = 3, E_OOM = 5, E_SET_UNBOUND = 6;

/* ───────────── 以 wasm 寫成的 runtime ───────────── */
function buildRuntime() {
  const H = [];
  const gAddr = id => add(c(GBASE), shl(id, c(2)));      // 全域變數 slot 位址

  H[F_ALLOC] = { name: 'alloc', type: T_1, locals: 4, body: [               // 0:size 1:p 2:nh 3:cur 4:need
    ls(0, and(add(lg(0), c(3)), c(-4))),
    ls(1, gg(0)),
    ls(2, add(lg(1), lg(0))),
    ls(3, shl(memSize, c(16))),
    if_(gtu(lg(2), lg(3)), [
      ls(4, add(shru(sub(lg(2), lg(3)), c(16)), c(1))),
      if_(eq(memGrow(add(lg(4), shru(memSize, c(1)))), c(-1)), [
        if_(eq(memGrow(lg(4)), c(-1)), [call(F_ERR, c(E_OOM), c(0), c(0)), UNREACH]),
      ]),
    ]),
    gs(0, lg(2)),
    lg(1),
  ] };

  H[F_ENVNEW] = { name: 'env_new', type: T_1, locals: 1, body: [           // 0:parent 1:p
    ls(1, call(F_ALLOC, c(8))),
    st(lg(1), lg(0)),
    st(lg(1), c(0), 4),
    lg(1),
  ] };

  H[F_ENVPUSH] = { name: 'env_push', type: T_V3, locals: 1, body: [        // 0:env 1:id 2:val 3:cell
    ls(3, call(F_ALLOC, c(12))),
    st(lg(3), lg(1)),
    st(lg(3), lg(2), 4),
    st(lg(3), ld(lg(0), 4), 8),
    st(lg(0), lg(3), 4),
  ] };

  H[F_SLOT] = { name: 'slot', type: T_FN, locals: 1, body: [               // 0:env 1:id 2:cell  -> 變數 slot 位址或 0
    block(
      loop(
        brIf(eqz(lg(0)), 1),
        ls(2, ld(lg(0), 4)),
        block(
          loop(
            brIf(eqz(lg(2)), 1),
            if_(eq(ld(lg(2)), lg(1)), [ret(add(lg(2), c(4)))]),
            ls(2, ld(lg(2), 8)),
            br(0),
          ),
        ),
        ls(0, ld(lg(0))),
        br(0),
      ),
    ),
    ls(2, gAddr(lg(1))),
    if_(eqz(ld(lg(2))), [ret(c(0))]),
    lg(2),
  ] };

  H[F_LOAD] = { name: 'load', type: T_FN, locals: 1, body: [                // 0:env 1:id 2:slot
    ls(2, call(F_SLOT, lg(0), lg(1))),
    if_(eqz(lg(2)), [call(F_ERR, c(E_UNBOUND), lg(1), c(0)), UNREACH]),
    ld(lg(2)),
  ] };

  H[F_DEF] = { name: 'def', type: T_V3, locals: 1, body: [                  // 0:env 1:id 2:val 3:cell
    if_(eqz(lg(0)), [st(gAddr(lg(1)), lg(2)), [0x0f]]),
    ls(3, ld(lg(0), 4)),
    block(
      loop(
        brIf(eqz(lg(3)), 1),
        if_(eq(ld(lg(3)), lg(1)), [st(lg(3), lg(2), 4), [0x0f]]),
        ls(3, ld(lg(3), 8)),
        br(0),
      ),
    ),
    call(F_ENVPUSH, lg(0), lg(1), lg(2)),
  ] };

  H[F_SET] = { name: 'set', type: T_V3, locals: 1, body: [                  // 0:env 1:id 2:val 3:slot
    ls(3, call(F_SLOT, lg(0), lg(1))),
    if_(eqz(lg(3)), [call(F_ERR, c(E_SET_UNBOUND), lg(1), c(0)), UNREACH]),
    st(lg(3), lg(2)),
  ] };

  const mkObj3 = (nm, tag) => ({ name: nm, type: T_FN, locals: 1, body: [  // 0:a 1:b 2:p
    ls(2, call(F_ALLOC, c(12))),
    st(lg(2), c(tag)),
    st(lg(2), lg(0), 4),
    st(lg(2), lg(1), 8),
    lg(2),
  ] });
  H[F_MKCLOS] = mkObj3('mkclosure', TAG.CLOSURE);                           // (func_table_idx, env)
  H[F_CONS] = mkObj3('cons', TAG.PAIR);

  const callBody = tail => [                                                 // 0:fn 1:argc 2:tag 3:fast結果
    if_(and(lg(0), c(1)), [call(F_ERR, c(E_NOTFN), lg(0), c(0)), UNREACH]),
    ls(2, ld(lg(0))),
    if_(eq(lg(2), c(TAG.CLOSURE)), [
      (tail ? retCallIndirect : callIndirect)([ld(lg(0), 8), lg(1)], ld(lg(0), 4)),
      ...(tail ? [] : [[0x0f]]),
    ]),
    if_(eq(lg(2), c(TAG.PRIM)), [
      ls(3, call(F_FAST, ld(lg(0), 4), lg(1))),
      if_(lg(3), [ret(lg(3))]),
      ret(call(F_PRIM, ld(lg(0), 4), lg(1))),
    ]),
    call(F_ERR, c(E_NOTFN), lg(0), c(0)),
    UNREACH,
  ];
  H[F_CALL] = { name: 'call', type: T_FN, locals: 2, body: callBody(false) };
  H[F_TAIL] = { name: 'tailcall', type: T_FN, locals: 2, body: callBody(true) };

  H[F_REST] = { name: 'rest_list', type: T_FN, locals: 2, body: [           // 0:from 1:argc 2:acc 3:i
    ls(2, c(NIL)),
    ls(3, lg(1)),
    block(
      loop(
        brIf(leS(lg(3), lg(0)), 1),
        ls(3, sub(lg(3), c(1))),
        ls(2, call(F_CONS, ld(add(c(ARGBUF), shl(lg(3), c(2)))), lg(2))),
        br(0),
      ),
    ),
    lg(2),
  ] };

  /* 小整數快速路徑: 兩個引數都是小整數時，直接在 wasm 內完成算術與比較，不進宿主 JS。
   * 回傳 0 表示不適用 (交給宿主處理，例如溢位、浮點、除以零、型別錯誤)。 */
  const pid = n => PRIM_NAMES.indexOf(n);
  const when = (id, ...body) => if_(eq(lg(0), c(pid(id))), body);
  const cmpOp = (id, f) => when(id, if_(f(lg(2), lg(3)), [ret(c(TRUE))]), ret(c(FALSE)));
  const setS = v => [ls(6, v), ls(7, c(1))];                                // s = 結果，ok = 1
  H[F_FAST] = { name: 'fastprim', type: T_FN, locals: 6, body: [          // 0:id 1:argc 2:a 3:b 4:x 5:y 6:s 7:ok
    if_(ne(lg(1), c(2)), [ret(c(0))]),
    ls(2, ld(c(ARGBUF))), ls(3, ld(c(ARGBUF + 4))),
    if_(eqz(and(and(lg(2), lg(3)), c(1))), [ret(c(0))]),                    // 兩者皆須為小整數
    cmpOp('=', eq), cmpOp('<', lts), cmpOp('>', gts), cmpOp('<=', leS), cmpOp('>=', geS),   // 已標記的整數大小順序不變
    ls(4, shrS(lg(2), c(1))), ls(5, shrS(lg(3), c(1))), ls(6, c(0)), ls(7, c(0)),
    when('+', setS(add(lg(4), lg(5)))),
    when('-', setS(sub(lg(4), lg(5)))),
    when('*', if_(ltu(add(lg(4), c(32767)), c(65535)), [if_(ltu(add(lg(5), c(32767)), c(65535)), [setS(mul(lg(4), lg(5)))])])),
    when('quotient', if_(lg(5), [setS(divS(lg(4), lg(5)))])),
    when('remainder', if_(lg(5), [setS(remS(lg(4), lg(5)))])),
    when('modulo', if_(lg(5), [setS(remS(add(remS(lg(4), lg(5)), lg(5)), lg(5)))])),
    // 結果必須落在 31-bit 小整數範圍內，否則交給宿主 (會轉成 float 物件)
    if_(and(lg(7), ltu(add(lg(6), c(0x40000000)), c(-2147483648))), [ret(or(shl(lg(6), c(1)), c(1)))]),
    c(0),
  ] };
  return H;
}

/* ───────────── 讀取 LBC 文字 ───────────── */
function loadLBC(text) {
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
    if (op === 'CONST') arg = JSON.parse(arg);
    else if (op === 'CALL' || op === 'TAILCALL') arg = Number(arg);
    cur.code.push([op, arg]);
  });
  for (const f of funcs.values()) {
    for (const ins of f.code) {
      if (ins[0] === 'JMP' || ins[0] === 'JF') {
        const t = f.labels.get(ins[1]);
        if (t === undefined) throw new Error(`函式 ${f.name}: 找不到標籤 ${ins[1]}`);
        ins[1] = t;
      } else if (ins[0] === 'CLOSURE' && !funcs.has(ins[1])) throw new Error(`找不到函式 ${ins[1]}`);
    }
  }
  if (!funcs.has('main')) throw new Error('缺少 main 函式');
  return funcs;
}

/* ───────────── 靜態資料區 ───────────── */
const align8 = n => (n + 7) & ~7;
class Static {
  constructor(top) {
    this.top = align8(top);
    this.buf = Buffer.alloc(Math.max(this.top + 4096, 1 << 14));
    this.strs = new Map(); this.syms = new Map(); this.flts = new Map();
  }
  ensure(n) { if (n > this.buf.length) { const nb = Buffer.alloc(Math.max(n, this.buf.length * 2)); this.buf.copy(nb); this.buf = nb; } }
  alloc(size) { const a = this.top; this.top += align8(size); this.ensure(this.top); return a; }
  w32(a, v) { this.ensure(a + 4); this.buf.writeInt32LE(v | 0, a); }
  str(s) {
    if (this.strs.has(s)) return this.strs.get(s);
    const b = Buffer.from(s, 'utf8'), a = this.alloc(8 + b.length);
    this.w32(a, TAG.STR); this.w32(a + 4, b.length); b.copy(this.buf, a + 8);
    this.strs.set(s, a); return a;
  }
  sym(n) {
    if (this.syms.has(n)) return this.syms.get(n);
    const sp = this.str(n), a = this.alloc(8);
    this.w32(a, TAG.SYM); this.w32(a + 4, sp);
    this.syms.set(n, a); return a;
  }
  float(x) {
    const k = Object.is(x, -0) ? '-0' : String(x);
    if (this.flts.has(k)) return this.flts.get(k);
    const a = this.alloc(16);
    this.w32(a, TAG.FLOAT); this.buf.writeDoubleLE(x, a + 8);
    this.flts.set(k, a); return a;
  }
  pair(car, cdr) { const a = this.alloc(12); this.w32(a, TAG.PAIR); this.w32(a + 4, car); this.w32(a + 8, cdr); return a; }
  value(d) {                                    // JSON 常數 -> 值 (i32)
    if (typeof d === 'number') return Number.isInteger(d) && d >= -1073741824 && d <= 1073741823 ? ((d << 1) | 1) : this.float(d);
    if (typeof d === 'boolean') return d ? TRUE : FALSE;
    if (typeof d === 'string') return this.str(d);
    if (d === null) return NIL;
    if ('sym' in d) return this.sym(d.sym);
    if ('list' in d) { let r = NIL; for (let i = d.list.length - 1; i >= 0; i--) r = this.pair(this.value(d.list[i]), r); return r; }
    throw new Error('錯誤的常數: ' + JSON.stringify(d));
  }
}

/* ───────────── 把一個 LBC 函式編譯成 wasm 函式 ───────────── */
const L_ENV = 0, L_ARGC = 1, L_CENV = 2, L_PC = 3, L_S = 4;     // local 配置: 運算元堆疊 slot 從 4 開始

function genFunc(fn, fidx, ctx) {
  const code = fn.code, n = code.length, isMain = fn.name === 'main';

  // 1. 靜態分析每個指令的堆疊深度 (所有路徑必須一致)
  const depth = new Array(n).fill(undefined), work = [], targets = new Set();
  let maxd = 0;
  const visit = (pc, d) => {
    if (pc >= n) throw new Error(`函式 ${fn.name}: 執行流程跑到函式結尾而沒有 RET / HALT`);
    if (depth[pc] === undefined) { depth[pc] = d; work.push(pc); }
    else if (depth[pc] !== d) throw new Error(`函式 ${fn.name}: 位置 ${pc} 的堆疊深度不一致 (${depth[pc]} vs ${d})`);
  };
  visit(0, 0);
  while (work.length) {
    const pc = work.pop(), d = depth[pc], [op, arg] = code[pc];
    const need = k => { if (d < k) throw new Error(`函式 ${fn.name}: 位置 ${pc} (${op}) 堆疊不足`); };
    switch (op) {
      case 'CONST': case 'VOID': case 'LOAD': case 'CLOSURE': maxd = Math.max(maxd, d + 1); visit(pc + 1, d + 1); break;
      case 'DEF': case 'SET': need(1); visit(pc + 1, d); break;
      case 'POP': need(1); visit(pc + 1, d - 1); break;
      case 'JMP': targets.add(arg); visit(arg, d); break;
      case 'JF': need(1); targets.add(arg); visit(arg, d - 1); visit(pc + 1, d - 1); break;
      case 'CALL': need(arg + 1); if (arg > ARGMAX) throw new Error(`CALL ${arg}: 引數過多 (上限 ${ARGMAX})`); visit(pc + 1, d - arg); break;
      case 'TAILCALL': need(arg + 1); if (arg > ARGMAX) throw new Error(`TAILCALL ${arg}: 引數過多 (上限 ${ARGMAX})`); break;
      case 'RET': need(1); break;
      case 'HALT': break;
      default: throw new Error(`函式 ${fn.name}: 未知的指令 ${op}`);
    }
  }

  // 2. 基本區塊: 0 與所有跳躍目標
  const leaders = [...new Set([0, ...targets])].sort((a, b) => a - b);
  const nb = leaders.length, blockOf = new Map(leaders.map((pc, i) => [pc, i]));
  const hasJumps = targets.size > 0;

  // 3. 逐區塊產生程式碼
  const blocks = leaders.map((start, bi) => {
    const end = bi + 1 < nb ? leaders[bi + 1] : n, out = [];
    const toLoop = nb - 1 - bi;                             // 從此區塊 br 回分派迴圈的深度
    for (let pc = start; pc < end; pc++) {
      if (depth[pc] === undefined) continue;                // 不可達的指令
      const d = depth[pc], [op, arg] = code[pc];
      const S = i => lg(L_S + i), setS = (i, v) => ls(L_S + i, v);
      switch (op) {
        case 'CONST': out.push(setS(d, c(ctx.st.value(arg)))); break;
        case 'VOID': out.push(setS(d, c(VOID))); break;
        case 'LOAD': out.push(setS(d, call(F_LOAD, lg(L_CENV), c(ctx.nameId(arg))))); break;
        case 'DEF': out.push(call(F_DEF, lg(L_CENV), c(ctx.nameId(arg)), S(d - 1)), setS(d - 1, c(VOID))); break;
        case 'SET': out.push(call(F_SET, lg(L_CENV), c(ctx.nameId(arg)), S(d - 1)), setS(d - 1, c(VOID))); break;
        case 'POP': break;
        case 'CLOSURE': out.push(setS(d, call(F_MKCLOS, c(ctx.funcIndex(arg)), lg(L_CENV)))); break;
        case 'CALL': case 'TAILCALL': {
          const base = d - arg - 1;
          for (let i = 0; i < arg; i++) out.push(st(c(ARGBUF + 4 * i), S(base + 1 + i)));
          if (op === 'CALL') out.push(setS(base, call(F_CALL, S(base), c(arg))));
          else out.push(S(base), c(arg), [0x12, ...uleb(F_TAIL)]);                // return_call
          break;
        }
        case 'RET': out.push(ret(S(d - 1))); break;
        case 'HALT': out.push(ret(d > 0 ? S(d - 1) : c(VOID))); break;
        case 'JMP': out.push(ls(L_PC, c(blockOf.get(arg))), br(toLoop)); break;
        case 'JF': out.push(ls(L_PC, c(blockOf.get(arg))), brIf(eq(S(d - 1), c(FALSE)), toLoop)); break;
      }
    }
    return out;
  });

  // 4. 函式前言: 建立環境並綁定參數
  const body = [];
  body.push(ls(L_CENV, isMain ? lg(L_ENV) : call(F_ENVNEW, lg(L_ENV))));
  if (!isMain) {
    const k = fn.params.length;
    body.push(if_(fn.rest === null ? ne(lg(L_ARGC), c(k)) : lts(lg(L_ARGC), c(k)),
      [call(F_ERR, c(E_ARITY), c(fidx), lg(L_ARGC)), UNREACH]));
    fn.params.forEach((p, i) => body.push(call(F_ENVPUSH, lg(L_CENV), c(ctx.nameId(p)), ld(c(ARGBUF + 4 * i)))));
    if (fn.rest !== null) body.push(call(F_ENVPUSH, lg(L_CENV), c(ctx.nameId(fn.rest)), call(F_REST, c(k), lg(L_ARGC))));
  }

  // 5. 區塊分派: loop { block{ ... block{ br_table } bb0 } ... bb(n-1) }
  if (!hasJumps) body.push(blocks[0]);
  else {
    let cur = [...lg(L_PC), 0x0e, ...uleb(nb), ...fl(leaders.map((_, i) => uleb(i))), ...uleb(nb - 1)];
    for (let i = 0; i < nb; i++) cur = [...block(cur), ...fl(blocks[i])];
    body.push(loop(cur));
  }
  body.push(UNREACH);
  return { name: fn.name, type: T_FN, locals: 2 + maxd, body };
}

/* ───────────── 組裝整個 wasm 模組 ───────────── */
function compile(lbcText) {
  const funcs = loadLBC(lbcText), flist = [...funcs.values()];

  // 名稱表: 先放內建函式，再放程式中出現的所有變數名稱
  const names = [...PRIM_NAMES], nameIds = new Map(names.map((n, i) => [n, i]));
  const nameId = n => { if (!nameIds.has(n)) { nameIds.set(n, names.length); names.push(n); } return nameIds.get(n); };
  for (const f of flist) {
    f.params.forEach(nameId); if (f.rest) nameId(f.rest);
    for (const [op, arg] of f.code) if (op === 'LOAD' || op === 'DEF' || op === 'SET') nameId(arg);
  }

  // 靜態資料: 單例、內建函式物件、(之後) 常數
  const stt = new Static(GBASE + 4 * names.length);
  stt.w32(NIL, TAG.NIL); stt.w32(VOID, TAG.VOID); stt.w32(TRUE, TAG.TRUE); stt.w32(FALSE, TAG.FALSE);
  PRIM_NAMES.forEach((pn, i) => {
    const a = stt.alloc(8); stt.w32(a, TAG.PRIM); stt.w32(a + 4, i);
    stt.w32(GBASE + 4 * nameIds.get(pn), a);
  });

  const ctx = { st: stt, nameId, funcIndex: nm => flist.findIndex(f => f.name === nm) };
  const lbcFuncs = flist.map((f, i) => genFunc(f, i, ctx));
  const helpers = buildRuntime();
  const all = [...helpers.slice(F_ALLOC), ...lbcFuncs];             // 定義的函式 (索引從 F_ALLOC 起)
  const mainIdx = F_FIRST + flist.findIndex(f => f.name === 'main');

  // type / import / function / table / memory / global / export / element / code / data
  const types = section(1, vec([
    [0x60, ...vec([[0x7f], [0x7f]]), ...vec([[0x7f]])],
    [0x60, ...vec([[0x7f], [0x7f], [0x7f]]), ...vec([])],
    [0x60, ...vec([[0x7f]]), ...vec([[0x7f]])],
  ]));
  const imports = section(2, vec([
    [...name('env'), ...name('prim'), 0x00, T_FN],
    [...name('env'), ...name('err'), 0x00, T_V3],
  ]));
  const funcSec = section(3, vec(all.map(f => [f.type])));
  const nTable = lbcFuncs.length;
  const table = section(4, vec([[0x70, 0x01, ...uleb(nTable), ...uleb(nTable)]]));
  const minPages = Math.ceil((stt.top + (1 << 20)) / 65536);
  const memory = section(5, vec([[0x01, ...uleb(minPages), ...uleb(Math.max(MAX_PAGES, minPages))]]));
  const globals = section(6, vec([[0x7f, 0x01, ...c(stt.top), 0x0b]]));
  const exportsSec = section(7, vec([
    [...name('memory'), 0x02, 0x00],
    [...name('main'), 0x00, ...uleb(mainIdx)],
    [...name('alloc'), 0x00, ...uleb(F_ALLOC)],
  ]));
  const elem = section(9, vec([[0x00, ...c(0), 0x0b, ...vec(lbcFuncs.map((_, i) => uleb(F_FIRST + i)))]]));
  const codeSec = section(10, vec(all.map(f => {
    const b = [...(f.locals ? [1, ...uleb(f.locals), 0x7f] : [0]), ...fl(f.body), 0x0b];
    return [...uleb(b.length), ...b];
  })));
  const data = section(11, vec([[0x00, ...c(0), 0x0b, ...uleb(stt.top), ...stt.buf.subarray(0, stt.top)]]));

  // 自訂區段: 函式名稱 (除錯用的標準 name section) 與 runtime 需要的中繼資料
  const fnNames = [[F_PRIM, 'prim'], [F_ERR, 'err'], ...all.map((f, i) => [F_ALLOC + i, f.name])];
  const nameSec = section(0, [...name('name'), 1, ...(() => { const b = vec(fnNames.map(([i, s]) => [...uleb(i), ...name(s)])); return [...uleb(b.length), ...b]; })()]);
  const meta = JSON.stringify({
    version: 1, names, prims: PRIM_NAMES.length,
    funcs: flist.map(f => ({ name: f.name, params: f.params.length, rest: f.rest !== null })),
  });
  const metaSec = section(0, [...name('lbc.meta'), ...Buffer.from(meta, 'utf8')]);

  const bytes = Uint8Array.from([0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00,
    ...types, ...imports, ...funcSec, ...table, ...memory, ...globals, ...exportsSec, ...elem,
    ...codeSec, ...data, ...nameSec, ...metaSec]);
  try { new WebAssembly.Module(bytes); }
  catch (e) { throw new Error('產生的 wasm 無法通過驗證 (需要支援 tail-call 的 Node.js v20+): ' + e.message); }
  return bytes;
}

/* ═══════════════════════ 執行端 (宿主 JS) ═══════════════════════
 * 只負責: 內建函式、錯誤訊息、輸出。所有資料都直接讀寫 wasm 線性記憶體。 */
function runBytes(bytes) {
  const mod = new WebAssembly.Module(bytes);
  const sec = WebAssembly.Module.customSections(mod, 'lbc.meta');
  if (!sec.length) throw new Error('不是由 vm2wasm.js 產生的 wasm (缺少 lbc.meta)');
  const meta = JSON.parse(Buffer.from(sec[0]).toString('utf8'));

  let ex = null, lastBuf = null, dv = null, u8 = null;
  const V = () => { if (ex.memory.buffer !== lastBuf) { lastBuf = ex.memory.buffer; dv = new DataView(lastBuf); u8 = new Uint8Array(lastBuf); } return dv; };
  const rd = a => V().getInt32(a, true);
  const wr = (a, v) => V().setInt32(a, v, true);
  const enc = new TextEncoder(), dec = new TextDecoder();

  /* 輸出緩衝 */
  let outBuf = [], outLen = 0;
  const flush = () => { if (outBuf.length) { process.stdout.write(outBuf.join('')); outBuf = []; outLen = 0; } };
  const out = s => { outBuf.push(s); outLen += s.length; if (outLen > 65536) flush(); };

  /* 值存取 */
  const tagOf = v => (v & 1) ? 0 : rd(v);
  const isNumV = v => (v & 1) || rd(v) === TAG.FLOAT;
  const numVal = v => (v & 1) ? v >> 1 : V().getFloat64(v + 8, true);
  const mkNum = x => {
    if (Number.isInteger(x) && x >= -1073741824 && x <= 1073741823) return (x << 1) | 1;
    const p = ex.alloc(16); wr(p, TAG.FLOAT); V().setFloat64(p + 8, x, true); return p;
  };
  const strOf = v => { const len = rd(v + 4); V(); return dec.decode(u8.subarray(v + 8, v + 8 + len)); };
  const mkStr = s => { const b = enc.encode(s), p = ex.alloc(8 + b.length); wr(p, TAG.STR); wr(p + 4, b.length); V(); u8.set(b, p + 8); return p; };
  const mkPair = (a, d) => { const p = ex.alloc(12); wr(p, TAG.PAIR); wr(p + 4, a); wr(p + 8, d); return p; };
  const isPair = v => !(v & 1) && rd(v) === TAG.PAIR;
  const car = v => rd(v + 4), cdr = v => rd(v + 8);
  const mkVec = a => { const p = ex.alloc(8 + 4 * a.length); wr(p, TAG.VEC); wr(p + 4, a.length); a.forEach((v, i) => wr(p + 8 + 4 * i, v)); return p; };
  const isVec = v => !(v & 1) && rd(v) === TAG.VEC;
  const vecLen = v => rd(v + 4);
  const vecRef = (v, i) => rd(v + 8 + 4 * i);
  const vecSet = (v, i, x) => wr(v + 8 + 4 * i, x);
  const vecToArray = v => { const a = []; for (let i = 0; i < vecLen(v); i++) a.push(vecRef(v, i)); return a; };
  const bool = b => b ? TRUE : FALSE;
  const arrOf = l => { const a = []; for (; isPair(l); l = cdr(l)) a.push(car(l)); return a; };
  const listOf = a => { let r = NIL; for (let i = a.length - 1; i >= 0; i--) r = mkPair(a[i], r); return r; };

  function toStr(v, write) {
    if (v & 1) return String(v >> 1);
    switch (rd(v)) {
      case TAG.FLOAT: return String(numVal(v));
      case TAG.STR: { const s = strOf(v); return write ? JSON.stringify(s) : s; }
      case TAG.SYM: return strOf(rd(v + 4));
      case TAG.CLOSURE: return `#<procedure ${meta.funcs[rd(v + 4)].name}>`;
      case TAG.PRIM: return '#<primitive>';
      case TAG.NIL: return '()';
      case TAG.VOID: return '';
      case TAG.TRUE: return '#t';
      case TAG.FALSE: return '#f';
      case TAG.PAIR: {
        const parts = []; let p = v;
        for (; isPair(p); p = cdr(p)) parts.push(toStr(car(p), write));
        return '(' + parts.join(' ') + (p === NIL ? '' : ' . ' + toStr(p, write)) + ')';
      }
      case TAG.VEC: return '[|' + vecToArray(v).map(x => toStr(x, write)).join('; ') + '|]';
    }
    return '#<unknown>';
  }
  const cmpVal = (a, b) => {
    const rank = v => isNumV(v) ? 0 : tagOf(v) === TAG.STR ? 1 : tagOf(v) === TAG.SYM ? 2
      : v === NIL ? 3 : (v === TRUE || v === FALSE) ? 4 : isPair(v) ? 5 : isVec(v) ? 6 : -1;
    const ra = rank(a), rb = rank(b);
    if (ra < 0 || rb < 0) throw new Error('compare: 不支援函式或 void 的比較');
    if (ra !== rb) return ra < rb ? -1 : 1;
    switch (ra) {
      case 0: { const x = numVal(a), y = numVal(b); return x < y ? -1 : x > y ? 1 : 0; }
      case 1: { const x = strOf(a), y = strOf(b); return x < y ? -1 : x > y ? 1 : 0; }
      case 2: { const x = strOf(rd(a + 4)), y = strOf(rd(b + 4)); return x < y ? -1 : x > y ? 1 : 0; }
      case 3: return 0;
      case 4: return a === b ? 0 : a === FALSE ? -1 : 1;
      case 5: { const c = cmpVal(car(a), car(b)); return c !== 0 ? c : cmpVal(cdr(a), cdr(b)); }
      case 6: {
        if (vecLen(a) !== vecLen(b)) return vecLen(a) < vecLen(b) ? -1 : 1;
        for (let i = 0; i < vecLen(a); i++) { const c = cmpVal(vecRef(a, i), vecRef(b, i)); if (c !== 0) return c; }
        return 0;
      }
    }
    return 0;
  };
  const hashVal = v => {
    const mix = h => ((h | 0) * 31 | 0) & 0x3fffffff;
    const strH = s => { let h = 0; for (let i = 0; i < s.length; i++) h = mix(h + s.charCodeAt(i)); return h; };
    const go = (v, d) => {
      if (isNumV(v)) { const x = numVal(v); return mix(x | 0) ^ mix(Math.floor(Math.abs(x % 1) * 1e9)); }
      const t = tagOf(v);
      if (t === TAG.STR) return strH('s' + strOf(v));
      if (t === TAG.SYM) return strH('k' + strOf(rd(v + 4)));
      if (v === NIL) return 0x1a2b3c;
      if (v === TRUE) return 0x111; if (v === FALSE) return 0x222;
      if (d <= 0) return 0x777;
      if (isPair(v)) return mix(go(car(v), d - 1)) ^ (mix(go(cdr(v), d - 1)) + 0x9e37);
      if (isVec(v)) { let h = vecLen(v); for (const x of vecToArray(v)) h = mix(h) ^ go(x, d - 1); return h; }
      throw new Error('hash: 不支援函式或 void 的雜湊');
    };
    return go(v, 8);
  };
  const eqv = (a, b) => {
    if (a === b) return true;
    if (isNumV(a) && isNumV(b)) return numVal(a) === numVal(b);
    return tagOf(a) === TAG.STR && tagOf(b) === TAG.STR && strOf(a) === strOf(b);
  };
  const equal = (a, b) => {
    if (isPair(a) && isPair(b)) return equal(car(a), car(b)) && equal(cdr(a), cdr(b));
    if (isVec(a) && isVec(b)) {
      if (vecLen(a) !== vecLen(b)) return false;
      for (let i = 0; i < vecLen(a); i++) if (!equal(vecRef(a, i), vecRef(b, i))) return false;
      return true;
    }
    return eqv(a, b);
  };

  /* 內建函式: 引數在 ARGBUF，A(i) 取第 i 個 */
  const A = i => rd(ARGBUF + 4 * i);
  const num = (v, who) => { if (!isNumV(v)) throw new Error(`${who}: 需要數字，得到 ${toStr(v, true)}`); return numVal(v); };
  const req = (who, n, k) => { if (n < k) throw new Error(`${who}: 參數個數錯誤 (需要 ${k}，得到 ${n})`); };
  const nums = (who, n) => { const r = []; for (let i = 0; i < n; i++) r.push(num(A(i), who)); return r; };
  const cmp = (who, f) => n => {
    const a = []; for (let i = 0; i < n; i++) a.push(A(i));
    for (let i = 0; i < a.length - 1; i++) {
      const x = a[i], y = a[i + 1];
      let ok = null;
      if (isNumV(x) && isNumV(y)) ok = f(numVal(x), numVal(y));
      else if (tagOf(x) === TAG.STR && tagOf(y) === TAG.STR) {
        const xs = strOf(x), ys = strOf(y);
        ok = f(xs < ys ? -1 : xs > ys ? 1 : 0, 0);
      }
      if (ok === null) throw new Error(`${who}: 需要兩個數字或兩個字串，得到 ${toStr(x, true)} 與 ${toStr(y, true)}`);
      if (!ok) return FALSE;
    }
    return TRUE;
  };
  const pairOrErr = (who, v) => { if (!isPair(v)) throw new Error(`${who}: 不是 pair: ${toStr(v, true)}`); return v; };

  const impl = {
    '+': n => mkNum(nums('+', n).reduce((x, y) => x + y, 0)),
    '*': n => mkNum(nums('*', n).reduce((x, y) => x * y, 1)),
    '-': n => { req('-', n, 1); const a = nums('-', n); return mkNum(n === 1 ? -a[0] : a.slice(1).reduce((x, y) => x - y, a[0])); },
    '/': n => {
      req('/', n, 1); const a = nums('/', n);
      return mkNum(n === 1 ? 1 / a[0] : a.slice(1).reduce((x, y) => { if (y === 0) throw new Error('/: 除以零'); return x / y; }, a[0]));
    },
    'quotient': n => { req('quotient', n, 2); return mkNum(Math.trunc(num(A(0), 'quotient') / num(A(1), 'quotient'))); },
    'remainder': n => { req('remainder', n, 2); return mkNum(num(A(0), 'remainder') % num(A(1), 'remainder')); },
    'modulo': n => { req('modulo', n, 2); const a = num(A(0), 'modulo'), b = num(A(1), 'modulo'); return mkNum(((a % b) + b) % b); },
    '=': cmp('=', (a, b) => a === b), '<': cmp('<', (a, b) => a < b), '>': cmp('>', (a, b) => a > b),
    '<=': cmp('<=', (a, b) => a <= b), '>=': cmp('>=', (a, b) => a >= b),
    'abs': n => { req('abs', n, 1); return mkNum(Math.abs(num(A(0), 'abs'))); },
    'min': n => mkNum(Math.min(...nums('min', n))), 'max': n => mkNum(Math.max(...nums('max', n))),
    'zero?': n => { req('zero?', n, 1); return bool(num(A(0), 'zero?') === 0); },
    'even?': n => { req('even?', n, 1); return bool(num(A(0), 'even?') % 2 === 0); },
    'odd?': n => { req('odd?', n, 1); return bool(Math.abs(num(A(0), 'odd?') % 2) === 1); },
    'not': n => { req('not', n, 1); return bool(A(0) === FALSE); },
    'eq?': n => { req('eq?', n, 2); return bool(eqv(A(0), A(1))); },
    'eqv?': n => { req('eqv?', n, 2); return bool(eqv(A(0), A(1))); },
    'equal?': n => { req('equal?', n, 2); return bool(equal(A(0), A(1))); },
    'cons': n => { req('cons', n, 2); return mkPair(A(0), A(1)); },
    'car': n => { req('car', n, 1); return car(pairOrErr('car', A(0))); },
    'cdr': n => { req('cdr', n, 1); return cdr(pairOrErr('cdr', A(0))); },
    'cadr': n => { req('cadr', n, 1); return car(pairOrErr('cadr', cdr(pairOrErr('cadr', A(0))))); },
    'cddr': n => { req('cddr', n, 1); return cdr(pairOrErr('cddr', cdr(pairOrErr('cddr', A(0))))); },
    'caddr': n => { req('caddr', n, 1); return car(pairOrErr('caddr', cdr(pairOrErr('caddr', cdr(pairOrErr('caddr', A(0))))))); },
    'list': n => { let r = NIL; for (let i = n - 1; i >= 0; i--) r = mkPair(A(i), r); return r; },
    'length': n => { req('length', n, 1); return mkNum(arrOf(A(0)).length); },
    'append': n => { const all = []; for (let i = 0; i < n; i++) all.push(...arrOf(A(i))); return listOf(all); },
    'reverse': n => { req('reverse', n, 1); return listOf(arrOf(A(0)).reverse()); },
    'null?': n => { req('null?', n, 1); return bool(A(0) === NIL); },
    'pair?': n => { req('pair?', n, 1); return bool(isPair(A(0))); },
    'number?': n => { req('number?', n, 1); return bool(isNumV(A(0))); },
    'string?': n => { req('string?', n, 1); return bool(tagOf(A(0)) === TAG.STR); },
    'symbol?': n => { req('symbol?', n, 1); return bool(tagOf(A(0)) === TAG.SYM); },
    'procedure?': n => { req('procedure?', n, 1); const t = tagOf(A(0)); return bool(t === TAG.CLOSURE || t === TAG.PRIM); },
    'string-append': n => { let s = ''; for (let i = 0; i < n; i++) s += toStr(A(i), false); return mkStr(s); },
    'string-length': n => { req('string-length', n, 1); return mkNum(strOf(A(0)).length); },
    'number->string': n => { req('number->string', n, 1); return mkStr(String(num(A(0), 'number->string'))); },
    'display': n => { req('display', n, 1); out(toStr(A(0), false)); return VOID; },
    'write': n => { req('write', n, 1); out(toStr(A(0), true)); return VOID; },
    'newline': () => { out('\n'); return VOID; },
    'error': n => { const a = []; for (let i = 0; i < n; i++) a.push(toStr(A(i), false)); throw new Error(a.join(' ')); },
    'sqrt': n => { req('sqrt', n, 1); return mkNum(Math.sqrt(num(A(0), 'sqrt'))); },
    'floor': n => { req('floor', n, 1); return mkNum(Math.floor(num(A(0), 'floor'))); },
    'ceil': n => { req('ceil', n, 1); return mkNum(Math.ceil(num(A(0), 'ceil'))); },
    'sin': n => { req('sin', n, 1); return mkNum(Math.sin(num(A(0), 'sin'))); },
    'cos': n => { req('cos', n, 1); return mkNum(Math.cos(num(A(0), 'cos'))); },
    'atan2': n => { req('atan2', n, 2); return mkNum(Math.atan2(num(A(0), 'atan2'), num(A(1), 'atan2'))); },
    'exp': n => { req('exp', n, 1); return mkNum(Math.exp(num(A(0), 'exp'))); },
    'log': n => { req('log', n, 1); return mkNum(Math.log(num(A(0), 'log'))); },
    'pow': n => { req('pow', n, 2); return mkNum(Math.pow(num(A(0), 'pow'), num(A(1), 'pow'))); },
    'bit-and': n => { req('bit-and', n, 2); return mkNum((num(A(0), 'bit-and') | 0) & (num(A(1), 'bit-and') | 0)); },
    'bit-or': n => { req('bit-or', n, 2); return mkNum((num(A(0), 'bit-or') | 0) | (num(A(1), 'bit-or') | 0)); },
    'bit-xor': n => { req('bit-xor', n, 2); return mkNum((num(A(0), 'bit-xor') | 0) ^ (num(A(1), 'bit-xor') | 0)); },
    'shift-left': n => { req('shift-left', n, 2); return mkNum((num(A(0), 'shift-left') | 0) << ((num(A(1), 'shift-left') | 0) & 31)); },
    'shift-right': n => { req('shift-right', n, 2); return mkNum((num(A(0), 'shift-right') | 0) >> ((num(A(1), 'shift-right') | 0) & 31)); },
    'shift-right-logical': n => { req('shift-right-logical', n, 2); return mkNum((num(A(0), 'shift-right-logical') | 0) >>> ((num(A(1), 'shift-right-logical') | 0) & 31)); },
    'compare': n => { req('compare', n, 2); return mkNum(cmpVal(A(0), A(1))); },
    'hash': n => { req('hash', n, 1); return mkNum(hashVal(A(0))); },
    'char-code': n => {
      req('char-code', n, 1);
      if (tagOf(A(0)) !== TAG.STR || strOf(A(0)).length !== 1) throw new Error(`char-code: 需要字元，得到 ${toStr(A(0), true)}`);
      return mkNum(strOf(A(0)).codePointAt(0));
    },
    'char-chr': n => {
      req('char-chr', n, 1); const c = num(A(0), 'char-chr');
      if (!Number.isInteger(c) || c < 0 || c > 0x10ffff) throw new Error(`char-chr: 字元碼超出範圍 ${c}`);
      return mkStr(String.fromCodePoint(c));
    },
    'string-get': n => {
      req('string-get', n, 2);
      if (tagOf(A(0)) !== TAG.STR) throw new Error(`string-get: 需要字串，得到 ${toStr(A(0), true)}`);
      const s = strOf(A(0)), i = num(A(1), 'string-get');
      if (!Number.isInteger(i) || i < 0 || i >= s.length) throw new Error(`string-get: 索引超出範圍 ${i} (長度 ${s.length})`);
      return mkStr(s[i]);
    },
    'vector': n => { const a = []; for (let i = 0; i < n; i++) a.push(A(i)); return mkVec(a); },
    'make-vector': n => {
      req('make-vector', n, 2); const len = num(A(0), 'make-vector');
      if (!Number.isInteger(len) || len < 0) throw new Error(`make-vector: 長度錯誤 ${len}`);
      return mkVec(Array(len).fill(A(1)));
    },
    'vector-length': n => { req('vector-length', n, 1); if (!isVec(A(0))) throw new Error(`vector-length: 不是陣列，得到 ${toStr(A(0), true)}`); return mkNum(vecLen(A(0))); },
    'vector-ref': n => {
      req('vector-ref', n, 2); const v = A(0), i = num(A(1), 'vector-ref');
      if (!isVec(v)) throw new Error(`vector-ref: 不是陣列，得到 ${toStr(v, true)}`);
      if (!Number.isInteger(i) || i < 0 || i >= vecLen(v)) throw new Error(`vector-ref: 索引超出範圍 ${i} (長度 ${vecLen(v)})`);
      return vecRef(v, i);
    },
    'vector-set!': n => {
      req('vector-set!', n, 3); const v = A(0), i = num(A(1), 'vector-set!');
      if (!isVec(v)) throw new Error(`vector-set!: 不是陣列，得到 ${toStr(v, true)}`);
      if (!Number.isInteger(i) || i < 0 || i >= vecLen(v)) throw new Error(`vector-set!: 索引超出範圍 ${i} (長度 ${vecLen(v)})`);
      vecSet(v, i, A(2)); return VOID;
    },
    'set-car!': n => { req('set-car!', n, 2); wr(pairOrErr('set-car!', A(0)) + 4, A(1)); return VOID; },
    'set-cdr!': n => { req('set-cdr!', n, 2); wr(pairOrErr('set-cdr!', A(0)) + 8, A(1)); return VOID; },
  };
  const prims = PRIM_NAMES.map(pn => impl[pn]);

  const hostErr = (kind, a, b) => {
    switch (kind) {
      case E_UNBOUND: throw new Error('未定義的變數: ' + meta.names[a]);
      case E_SET_UNBOUND: throw new Error('set!: 未定義的變數: ' + meta.names[a]);
      case E_ARITY: { const f = meta.funcs[a]; throw new Error(`${f.name}: 參數個數錯誤 (需要 ${f.params}${f.rest ? '+' : ''}，得到 ${b})`); }
      case E_NOTFN: throw new Error('不是可呼叫的物件: ' + toStr(a, true));
      case E_OOM: throw new Error('記憶體不足 (heap 沒有 GC)');
    }
    throw new Error('runtime error ' + kind);
  };

  const inst = new WebAssembly.Instance(mod, { env: { prim: (id, argc) => prims[id](argc), err: hostErr } });
  ex = inst.exports;
  try { return ex.main(0, 0); }
  catch (e) {
    if (e instanceof RangeError) throw new Error('遞迴太深 (call stack overflow)');
    throw e;
  } finally { flush(); }
}

/* 在 worker 內執行，以便給予很大的呼叫堆疊 (非尾遞迴的深度 = wasm 原生堆疊深度) */
function runInWorker(bytes) {
  const w = new Worker(__filename, { workerData: { vm2wasmRun: true, bytes }, resourceLimits: { stackSizeMb: 256 } });
  w.on('message', m => { if (m && m.error) { console.error('執行錯誤: ' + m.error); process.exitCode = 1; } });
  w.on('error', e => { console.error('執行錯誤: ' + (e && e.message)); process.exitCode = 1; });
}

module.exports = { compile, run: runBytes };

/* ───────────── 進入點 ───────────── */
if (!isMainThread && workerData && workerData.vm2wasmRun) {
  try { runBytes(workerData.bytes); parentPort.postMessage({ ok: true }); }
  catch (e) { parentPort.postMessage({ error: e.message }); }
} else if (require.main === module) {
  const args = process.argv.slice(2);
  let input = null, output = null, run = false;
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '-o') output = args[++i];
    else if (args[i] === '--run') run = true;
    else input = args[i];
  }
  if (!input) {
    console.error('用法: node vm2wasm.js prog.lbc [-o prog.wasm] [--run]\n      node vm2wasm.js prog.wasm');
    process.exit(1);
  }
  try {
    if (input.endsWith('.wasm')) runInWorker(fs.readFileSync(input));
    else {
      const bytes = compile(fs.readFileSync(input, 'utf8'));
      output = output || input.replace(/\.[^.]*$/, '') + '.wasm';
      fs.writeFileSync(output, bytes);
      console.error(`已編譯 ${input} -> ${output} (${bytes.length} bytes)`);
      if (run) runInWorker(bytes);
    }
  } catch (e) { console.error('錯誤: ' + e.message); process.exit(1); }
}
