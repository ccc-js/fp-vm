# vm2wasm.js — 說明文件

`vm2wasm.js` 兼任 **LBC→WebAssembly 編譯器**與 **wasm 執行器**：把 `.lbc` 編成自給自足的 `.wasm`
（含 GC-less runtime），再以 Node `worker_threads`（256MB 堆疊）執行。輸出語意與 `vm.js` 逐字一致。

## 1. 用法

```bash
node vm2wasm.js prog.lbc [-o prog.wasm]   # 編譯（預設 prog.wasm）
node vm2wasm.js prog.lbc --run             # 編譯並執行
node vm2wasm.js prog.wasm                 # 直接執行 wasm
```

需支援 tail-call 的 Node（v20+）；產生失敗會報「無法通過驗證」。
API：`require('./vm2wasm.js')` → `{ compile(lbcText), run(bytes) }`。

## 2. 值編碼 EBNF（i32 視角）

```ebnf
value ::= smi | ptr
smi     ::= (x << 1) | 1                    (* 31-bit 小整數，最低位 1 *)
ptr     ::= 4-byte 對齊位址                 (* 最低位 0，指向物件 *)
object  ::= FLOAT  [1][pad][f64]
          | STR    [2][len][utf8...]        (* char = 長度 1 的 STR *)
          | SYM    [3][字串指標]            (* 編譯期 intern，eq? 比指標 *)
          | PAIR   [4][car][cdr]
          | VEC    [11][len][elem...]       (* array/bytes 底層 *)
          | CLOSURE[5][函式表索引][env]
          | PRIM   [6][內建編號]
單例      ::= NIL=8 | VOID=16 | TRUE=24 | FALSE=32
```

## 3. 記憶體配置

```ebnf
0..63        保留（單例在 8/16/24/32）
64..1087     ARGBUF（引數緩衝，最多 256 個）
1088..       GLOBALS（每全域變數一 slot，0 表未定義）
之後         靜態資料（字串/符號/常數/內建物件）→ heap（bump allocator，無 GC）
```

環境：`[parent][bindings]` 鏈，`env=0` 表全域（直查 `GLOBALS`）；
`LOAD/DEF/SET` 語意與 `vm.js` 相同。函式编為 `(env,i32,argc:i32)->i32`，
經 funcref table + `call_indirect` 分派，`TAILCALL` 用 `return_call_indirect`（真尾呼叫）。

## 4. 原理：編譯管線與執行分工

1. **前端**：解析 `.lbc`（與 `vm.js` 同格式）→ 靜態資料 intern（字串/符號/常數去重）→
   以「摺疊式」builder（`c/lg/ld/st/bin/if_/loop/block/call…`）產生各函式體：
   運算元堆疊在編譯期靜態對應 wasm locals（`s0,s1…`），跳躍用 `loop + br_table` 基本塊分派，
   引數經 `ARGBUF` 傳遞。
2. **Runtime**（wasm 內）：`alloc/env_new/env_push/slot/load/def/set/mkclos/call/tail/cons/rest/fast` 等 helper；
   內建函式**全部在宿主 JS**（`import env { prim(id,argc), err(kind,a,b) }`，引數在 `ARGBUF`）。
3. **中繼資料**：自訂段 `lbc.meta`（函式名、引數個數、`prims` 數量）供執行端解讀。
4. **執行**（`runBytes`）：讀 meta → 以 `DataView` 直讀線性記憶體實作
   `mkNum/mkStr/mkPair/mkVec/car/cdr/strOf/toStr/eqv/equal/cmpVal/hashVal` 與全部原語
   （與 `vm.js` 同演算法、同錯誤字串）；`prim` import 回呼即分派；`err` 回呼轉譯
   `UNBOUND/ARITY/NOTFN/OOM` 等；跑在 worker 內以取得大堆疊（非尾遞迴深度 = wasm 原生堆疊）。

## 5. 原語與一致性

`PRIM_NAMES`（共 70）與 `vm.js` 的 `primitives` 一一對應，**只能在尾端追加**
（ID 已 bake 進 `.wasm`）。新增原語三處同步：`PRIM_NAMES`、`impl`、宿主 helper。
`run_*.sh` 以 `cmp` 比對 `vm.js` 與本機輸出；錯誤訊息亦納入比對，故兩邊字串必須相同。

## 6. 功能邊界

* heap 無 GC：長期配置的常駐程式會 `E_OOM`（記憶體不足）；`MAX_PAGES` 上限約 1.9GB。
* 深遞迴上限 = worker 堆疊（256MB），超過拋 RangeError 轉譯為訊息。
* 浮點/字串/比較語意刻意與 `vm.js` 一致（含 32 位位運算、UTF-16 字串長度），而非與原生 OCaml 一致。
