# vm.js — 說明文件

`vm.js`（前身 `lispvm.js`）是以純 JS 實作的 **LBC v1 堆疊虛擬機**：讀入 `lispc.js` 產生的 `.lbc` 文字，執行並輸出結果。是全專案語意正確性的基準（`run_*.sh` 以它為準比對 wasm）。

## 1. 用法

```bash
node vm.js program.lbc
node lispc.js prog.lisp -o prog.lbc && node vm.js prog.lbc
```

API：`require('./vm.js')` → `{ load(text), run(funcs), execute(text), toStr(v, write) }`。

## 2. 資料模型（執行期型別）

| 值 | JS 表示 | 來源 |
|---|---|---|
| 數字（int/float 不分，double） | `number` | `CONST` 數字 |
| 布林 | `true`/`false` | `#t/#f` |
| 字串（含 `char`：1 字元字串） | `string` | `"…"` |
| 符號（intern） | `Sym`（`symtab` 唯一化） | `{"sym":…}` |
| 空串列 | `null` | `null` / `'()` |
| pair / list | `Pair{car,cdr}`（可變，供 `set-car!`） | `{"list":…}`、`cons/list` |
| 向量（`array`/bytes 底層） | `Vec{a: Array}`（可變） | `vector/make-vector` |
| 閉包 | `Closure{fn, env}`（詞彙作用域） | `CLOSURE` |
| 原語 | JS `function` | 內建表 |
| 未定義值 | `VOID` 單例 | `VOID`、`define` 回傳 |

相等：`eq?/eqv?` 為 `===`（數字/字串按值，物件按身份）；`equal?` 另對 pair 鏈與 `Vec` 做結構遞迴。
`compare` 為跨型別結構比較（數字 < 字串 < 符號 < `()` < 布林 < pair < 向量；函式/VOID 報錯）。
`hash` 為結構雜湊（djb2 風格，`& 0x3fffffff`），**與 `vm2wasm.js` 同演算法**，保證雙 VM 輸出一致。

## 3. 內建原語（`primitives`）

算術：`+ * - / quotient remainder modulo abs min max sqrt floor ceil sin cos atan2 exp log pow`
位運算（32 位）：`bit-and bit-or bit-xor shift-left shift-right shift-right-logical`
比較：`= < > <= >=`（數字兩兩比，或字串兩兩字典序；混合報錯）、`zero? even? odd? not eq? eqv? equal? compare hash`
pair/list：`cons car cdr cadr cddr caddr list length append reverse null? pair?`
型別謂詞：`number? string? symbol? procedure?`
字串/字元：`string-append string-length number->string char-code char-chr string-get`
向量：`vector make-vector vector-length vector-ref vector-set!`
可變 pair：`set-car! set-cdr!`
IO：`display write newline error`（`error` 拋 JS Error 中止程式）

索引越界訊息（`vector-ref/set!`、`string-get`）含索引與長度；所有原語參數錯誤訊息與 `vm2wasm.js` 逐字相同。

## 4. 原理：載入與執行迴圈

* **載入**（`load`）：逐行解析 `.func/標籤/指令`；`CONST` 經 `JSON.parse` → `fromDatum` 還原值；
  第二遍回填 `JMP/JF` 標籤為指令下標、`CLOSURE` 為函式物件；缺 `main` 報錯。
* **執行**（`run`）：單一 `for(;;)` 分派迴圈 + 顯式運算元堆疊 `stack`。
  環境鏈 `Env{vars, parent}`；全域環境預掛全部原語。
  `LOAD/DEF/SET` 沿鏈查找（`SET` 查無報錯）；`CLOSURE` 捕獲當時環境。
  `CALL`：閉包則建新 `Env` 綁參數（含 `. rest` 收集），舊框架壓入 `frames`（堆積，不吃 JS 堆疊，
  故深遞迴只受記憶體限制）；原語則直接 JS 呼叫。
  `TAILCALL`：閉包時**不壓框架**（尾遞迴 O(1) 空間）；原語呼叫後等同 `RET`。
  `JF` 只認 `false` 跳轉；`HALT` 回傳堆疊頂。

## 5. 功能邊界

* 無 GC 存活分析以外的記憶體管理問題（全部 JS 物件，靠 JS GC）。
* `display` 印人類可讀形，`write` 印 machine 形（字串加引號）；向量印 `[|a; b|]`。
* 錯誤一律拋出並以 `執行錯誤: …` 結束（exit 1）；無 `try/catch` 語意。
* 效能：直譯器分派，約比 `vm2wasm.js` 慢一個量級；適合除錯與語意基準。
