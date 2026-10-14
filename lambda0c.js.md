# lambda0c.js — 說明文件

`lambda0c.js` 是 **Church 式 Lambda Calculus → LBC v1** 編譯器（經 Scheme 核心 + `lispc.js`，
用 `vm.js` 執行）。與 `lambdac.js` 的差別：刻意只留 Church 1930 年代的三件套——
命名、函數抽象、函數應用——外加務實的 primitive `int` 與 `print`；
`TRUE/FALSE/IF/PAIR/NIL` 等一律由使用者以函數建構（見 `lambda0/` 範例），
**VM（`vm.js`/`vm2wasm.js`）完全不需修改**。

## 1. 用法

```bash
node lambda0c.js input.l0 [-o output.lbc]   # -o - 表 stdout；預設 input.lbc
node lambda0c.js input.l0 --scheme          # 只印 Scheme 核心（除錯）
node vm.js output.lbc
```

```text
-- Church 布林
TRUE = \x.\y.x;
FALSE = \x.\y.y;
IF = \b.\t.\e.b t e;
print (IF TRUE 1 0)
```

API：`require('./lambda0c.js')` → `{ compile(src), toScheme(src) }`。

## 2. 語法 EBNF

```ebnf
program   ::= item (";" item)* [";"]
item      ::= name "=" expr              (* 命名定義；循序、不可遞迴，遞迴請用 Z *)
            | expr                       (* 求值，如 print 42 *)
expr      ::= "\" params "." expr         (* lambda，可寫 λ；\x y. e 即 \x.\y. e *)
            | cmp
cmp       ::= add (("=="|"!="|"<"|">"|"<="|">=") add)*
add       ::= mul (("+"|"-") mul)*
mul       ::= unary (("*"|"/"|"%") unary)*
unary     ::= "-" unary | app
app       ::= atom { atom }               (* 左結合；函數全為一元 curried *)
atom      ::= int | name | "(" expr ")" | print | prefixop atom atom
prefixop  ::= "+" | "*" | "/" | "%" | "==" | "!=" | "<" | ">" | "<=" | ">="
int       ::= digits                      (* 十進位；-5 由一元負號處理 *)
comment   ::= "--" 至行尾
```

`print` 為保留字（永遠是內建輸出：印出並換行；不可定義）。
另保留不可定義：`display`、`modulo`（編譯器展開式內部使用）。
`%TRUE`/`%FALSE` 為編譯器內部名（含 `%`，lexer 寫不出來，不會碰撞）。

## 3. 語意

* **純粹性**：source 語言沒有 `if/true/false/letrec/字串/串列`——全部是函數（或 `int`）。
* **整數比較回傳真正的 Church 布林**：`a == b` 展開為
  `(if (= a b) %TRUE %FALSE)`，其中 `%TRUE/%FALSE` 是前置的普通 lambda
 （`\x.\y.x`），`if` 借用 `lispc` 現成的特殊形式——要分支的「那一下判斷」
  是實現細節，source 層看不見，使用者自定的 `IF` 照常用。
* **call-by-value**（繼承自 VM）：`Y` 會無窮迴圈（只能定義、不能呼叫），遞迴請用 `Z`；
  Church 版 `IF` 的兩分支須包成 thunk（`(\d. …)`），用 dummy（慣例 `0`）驅動，
  否則兩邊都先求值。
* 命名定義循序生效、不可自指（`f = …f…` 的 `f` 是未定義）；`print` 印整數（函數印 `#<procedure …>`）。
* 前綴運算子恰接兩個原子參數；減法請用中綴（`n - 1`），前綴 `(- n 1)` 讀成 negation
  （與 `lambdac.js` 一致）；函數參數中的負數須加括號（`f (-5)`）。

## 4. 編譯原理

`lex`（`--` 註解、整數、`\`/`λ`、雙元運算子最長匹配）→ `Parser`
（`parseProgram/parseItem/parseLam/parseCmp/parseAdd/parseMul/parseUnary/parseApp/parseAtom`；
`\x y.` 降為巢狀一元 lambda；應用左結合）→ `gen` 直吐 Scheme 字串
（`print e` → `(begin (display e) (newline))`；中綴/前綴原語扁平化為 n 元 prim 呼叫；
比較展開為 `if` + `%TRUE/%FALSE`）→ 前置 `%TRUE/%FALSE` 的 `(define …)` →
`lispc.compile`。多參函式不另設 arity 機制（已是巢狀一元閉包），天然支援部分套用；
尾呼叫由 `lispc`/`vm` 的 `TAILCALL` 保證。

## 5. 範例（`lambda0/`，各檔獨立、`vm`/`wasm` 輸出一致）

| 檔案 | 內容 |
|---|---|
| `00_hello.l0` | 命名、整數、`print` |
| `01_booleans.l0` | `TRUE/FALSE/IF/NOT/AND/OR` + 整數比較餵 `IF` |
| `02_pairs.l0` | `PAIR/FST/SND` + 巢狀取 projection |
| `03_ycombinator.l0` | `Y`（僅定義）/`Z` + thunk 階乘、費氏數（120/3628800/55/610） |
| `04_lists.l0` | fold 編碼串列：`NIL/CONS/ISNIL/HEAD/TAIL/LENGTH/SUM/MAP`，不需 `Z` |

## 6. 功能邊界

* 無型別檢查（錯用如 `5 6` 到執行期才報「不是可呼叫的物件」）。
* 無字串（`print` 只能印整數/函式形）、無 `letrec`/相互遞迴（請用 `Z` 寫不动点）。
* 與 `lambdac.js` 的關係：後者多了 `let/letrec/if/字串/串列/nil/symbol` 等糖與額外原語；
  本檔案是刻意做小的 Church 子集，兩者輸出格式相容（同為 LBC v1）。
