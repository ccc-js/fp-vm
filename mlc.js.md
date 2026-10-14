# mlc.js — 說明文件

`mlc.js` 是 **迷你 ML（OCaml 風格，無 module 系統）→ LBC v1** 編譯器。
定位是 `ocamlc.js` 的精簡版：同樣的 Hindley–Milner 核心與 Scheme 後端，
但**沒有 module / functor / open / include**，適合只想學 HM 與函數式的讀者。
（`ml/` 目錄範例用它編譯；要完整語言請用 `ocamlc.js`。）

## 1. 用法

```bash
node mlc.js prog.ml [-o prog.lbc]   # 預設 prog.lbc
node mlc.js prog.ml --types         # 只印每個頂層定義的型別
node mlc.js prog.ml --scheme        # 只印 Scheme 核心
node mlc.js prog.ml --no-check      # 略過型別檢查
node vm.js prog.lbc
```

```ocaml
let rec fact n = if n <= 1 then 1 else n * fact (n - 1)
let () = print_endline (string_of_int (fact 10))
```

## 2. 語法 EBNF

```ebnf
program   ::= { ";;" | item }
item      ::= type_decl | external | let_top | expr
type_decl ::= "type" typedef { "and" typedef }
typedef   ::= [typarams] name "=" ( record | variant | alias )
record    ::= "{" field ":" type { ";" field ":" type } [";"] "}"
variant   ::= ["|"] Ctor ["of" type {"*" type}] { "|" Ctor [...] }
alias     ::= type
type      ::= tvar | name | "(" type { "," type } ")" name
            | type "->" type | type {"*" type} | argtype name   (* 'a list *)
external  ::= "external" name ":" type "=" string
let_top   ::= "let" ["rec"] binding { "and" binding }
binding   ::= name params ["=" ...] "=" seq | pattern "=" seq
expr      ::= "let" ["rec"] bindings "in" seq
            | "fun" pat+ "->" seq | "function" arms
            | "match" seq "with" arms | "if" e "then" e ["else" e]
            | "while" seq "do" seq "done" | "for" id "=" e ("to"|"downto") e "do" seq "done"
            | assign
assign    ::= tuple [ ":=" assign ]
tuple     ::= binop { "," binop }
binop     ::= 一元 { op 一元 }   (* 優先序見 §3；右結合層一次只吃一層 *)
pattern   ::= or_pat ["as" name]
or_pat    ::= tuple_pat { "|" tuple_pat }   (* 各選項不可綁定變數 *)
tuple_pat ::= cons_pat { "," cons_pat }
cons_pat  ::= app_pat ["::" cons_pat]
app_pat   ::= Ctor [atom_pat] | atom_pat
atom_pat  ::= name | "_" | literal | "(" pattern [":" type] ")"
            | "[" [pattern {";" pattern}] "]"
            | "{" [name ["=" pattern] {";" ...}] "}"
            | "-" number
literal   ::= int | float | string | true | false | "()"
```

運算子優先序（低→高）：`||` → `&&` → 比較/`=`/`<>`/`& $`類 → `@ ^` → `::`（右）→
`+ -` → `* / mod`（`mod` 為關鍵字）→ 自訂 `**` 類（右）。`&&/||` 短路。
不支援：`try/exception/mutable/lazy/class/object`（關鍵字見即報錯）、`char` 字面值、
`[| |]`、`.( )`、`let*/and*`、`land/lor/lxor/lsl/lsr/asr`、`mutable` 欄位。

## 3. 語意

* 靜態型別 + HM 推論 + `let` 多型；**嚴格 value restriction**（非語法值一律不泛化，
  比 `ocamlc.js` 的放寬版保守）。
* `int`/`float` 兩套運算子（`+` vs `+.`），不隱式轉換；`=` 結構相等，
  `< > <= >=` 僅數字（此版 VM 語意；注意 `ocamlc.js` 已放寬至字串）。
* `ref/!/:=`（閉包實現）、`while/for`、`record`（不可變欄位）皆為核心語意。
* match 失敗 → 執行期 `Match_failure`（無窮盡性靜態檢查）。

## 4. 函式庫（PRELUDE，以 ML 自寫）

`'a option`、`('a,'b) result`；externals：四則/`mod`/`~-`、浮點四則/`~-.`、
`=→equal?`、`==→eq?`、比較、`not ^ @ :: fst/snd`、`ref/!/:=`、`failwith→error`、
`abs/min/max`、`float_of_int/int_of_float/string_of_int`、`print_*`、`String.length`、
`List.length/rev/hd/tl`；`Printf.printf/sprintf` 為編譯期特殊式（`%d %s %f %b` + 寬度/精度）。
lets：`<> != |> @@ ignore incr decr succ pred compare invalid_arg assert print_endline …`、
`string_of_bool/float print_float Fun.id/const/flip`、`List.map/mapi/iter/fold/filter/exists/assoc/sort(merge sort)…`、
`Option.map/bind/value/get/is_some/is_none`、`String.concat`。

## 5. 原理（與 `ocamlc.js` 共享架構，減去 module）

`lex`（巢狀註解、`Module.func` 合併、`=-1` 特判）→ `Parser` 類
（`parseProgram/parseItem/.../parseAssign/parseTuple/binOp/parseBin/mkBin/parseUnary/parseApp/parsePostfix/parseAtom/parseRecord`）→
HM（`convType/declareTypes/infer/inferPat/inferLet/checkItem`，`unify/prune/instantiate/generalize/adjustLevels`）→
AST→Scheme（`patCompile/prepParams/genMatch/genBindings/genPrintf/gen/genItem`；
多參函式產 `f/k + curried f` 雙名；`match` 編 `if` 鏈）→ `setup/translate`（prelude 依賴分析只留用到的）→ `lispc.compile`。
`LBC_PRIMS` 與 `ocamlc.js` 相同（VM 原語全集），`RESERVED` 防 mangling 碰撞。

## 6. 與 `ocamlc.js` 對照

| 面向 | `mlc.js` | `ocamlc.js` |
|---|---|---|
| module/functor/open/include/sig | 無（關鍵字報錯） | 完整（defunctorize，generative） |
| `char/bytes/array`、`[| |]`、`.( )`、`mutable` | 無 | 有 |
| `land/lor/lxor/lsl/lsr/asr`、`**` | 無 | 有 |
| `let*/let+/and*/and+` | 無 | 有 |
| or-樣式綁定 | 禁止 | 允許（同名同型） |
| value restriction | 嚴格版 | 放寬版（協變可泛化） |
| `Result/Bytes/Array/Hashtbl/Seq/Char/Int/Float`、`%c %x %X %o` | 無 | 有 |
