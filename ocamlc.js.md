# ocamlc.js — 說明文件

`ocamlc.js` 是本專案最完整的編譯器：**OCaml 風格（含 module/functor）→ LBC v1**。
管線：`ML --lexer/parser--> AST --HM 型別推論--> Scheme 核心 --lispc.js--> LBC`，
由 `vm.js` / `vm2wasm.js` 執行。`ocaml/` 目錄範例（`01`-`07`）用它編譯。

## 1. 用法

```bash
node ocamlc.js prog.ml [-o prog.lbc]   # 預設 prog.lbc
node ocamlc.js prog.ml --types         # 只印頂層定義的型別
node ocamlc.js prog.ml --scheme        # 只印 Scheme 核心
node ocamlc.js prog.ml --no-check      # 略過型別檢查
node vm.js prog.lbc
```

```ocaml
type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree
let rec size = function Leaf -> 0 | Node (l, _, r) -> size l + 1 + size r
```

## 2. 語法 EBNF

```ebnf
program   ::= { ";;" | item }
item      ::= type_decl | external | module_item | "open" path
            | "include" mexpr | let_top | expr
type_decl ::= "type" typedef { "and" typedef }
typedef   ::= [typarams] name "=" ( record | variant | alias )
record    ::= "{" ["mutable"] field ":" type { ";" … } [";"] "}"
variant   ::= ["|"] Ctor ["of" type {"*" type}] { "|" … }
external  ::= "external" name ":" type "=" string
let_top   ::= "let" ["rec"] binding { "and" binding }
(* --- module --- *)
module_item ::= "module" Name params [":" sig] "=" mexpr
            | "module" "type" Name "=" sig
params    ::= { "(" Name ":" sig ")" | "(" ")" }
mexpr     ::= "struct" items "end" | "functor" "(" Name ":" sig ")" "->" mexpr
            | "(" mexpr [":" sig] ")" | path | mexpr "(" mexpr ")"
sig       ::= "sig" spec* "end" | Name ["with" "type" …]
spec      ::= "val" name ":" type | "type" … | "module" Name ":" sig | "include" sig
(* --- 運算式 --- *)
expr      ::= bindop | "let" ["rec"] bindings "in" seq | "let" "open" path "in" seq
            | "fun" pat+ "->" seq | "function" arms
            | "match" seq "with" arms
            | "if" e "then" e ["else" e]
            | "while" seq "do" seq "done"
            | "for" id "=" e ("to"|"downto") e "do" seq "done"
            | assign
bindop    ::= ("let*"|"let+"|…) pat "=" e {("and*"|…) …} "in" seq   (* monad do 記法，需先定義 ( let* ) *)
assign    ::= tuple [ (":=" | "<-") assign ]   (* := 給 ref；<- 給 mutable 欄位/陣列元素 *)
tuple     ::= binop { "," binop }
arms      ::= ["|"] pat ["when" e] "->" seq { "|" … }
(* --- 樣式 --- *)
pattern   ::= or_pat ["as" name]
or_pat    ::= tuple_pat { "|" tuple_pat }   (* 各選項須綁定相同變數（同型別） *)
tuple_pat ::= cons_pat { "," cons_pat }
cons_pat  ::= app_pat ["::" cons_pat]
app_pat   ::= Ctor [atom_pat] | atom_pat
atom_pat  ::= name | "_" | literal | char | "(" pattern [":" type] ")"
            | "[" [pattern {";" pattern}] "]" | "{" [f ["=" pattern] {";"…}] "}"
            | "-" number
literal   ::= int | float | string | true | false | "()"
char      ::= "'" (char | "\\nrtb\\'\" " | "\ddd" | "\xhh") "'"
```

運算子優先序（低→高）：`||` → `&&` → 比較/`=`/`<>`/`& $`類 → `@ ^` → `::`（右）→
`+ -` → `* / mod land lor lxor` → `** lsl lsr asr`（右）。
字面值：`42 0xFF` 不支援（十六進位尚未實作）→ 十進位/`_` 分隔/浮點 `1e-3`；
字串 `"…"`（`\n \t \r \b \0`，原始碼 UTF-8）。

## 3. 語意

* **型別系統**：Hindley–Milner + `let` 多型 + 放寬版 value restriction
  （僅出現在協變位置的變數仍可泛化，與 OCaml 同；`array`/`ref` 參數視為不變）。
  內建 `int float string char bytes bool unit 'a list 'a array 'a ref`。
* **求值**：嚴格求值、call-by-value；函式全為 curried（多參是糖）。
  `int`/`float` 運算子分家（`+` vs `+.`）；`=` 結構相等；
  `< > <= >=` 支援數字與字串（字典序）；`compare` 為跨型別結構比較。
* **資料**：`tuple/record`（`{r with x}` 拷貝更新；`mutable` 欄位以 `set-car!` 原地改）、
  `variant`（多型遞迴）、`list`、`array`（`[| |]`/`.( )`，VM 原生向量）、
  `bytes`（獨立型別，向量底數）、`char`（Unicode 碼位，運行期為 1 字元字串）、
  `ref/!/:=`、`while/for`。
* **match**：`when` 守衛；or-樣式在 codegen 展開為多分支；失敗為執行期 `Match_failure`
  （無靜態窮盡檢查）。
* **Binding operators**：`let*/let+/and*/and+ … in` 降為 `( let* ) e (fun (p1,p2) -> body)`，
  每個 monad 各自定義（Option/Result/List/State 範例見 `ocaml/05_monads.ml`）。
* **Module**（defunctorize）：module 是命名空間；functor 是模板——**每次套用時展開並重做
  型別檢查與代碼產生**（generative，每次狀態獨立）；簽章做符合性檢查 + 封裝
  （抽象型別對外 opaque，未列成員隱藏）；參數只做符合性檢查（本體可見引數全部成員）。
  不支援：`let module`、`module rec`、first-class module、functor 型別、`module type of`、
  `try/exception`、`lazy`、labeled/optional、GADT/多型變體/object。

## 4. 函式庫（PRELUDE，以 ML 自寫，用到才編入）

`'a option`、`('a,'b) result`；externals：整數/浮點四則、`land/lor/lxor/lsl/asr/lsr`、
`**→pow`、`sqrt floor ceil sin cos atan2 exp log`、`mod_float`、`compare`、`Hashtbl.hash`、
`Char.code/chr`、`String.get`、`Array.make/length/get/set`、位元組後端 `__bytes_*`、
`ref/!/:=`、`failwith`、`string_of_int`、`print_*`、`String.length`、`List.length/rev/hd/tl`。
`Printf.printf/sprintf` 為編譯期特殊式：`%d %s %f %b %c %x %X %o %%` + 寬度/左右/補零/精度。
lets：`Char/String/Bytes/Array` 全套、`Hashtbl`（association+向量）、`Seq`（`seq_node` 惰性）、
`List/Option/Result`（含 `find_map/rev_map/assoc` 等）、`Int/Float` 常數、
`string_of_char/print_char/int_of_string(_opt)`、`Fun.id/const/flip`。
（`String.starts_with` 等官方標號函式改為位置參數；`Hashtbl.t` 具名為全域 `hashtbl`。）

## 5. 執行期資料表示（與 `vm.js` 對應）

`int/float`=數字（double，>2^53 失準；位運算 32 位）→ `bool`=`#t/#f` →
`string`/`char`(1 字元串) → `unit`=`()` → `tuple/list`=list →
`variant`（`C a b`=(C a b)，無參 `(C)`）→ `record`=依序 list →
`array/bytes`底層=向量 → `ref`=閉包可變格。

## 6. 原理（階段與關鍵函式）

`lex`（巢狀註解、char、`M.N.x` 合併、`land…` 關鍵字）→ `Parser`
（`parseProgram/parseItem/parseModuleItem/parseModExpr/parseSigExpr`、
`parsePat系/parseSeq/parseExpr/parseArms/parseAssign/parseBin/mkBin/parsePostfix/parseAtom/parseRecord`；
`[||]` 的 `||` token 拆分；`<-` 排除於二元運算子）→
HM（`convType/declareTypes` 含 mutable 不變性；`infer/inferPat/inferLet/checkItem`；
`unify/prune/instantiate/generalize(+Except)/occ/skolemize`；簽章 `evalSig/applySignature`）→
AST→Scheme（`patCompile/prepParams/genMatch（or 展開）/genBindings（f/k 雙名）/genPrintf/gen/genItem`；
`fieldset→set-car!`、`array→vector`）→ module elaboration
（`elabModExpr/processItem`；`NS` 限定名註冊）→ `setup/translate`（prelude 依賴分析）→ `lispc.compile`。
`--types` 印 `TYPE_LINES`（封裝後型別）；`--scheme` 印中間 Scheme。
