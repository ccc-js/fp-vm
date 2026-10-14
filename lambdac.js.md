# lambdac.js — 說明文件

`lambdac.js` 是 **無型別 Lambda Calculus → LBC v1** 編譯器（經 Scheme 核心），用於教學
「從 λ 演算長出程式語言」。語意為 call-by-value、全函式 curried（單參數）。

## 1. 用法

```bash
node lambdac.js input.lc [-o output.lbc]   # -o - 表 stdout；預設 input.lbc
node vm.js output.lbc
```

`01_basics.lc`：

```
-- 註解以 -- 開頭
let id x = x;
letrec fact n = if n <= 1 then 1 else n * fact (n - 1);
display (fact 10);
```

## 2. 語法 EBNF

```ebnf
program   ::= item ( ";" item )* [ ";" ]
item      ::= expr
            | "let" name param* "=" expr        (* 頂層定義 *)
            | "letrec" name param* "=" expr     (* 頂層遞迴定義 *)
expr      ::= "\" params "." expr               (* lambda，可寫 λ；\x y. e 即 \x.\y. e *)
            | "let" x "=" e "in" e              (* ≡ (\x. body) e *)
            | "letrec" x "=" e "in" e
            | "if" c "then" a "else" b
            | expr "||" expr | expr "&&" expr    (* 短路，右結合由外而內 *)
            | expr ("==" | "!=" | "<" | ">" | "<=" | ">=") expr
            | expr "::" expr                    (* cons，右結合 *)
            | expr ("+" | "-") expr
            | expr ("*" | "/" | "%") expr
            | app
app       ::= atom { atom }                     (* 左結合 curried 應用 *)
atom      ::= number | string | true | false | nil | "()" | "'symbol"
            | "[" [expr ("," expr)*] "]"        (* cons 鏈糖 *)
            | variable | "(" expr ")"
            | "(+)" "(-)" …                     (* 運算子當函式 *)
```

優先序由低到高：`||` → `&&` → 比較 → `::` → `+-` → `*/%`。
一元 `-`：常數折疊，否則 `(- 0 e)`；`!=` 降為 `not (equal? …)`。

## 3. 語意

* 基礎型別與 `lispc` 相同：數字（double）、布林、字串、符號、pair/list、`nil`（空串列）。
* `&&` 編為 `if`，`||` 編為 `let gensym + if`（單次求值短路）。
* 內建函式亦可 curried：`map (add 1) xs`、`foldl (+) 0 xs` 皆可（編譯期依 arity 做 eta 展開）。

## 4. 內建函式（表面名 → VM 名，arity）

`+ - * /`（2）、`%→modulo`（2）、`==→equal?`、`!=`、`</>/<=/>=`（2）、`::→cons`（2）、
`quotient remainder modulo abs min max`、`not`（1）、`eq? equal?`（2）、
`cons`（2）、`car/cdr`（1）、`null? pair? number? string? symbol? zero? even? odd?`（1）、
`length`（1）、`append`（2）、`reverse`（1）、
`string_append→string-append`（2）、`string_length→string-length`（1）、
`number_to_string→number->string`（1）、`display write newline error`（1）。

## 5. 原理：編譯策略

`tokenize`（`--` 註解、`"…"` 含 `\n \t`、`'sym`、`lam`/`λ`、雙元運算子）→
`Parser`（`parseProgram/parseItem/parseBinding/parseExpr/parseBin分層/parseUnary/parseApp/parseAtom`；
`LEVELS/OPMAP` 表驅動優先序）→ `Compiler` 直編 LBC Scheme 核心：

* 每 `lam` 一個單參數 `.func`（`compileLam`，尾位 `RET`）；應用展平為連續 `CALL 1`，
  尾位最後一個用 `TAILCALL 1`。
* 未遮蔽的內建名經 `expandPrim`：多參一次套用、少參 gensym eta 展開包 `lam`。
* `let x=v in b ≡ (\x.b) v`；`letrec` 用 0 參 thunk 閉包先 `DEF` 再編 body，
  以 `CALL 0/TAILCALL 0` 建立遞迴環境。
* `if` 編 `JF/JMP/LABEL`（尾位兩分支皆 tail）；頂層合成單一 `main`（定義間補 `POP`，結尾 `HALT`）。

## 6. 功能邊界

* 無型別檢查、無模式匹配、無字串插值；`%` 即 `modulo`（可為負）。
* 與 `lispc.js` 的差別：本檔案自帶 lexer/parser 直出 LBC，不经过 `lispc.js` 的 `compile`（格式相容，可互換執行）。
