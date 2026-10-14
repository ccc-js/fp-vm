# lispc.js — 說明文件

`lispc.js` 是本專案的中樞：迷你 Scheme 風格 Lisp → **LBC v1 中間碼**（`.lbc`）編譯器。
所有上層語言（`lambdac`、`cljc`、`mlc`、`ocamlc`）都先降級為 Scheme 核心，再經它產生 `.lbc`，由 `vm.js` / `vm2wasm.js` 執行。

## 1. 用法

```bash
node lispc.js input.lisp [-o output.lbc]   # 預設輸出 input.lbc
node lispc.js input.lisp -o -              # 輸出到 stdout
node vm.js output.lbc                      # 用 JS 虛擬機執行
```

`example.lisp`：

```lisp
(define (fact n)
  (if (<= n 1) 1 (* n (fact (- n 1)))))
(display (fact 10))
```

API：`require('./lispc.js').compile(schemeSource) -> lbcText`，另有 `parse`。

## 2. 輸入語法 EBNF

```ebnf
program   ::= form*
form      ::= atom | list
list      ::= "(" form* ")"
atom      ::= number | boolean | string | symbol
number    ::= [-+]? ( digits [. digits] | . digits )   (* 十進位，JS double *)
boolean   ::= "#t" | "#true" | "#f" | "#false"
string    ::= '"' ( '\\n' | '\\t' | char )* '"'
symbol    ::= [^ \t\n()';"]+
comment   ::= ";" 至行尾
quote     ::= "'" form                          (* 讀入期展開為 (quote form) *)
```

特殊形式（`comp` 內 `switch (head.name)` 直接處理，其餘視為函式應用）：

```ebnf
special   ::= "(quote datum)"
            | "(if test then [else])"
            | "(define name expr)" | "(define (f args...) body...)"
            | "(set! name expr)"
            | "(lambda params body...)" | "(lambda rest body...)"
            | "(begin expr...)"
            | "(let ([v e]...) body...)" | "(let name ([v e]...) body...)"  (* 具名 let *)
            | "(let* ([v e]...) body...)" | "(letrec ([v e]...) body...)"
            | "(cond clause...)" | "(and e...)" | "(or e...)"
            | "(when c body...)" | "(unless c body...)"
```

除 `quote/if/define/set!/lambda/begin/let 系列/cond/and/or/when/unless` 外一切皆為應用；
`and/or/cond/when/unless` 在編譯期改寫為 `if`（見 §4）。

## 3. LBC v1 中間碼 EBNF 與語意

文字檔，一行一個項目；第一個函式必須是 `main`。

```ebnf
lbc       ::= { func }
func      ::= ".func" name { param } [ "." rest ] "\n" { instr }
instr     ::= "CONST" json            (* 推入常數 *)
            | "VOID"                  (* 推入未定義值 *)
            | "LOAD" name             (* 讀變數 *)
            | "DEF" name              (* 彈出並在目前環境定義，推入 VOID *)
            | "SET" name              (* 彈出並修改已存在變數，推入 VOID *)
            | "POP"                   (* 丟棄堆疊頂 *)
            | "JMP" label
            | "JF" label              (* 彈出值，為 #f 則跳 *)
            | "CLOSURE" funcname      (* 以目前環境建立閉包 *)
            | "CALL" n | "TAILCALL" n (* [... f a1..an] -> 結果；TAILCALL 重用框架 *)
            | "RET" | "HALT"
            | label ":"
json      ::= number | true | false | string | null
            | '{"sym":"name"}' | '{"list":[...]}'
```

核心不變量：**每個運算式恰好在堆疊留下 1 個值**。
`JF` 只認 `#f` 為假（`0`、`""`、`()` 皆為真，Scheme 語意）。
`TAILCALL` 保證尾遞迴不增長呼叫堆疊（`vm.js` 重用框架，`vm2wasm.js` 用 `return_call`）。

## 4. 原理：編譯策略

`compile(src) = new Compiler().compileProgram(parse(src))`，三階段：

1. **Reader**（`tokenize`/`parse`）：`(`/`)`/`'`/字串（含 `\n \t`）/數字/布林/符號；`'x` 讀入期展開。
2. **Codegen**（`Compiler.comp(x, code, tail)`，`tail` 旗標逐層傳遞）：
   - `if`：尾位時兩分支各自 `RET`/`TAILCALL`，非尾位用 `JMP/LABEL` 合流。
   - `define`：`(define (f a) …)` 與 `(define f (lambda …))` 直接建 `CLOSURE`；其餘先編值。
   - `let/let*/letrec`：降級為 lambda 應用（具名 `let` 降為遞迴定義的立即套用）；`letrec` 用「空 lambda 包 `define`」在堆積框架上建遞迴環境（不吃 JS 堆疊）。
   - `cond/and/or/when/unless`：macro 化為巢狀 `if`；`or` 用 gensym 保證單次求值。
   - 一般應用：先編函式與各引數，再 `CALL n`（尾位則 `TAILCALL n`）。
3. **Emit**：`main` 函式依序編譯（項目間補 `POP`），輸出 `.func` 與標籤。

函式參數支援點記法 `. rest`（可變參數），由 VM 收集為 list。

## 5. 功能邊界

* 無巨集系統、無 `call/cc`、無異常處理（`error` 原語直接中止）。
* `set!` 只能修改已存在變數（VM 查無則報錯）。
* 常數僅上述 JSON 子集（無 char/vector 型別；上層編譯器以函式呼叫合成）。
* 錯誤訊息為英文（`缺少 ")"`、`空的應用 ()` 等），行號僅 LBC 載入期提供。
