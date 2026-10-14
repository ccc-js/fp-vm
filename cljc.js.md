# cljc.js — 說明文件

`cljc.js` 是 **迷你 Clojure → LBC v1** 編譯器：Clojure reader 資料 → desugar 為 Scheme 核心 →
`lispc.js` → `.lbc`。標準函式庫以 Clojure 自寫 prelude，只編入用到的函式（依賴分析），VM 免改。

## 1. 用法

```bash
node cljc.js prog.clj [-o prog.lbc]   # 預設 prog.lbc
node cljc.js prog.clj --scheme        # 只印 Scheme 核心（除錯）
node vm.js prog.lbc
```

```clojure
(defn fact [n] (if (<= n 1) 1 (* n (fact (dec n)))))
(println (fact 10))
```

API：`compile(src)`、`toScheme(src)`。

## 2. 語法 EBNF（reader 層）

```ebnf
program   ::= form*
form      ::= number | string | keyword | nil | true | false
            | symbol | list | vector | map
list      ::= "(" form* ")"
vector    ::= "[" form* "]"
map       ::= "{" (form form)* "}"          (* 奇數個報錯 *)
keyword   ::= ":" symbol
string    ::= '"' ( "\\n" | "\\t" | "\\r" | "\\uXXXX" | char )* '"'
comment   ::= ";" 至行尾 | "#_" 跳過下式
sugar     ::= "'" f       → (quote f)
            | "@a"        → (deref a)
            | "#(" ... ")" → (fn [p1..] ...)  (* % %1..%9 %& 決定參數 *)
meta      ::= "^" form f  → f（丟棄）  |  "," 視為空白
```

不支援：`` ` `` `~` `#?` `#{}` `::kw`、`a/b` ratio（報錯）。

特殊形式（`SPECIAL` 表）：

```ebnf
special   ::= "(quote x)" | "(if c t [e])" | "(do e...)"
            | "(let [b...] e...)" | "(loop [b...] e...)" | "(recur e...)"
            | "(fn name? ([params] body...)...)" | "(def name e)" | "(defn ...)" | "(defn- ...)"
            | "(declare ...)" | "(ns ...)" | "comment" | "require/use/import"（忽略）
            | "(when/when-not/if-not/if-let/when-let c e...)"
            | "(cond test expr...)" | "(case e clause... default)"
            | "(and e...)" | "(or e...)" | "(-> x f...)" | "(->> x f...)"
            | "(dotimes [i n] e...)" | "(doseq [x xs] e...)" | "(for [x xs ...] e)"
defmacro/try → 直接報錯（不支援）
```

解構（`let/fn/loop/doseq/for` 綁定）：`[a b & rest :as all]`（vector，`& rest` 經 `core/_nthrest`），
`{:keys [a b] :or {…} :as m}`（map，經 `core/get`）。

## 3. 語意

* 真值：僅 `nil`/`false` 為假（`core/t?`），空 list 為**真**（與 Clojure 同）。
* `fn`：支援 `[x & rest]`、多 arity（打包 `args` + `length` 分派）、命名遞迴 `(fn self [x] …)`（→ `letrec`）。
* `recur` 僅限尾位置（編譯期檢查 `sc.recur + tail + arity`，違反報錯）。
* 無 lazy seq：`map/filter/range` 皆 eager（故無 `iterate/cycle`/無限 range）。
* `map` 為 association list（O(n)，保插入序）；`vector` 底層為 list（`nth/get` O(n)）。
* `/` 為浮點除法（無 ratio）；`(str 'sym)` 不支援（VM 無 symbol→string）。

## 4. 執行期資料表示

```ebnf
nil     ::= 符號 nil
vector  ::= ("\%vec" elem...)      (* list 包裝 *)
map     ::= ("\%map" (k v) ...)
keyword ::= ("\%kw" "name")
list    ::= 一般 LBC list
```

全常數 `Vec/MapLit` 走 `quote`，否則動態 `cons %vec/%map` 構造。
列印：`pr/pr-str` 印可讀形（`_pr` 區分 map/vector/keyword），`println` 以空白連接。

## 5. 函式庫（prelude，Clojure 自寫，約 150 個）

謂詞/基礎：`nil? some? true? false? identity inc dec pos? neg? keyword? vector? map? list? seq? name keyword`
seq：`first rest next second seq empty? cons count nth last butlast reverse vec vector peek pop`
相等：`=/not=`（常數走 `equal?`，否則 `core/_equiv` 結構比）
assoc：`conj assoc dissoc get contains? keys vals merge update get-in assoc-in update-in select-keys zipmap frequencies group-by`
eager 序列：`map mapv filter filterv remove reduce range repeat take drop take-while drop-while concat mapcat into some every? distinct flatten partition interleave interpose keep doall dorun run!`
排序：`sort sort-by`（merge sort）；高階：`apply comp partial complement constantly`
字串/列印：`str pr-str println print prn pr join`；並行原語：`atom deref reset! swap!`
（atom = `fn [op x]` 閉包 + `%set!` 實現）。

## 6. 原理：desugar 與依賴分析

`readAll`（reader：`readForm/readSeq/readString/anonFn` 掃 `%N` 定參數）→
`collectGlobals` 預掃頂層名（解前向引用）→ `ex/exBody/exCall` 遞迴改寫為 Scheme AST
（巨集式先還原再 `ex`，如 `if-let→let+if`、`case→let+cond+%equal?`、`->/->>→線性摺疊`、
`for→map/mapcat+filter`、`(:k m)→core/get`；`apply +/*/...` 走 `APPLY_REWRITE` 快徑）→
`toScheme` 依賴分析（`scanCore` 收集 `core/`，BFS 只拼用到的 prelude `define`）→ `lispc.compile`。
名稱：`resolveName`（`%x` 剝 `%` 直通原語 → 局部 → `core/` → `a/b→b` → `ALIAS{mod/rem/quot}` → 原語原樣），
`ident` mangling（`'`→`_q`，保留字加 `u/` 前綴）。
