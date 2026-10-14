# OCaml 程式學習書（對標官方 OCaml 5.5）

> 本書以官方 OCaml 5.5 系列（2025–2026，最新 5.5.1）為準，不依賴本專案自製的迷你 ML 子集。
> 目標讀者：會一種主流語言（Python / JavaScript / C），想系統學會函數式 + 模組 + 型別推論的工程師。
> 閱讀方式：依序閱讀，每節皆可在 `utop` 或 `dune exec` 中實作驗證。

- 官方網站：<https://ocaml.org/>
- 語言手冊：<https://ocaml.org/manual/5.5/>
- 標準函式庫 API：<https://ocaml.org/manual/5.5/api/>
- 版本重點：多核 runtime（Domains）、代數效應與 Effect Handlers（5.0+ 穩定，5.3+ 深層 handler 語法）、 immutable array、`Iarray`、`Pair`、`Pqueue`、UTF-8 原始碼。

## 使用環境

```bash
opam switch create 5.5.1
eval $(opam env)
opam install dune utop ocamlformat ocaml-lsp-server
dune --version   # 3.x
ocaml -version   # 5.5.1
```

## 目錄

* 第1章-認識 OCaml 與環境建置
    * [1.1 為什麼學 OCaml](01.1-why-ocaml.md)
    * [1.2 安裝 opam、dune 與 utop](01.2-install-opam-dune-utop.md)
    * [1.3 第一個程式與 REPL](01.3-first-program-repl.md)
    * [1.4 編譯與 dune 專案結構](01.4-compile-dune-project.md)
* 第2章-基礎語法與型別
    * [2.1 let、值與不可變性](02.1-let-values-immutability.md)
    * [2.2 基本型別與運算子](02.2-basic-types-operators.md)
    * [2.3 函式、柯里化與標號參數](02.3-functions-currying-labeled.md)
    * [2.4 型別推論與多型](02.4-inference-polymorphism.md)
* 第3章-複合資料與模式匹配
    * [3.1 tuple 與 record](03.1-tuple-record.md)
    * [3.2 variant 與遞迴型別](03.2-variant-recursive-type.md)
    * [3.3 list、array 與字串](03.3-list-array-string.md)
    * [3.4 match、function 與守衛](03.4-match-function-guard.md)
* 第4章-函數式設計
    * [4.1 高階函式與管線](04.1-higher-order-pipeline.md)
    * [4.2 遞迴、尾遞迴與摺疊](04.2-recursion-tailrec-fold.md)
    * [4.3 option、result 與例外處理](04.3-option-result-exception.md)
    * [4.4 延遲求值、Seq 與惰性結構](04.4-lazy-seq.md)
* 第5章-模組與標準函式庫
    * [5.1 module、簽章與封裝](05.1-module-signature.md)
    * [5.2 functor](05.2-functor.md)
    * [5.3 標準函式庫導覽](05.3-stdlib-tour.md)
    * [5.4 dune 函式庫管理與測試](05.4-dune-lib-test.md)
* 第6章-進階型別
    * [6.1 多型變體、物件與類別簡介](06.1-polymorphic-variant-object.md)
    * [6.2 GADT 與 phantom type](06.2-gadt-phantom.md)
    * [6.3 first-class module 與泛型程式](06.3-firstclass-module.md)
* 第7章-併發、效應與實戰
    * [7.1 Domain 並行與記憶體模型](07.1-domain-parallel.md)
    * [7.2 Effect Handler](07.2-effect-handler.md)
    * [7.3 Eio 實務併發](07.3-eio-practice.md)
    * [7.4 完整專案：待辦事項 CLI](07.4-todo-cli-project.md)

## 約定

- 程式碼區塊標註 `ocaml`，可在 `utop` 貼上執行。
- `(* ... *)` 為 OCaml 註解。
- 每節結尾有「練習」與「常見錯誤」。
- 檔名格式為 `章.節-英文slug.md`，例如 `01.1-why-ocaml.md`。
