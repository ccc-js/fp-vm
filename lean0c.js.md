# lean0c.js — 說明文件

`lean0c.js` 是**微型 Lean4 的 elaborator**（手法、tactic、codegen、命令）：
依賴型別核心（數學建構＋定理證明）→ LBC v1
（經 Scheme 核心＋`lispc.js`，用 `vm.js` 執行）。VM 完全不需修改。
**可信任的檢查在 `lean0kernel.js`**（見該文件）；本檔每存一個定義，
都以 `kernel.checkDef` 重查（不合即內部錯誤），tactic 證明則存型別＋公理依賴。

## 1. 用法

```bash
node lean0c.js input.l0 [-o output.lbc]   # -o - 表 stdout；預設 input.lbc
node lean0c.js input.l0 --elab            # 印 Scheme 核心（除錯）
node vm.js output.lbc
```

```text
theorem add_zero (n : Nat) : n + 0 = n := by
  induction n
  rfl
  intro k
  intro ih
  rw [ih]
```

## 2. 語法 EBNF

版面規則：頂層命令從 col 0 開始；接續行與 tactic 行須縮排。

```ebnf
program   ::= { command }
command   ::= "def" name binders* [":" term] ":=" term
            | ("theorem"|"lemma"|"example") [name] [":" term] (":=" term | "by" tactics)
            | "axiom" name ":" term
            | "structure" name [":="] binder-line+
            | "#check" term | "#eval" term | "#print" "axioms" [name]
binder    ::= name | "(" names ":" term ")" | "{" names ":" term "}"
term      ::= "fun" binder+ "=>" term | ("forall"|"∀") binder+ "," term
            | arrow
arrow     ::= eq ["->" arrow]                (* 右結合；A -> B 即 Pi _ : A, B *)
eq        ::= add ["=" add]                  (* a = b 即 Eq _ a b *)
add       ::= mul ["+" add]                  (* + 即 Nat.add *)
mul       ::= app ["*" ...]                  (* * 即 Nat.mul *)
atom      ::= name | number | "(" term ")" | "Prop" | "Type" | "_" | "rfl"
            | "Nat" | "Nat.zero" | "Nat.succ" | "Nat.rec"
            | "Bool" | "true" | "false" | "Bool.rec"
            | "Eq" | "Eq.subst" | "Sigma.mk" | "Sigma.fst" | "Sigma.snd"
tactics   ::= tac ((";"|換行) tac)*           (* 括號內除外 *)
tac       ::= "rfl" | "exact" term | "apply" term | "intro" name+
            | "rw" "[" [rwrule {"," rwrule}] "]" | "simp" ["[" term {"," term} "]"]
            | "induction" name | "assumption" | "swap"
rwrule    ::= ["←"] term
```

`{x : A}` 為隱式 binder（套用時自動插 meta）；`_` 為 hole；數字預設 `Nat`。

## 3. 型別系統（核心規則）

Sort：`Prop : Type`，`Type n : Type (n+1)`；Pi 形成：codomain 為 Prop 必落 Prop
（impredicative），否則取 max。`Type : Type` 的不一致性由「無 universe 多型、
層級皆具體」規避（`Type` 即 `Type 1`，不寫層級）。

| 構造 | 規則 |
|---|---|
| `Nat` | `Zero/Succ/字面值`；`Nat.rec`（motive 可進任意 Sort，程序檢查） |
| `Bool` | `true/false`；`Bool.rec` |
| `Eq A a b` | `rfl`（需 defeq）；`Eq.subst`（motive 須明寫，單端點形） |
| `Sigma` | `mk/fst/snd`（iota）；`structure` 展開為巢狀 Sigma＋投影 |
| 定義相等 | beta＋delta（非遞迴 def）＋iota＋zeta；`Zero ≡ Lit 0`；大數先比值 |

`And/Or/Exists/Not/False/True` 以 surface def（impredicative 編碼）提供；
`Nat.add/mul`、`Eq.symm/trans`、`congrArg` 同為 prelude def。
`def` 採嚴格 value restriction＋命令結束歧義檢查（含未定元即報錯）。

## 4. tactic 語意

goal 為明确上下文＋目標型別的列表（單焦點推進；`induction` 產生兩 goal）。
`rfl`（defeq 比對）、`exact`（對 goal 檢查）、`apply`（隱式插 meta，
結論一階合一，Prop 前提成新 goal）、`intro`、`rw`（defeq 匹配、改寫全部、
自動收尾 rfl，支援 `←`）、`simp [lemmas]`（重寫閉包＋rfl）、
`induction`（revert 到該變數、motive 抽象、base＋step）、`assumption`、`swap`。
`defeq` 對同頭 rigid type-former（結果為 Sort 的參數化定義：`Exists/And/Or/Not`）
優先結構比對（保一階合一），失敗才落回一般路徑——比較時任一邊含未定元即保持剛性。

## 5. 證明編譯（codegen）與 `#eval`

`Nat.rec`→`letrec` 遞迴、`NatLit`→數字、`Bool.rec`→`if`、`Sigma`→`cons/car/cdr`、
`Eq.subst`→取被代入值、`rfl`/證明→`0`、`Nat.add/mul`→遞迴函式。
`#eval e` Elaborate 後全量 emit＋`display`，行內經 `vm.js` 求值印出。
`axiom` 無值（引用即記錄）；`#print axioms [name]` 列出依賴。

## 6. 範例（`lean0/`，各檔獨立、`vm`/`wasm` 輸出一致）

| 檔案 | 內容 |
|---|---|
| `00_nat.l0` | `add_zero/zero_add/add_succ/succ_add/add_comm`＋`#check/#eval` |
| `01_logic.l0` | `and/or_comm`、`modus_ponens`、`Exists.intro`、`intro/apply/exact` |
| `02_eq.l0` | `rw` 鏈、`simp [add_zero]`、`congrArg`、`em` 公理＋追蹤 |
| `03_struct.l0` | `Point` 建構/投影/`#eval`/`rfl` |

## 7. 功能邊界（誠實聲明）

* 無 general inductive、無 universe 多型、無 typeclass、無 `calc/match` 項式複雜模式。
* defeq 無 proof irrelevance（同 Prop 的兩證明不等價，除非結構同）。
* meta 作用域 naive（occurs check 有，無 scope 剪枝）；高階合一僅 `rfl` 延後一例。
* `structure` 無參數、無單構造子語法糖；`Seq`/`Hashtbl` 等無；`Nat` 字面值上限外全為一元表示之上的字面值優化（`Lit` 直接算術，defeq 設 10000 展開上限）。
* `whnf` 兩個檔：lazy（defeq/匹配，保剛性）與 full（elab 形狀檢查、tactic 檢視，看穿閉別名）。
* type-former（結果為 Sort 的參數化定義）套用式含未定元時保持剛性—— concrete 時正常展開。
