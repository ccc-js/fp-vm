# lean0kernel.js — 說明文件

`lean0kernel.js` 是微型 Lean4 的**可信任小核心**（LCF 式拆分的核心側）：
純函數、無 I/O、無全域狀態、無未定元儲存。`lean0c.js`（elaborator）做的
每件事——隱式參數、一階合一、tactic——最終都要過它重查才算數。

## 1. 職責邊界

| | kernel（本檔） | elaborator（`lean0c.js`） |
|---|---|---|
| 未定元 | 看到即報錯（防火牆） | 擁有 `G.metas`，經 `flex` 介面代入 |
| 展開策略 | 全部展開（無 rigid 概念） | rigid-first 保一階合一 |
| 隱式 binder | 無（全為顯式） | 自動插入 meta |
| tactic/Parser/CLI | 無 | 全在這裡 |
| I/O | 無 | 有 |

`flex` 介面：`{ get(id) → term|undefined, set(id, term) } | null`。
`null`＝嚴格模式（供 `checkDef`）；elaborator 傳自己的存取器。

## 2. 核心項

`var/const/sort(n)/pi/lam/app/let/sigma/pair/fst/snd`、
`nat/zero/succ/natlit/natrec(motive,zero,succ,target)`、
`bool/true/false/boolrec`、`eq(ty,lhs,rhs)/refl/eqrec(motive,h,target)`。

## 3. 函式一覽

* `subst/freeVars`——capture-avoiding 代換（fresh 改名）。
* `whnf(e, consts, full?, flex?)`——beta／iota（`Zero/Succ/Lit` 三態＋大數迴圈）
  ／zeta／delta（閉值；`full` 另展無自由變數的 Pi/Sort 值）。
* `defeq(a, b, consts, fuel?, flex?)`——剛性同頭優先結構比對（保一階），
  落回 whnf 比對；`Zero ≡ Lit 0`；大數先比值；fuel 耗盡報錯。
* `inferK/checkK`——全顯式項的推論／檢查（含 `natrec/boolrec/eqrec` 節點的
  motive 程序檢查；`rfl` 需期望為 `Eq` 且兩邊 defeq）。
* `sortOfK/piSort`——`Prop` impredicative（codomain Prop 必落 Prop）。
* `checkDef(ty, val, consts)`——`ty` 須為 Sort、`val` 須具 `ty`；回傳用到的
  公理集合（供 `#print axioms`）。

## 4. 為何這樣拆是對的

* **除錯定位**：`kernel 重查失敗 (內部錯誤)`＝elaborator 送了壞項，
  直接看 kernel 訊息，不必在 tactic 層瞎猜（本次重構即靠此抓到
  「存入項含已指派 meta 節點」一案——解法：存入前 `inst` 徹底展開）。
* **心智負擔**：kernel 約 500 行、零全域，將來要審查 soundness
  只看這一份；elaborator 的啟發式（rigid、延後 rfl、simp）壞了也不會誤收。
* **可替換**：哪天要 NbE／de Bruijn levels，只要換掉本檔，
  surface 語言與 tactic 不動。

## 5. 功能邊界

* kernel 不保證終止證明（靠「無遞迴定義」維持；`defeq` 有 fuel 背擋）。
* 無 proof irrelevance、無 universe 多型（見 `lean0c.js.md`）。
* tactic 證明目前存佔位 `rfl`＋公理日誌（只重查陳述的良構性），
  完整證明項重建是下一步（介面已留好：只要 tactic 開始建項，`checkDef` 照單全收）。
