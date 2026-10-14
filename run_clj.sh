#!/bin/sh
# 用法: sh run_clj_tests.sh
# 把 clj/*.clj 編譯成 LBC，分別用 JS 虛擬機與 wasm 執行，比對輸出是否相同。
pass=0; fail=0
for f in clj/*.clj; do
  base=${f%.clj}
  node cljc.js "$f" 2>/dev/null || { echo "編譯失敗 $f"; fail=$((fail+1)); continue; }
  node vm.js "$base.lbc" > /tmp/vm.out 2>&1
  node vm2wasm.js "$base.lbc" -o "$base.wasm" 2>/dev/null && node vm2wasm.js "$base.wasm" > /tmp/wasm.out 2>&1
  if cmp -s /tmp/vm.out /tmp/wasm.out; then echo "OK    $f"; pass=$((pass+1)); else echo "DIFF  $f"; fail=$((fail+1)); fi
done
echo "通過 $pass ，失敗 $fail"
[ $fail -eq 0 ]
