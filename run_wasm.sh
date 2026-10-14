#!/bin/sh
# 用法: sh run_wasm_tests.sh
# 把 tests/*.lisp 與 examples/*.lc 都編譯成 .lbc -> .wasm，
# 並比對「JS 虛擬機 (vm.js)」與「wasm」兩者的輸出是否完全相同。
pass=0; fail=0
for f in lisp/*.lisp lambda/*.lc; do
  base=${f%.*}
  case $f in *.lisp) node lispc.js "$f" 2>/dev/null ;; *.lc) node lambdac.js "$f" 2>/dev/null ;; esac
  node vm.js "$base.lbc" > /tmp/vm.out 2>&1
  node vm2wasm.js "$base.lbc" -o "$base.wasm" 2>/dev/null
  node vm2wasm.js "$base.wasm" > /tmp/wasm.out 2>&1
  if cmp -s /tmp/vm.out /tmp/wasm.out; then echo "OK    $f"; pass=$((pass+1)); else echo "DIFF  $f"; fail=$((fail+1)); fi
done
echo "通過 $pass ，失敗 $fail"
[ $fail -eq 0 ]
