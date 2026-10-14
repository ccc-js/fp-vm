#!/bin/sh
for f in lambda/*.lc; do
  echo "=== $f ==="
  node lambdac.js "$f" 2>/dev/null && node vm.js "${f%.lc}.lbc"
done
