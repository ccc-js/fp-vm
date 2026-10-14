#!/bin/sh
for f in lisp/*.lisp; do
  echo "=== $f ==="
  node lispc.js "$f" 2>/dev/null && node vm.js "${f%.lisp}.lbc"
done
