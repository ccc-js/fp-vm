#!/bin/sh
for f in lisp/*.lisp; do
  echo "=== $f ==="
  node lispc.js "$f" 2>/dev/null && node lispvm.js "${f%.lisp}.lbc"
done
