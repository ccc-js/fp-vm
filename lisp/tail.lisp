; 尾遞迴: 一百萬次迴圈不會爆堆疊
(define (loop i acc) (if (= i 0) acc (loop (- i 1) (+ acc i))))
(display (loop 1000000 0)) (newline)
; 非尾遞迴深度 50000 (VM 的呼叫堆疊在 heap)
(define (count n) (if (= n 0) 0 (+ 1 (count (- n 1)))))
(display (count 50000)) (newline)
; 具名 let
(display (let lp ((i 0) (s 0)) (if (> i 100) s (lp (+ i 1) (+ s i))))) (newline)
