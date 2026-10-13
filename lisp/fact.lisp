; 階乘與費氏數列
(define (fact n) (if (<= n 1) 1 (* n (fact (- n 1)))))
(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
(display "fact 10 = ") (display (fact 10)) (newline)
(display "fact 20 = ") (display (fact 20)) (newline)
(display "fib 20  = ") (display (fib 20)) (newline)
