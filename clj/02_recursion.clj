;; 02_recursion.clj : loop/recur、尾遞迴、多元 arity、不定參數、閉包、高階函式

;; loop / recur
(defn sum-to [n]
  (loop [i 1 acc 0]
    (if (> i n) acc (recur (inc i) (+ acc i)))))
(println "sum-to 100 =" (sum-to 100))

;; 一百萬次迴圈 (recur 是真正的尾呼叫，不會爆堆疊)
(println "sum-to 1000000 =" (sum-to 1000000))

;; fn 內直接 recur
(defn fact [n]
  ((fn [n acc] (if (<= n 1) acc (recur (dec n) (* acc n)))) n 1))
(println "fact 20 =" (fact 20))

;; 一般遞迴
(defn fib [n] (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))
(println "fib 0..15:" (map fib (range 16)))

;; 互相遞迴 (declare)
(declare my-odd?)
(defn my-even? [n] (if (zero? n) true (my-odd? (dec n))))
(defn my-odd?  [n] (if (zero? n) false (my-even? (dec n))))
(println (my-even? 100) (my-odd? 7) (my-even? 7))

;; 多元 arity 與 & rest
(defn greet
  ([] (greet "world"))
  ([name] (str "Hello, " name "!"))
  ([greeting name] (str greeting ", " name "!")))
(println (greet) (greet "Clojure") (greet "Howdy" "partner"))

(defn sum-all [& nums] (reduce + 0 nums))
(println (sum-all) (sum-all 1) (sum-all 1 2 3 4 5))

(defn tag [t & items] (str "<" t ">" (join "," items) "</" t ">"))
(println (tag "li" 1 2 3))

;; 閉包與狀態
(defn make-adder [n] (fn [x] (+ x n)))
(def add5 (make-adder 5))
(println (add5 10) ((make-adder 100) 1))

(defn make-counter []
  (let [c (atom 0)]
    (fn [] (swap! c inc))))
(def c1 (make-counter))
(def c2 (make-counter))
(c1) (c1)
(println "counters:" (c1) (c2))

;; 高階函式
(def inc-then-double (comp #(* 2 %) inc))
(println (inc-then-double 5) ((partial + 10) 5) ((complement even?) 3))
(println (map (fn [[a b]] (+ a b)) [[1 2] [3 4] [5 6]]))
(println (apply + [1 2 3 4]) (apply max [3 9 2]) (apply str ["a" "b" "c"]))
(println (apply (fn [a b c] (* a b c)) [2 3 4]))

;; 一百萬層的非尾遞迴也沒問題 (VM 的呼叫堆疊在 heap)
(defn depth [n] (if (zero? n) 0 (+ 1 (depth (dec n)))))
(println "depth 50000 =" (depth 50000))
