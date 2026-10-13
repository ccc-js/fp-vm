;; 04_programs.clj : 完整的小程式 —— FizzBuzz、質數、quicksort、字數統計、堆疊機

;; FizzBuzz
(defn fizzbuzz [n]
  (cond (zero? (mod n 15)) "FizzBuzz"
        (zero? (mod n 3))  "Fizz"
        (zero? (mod n 5))  "Buzz"
        :else n))
(println (map fizzbuzz (range 1 16)))

;; 質數 (試除法)
(defn prime? [n]
  (and (> n 1)
       (loop [d 2]
         (cond (> (* d d) n) true
               (zero? (mod n d)) false
               :else (recur (inc d))))))
(println "primes < 60:" (filter prime? (range 60)))

;; quicksort
(defn qsort [[pivot & more]]
  (if (nil? pivot)
    []
    (concat (qsort (filter #(< % pivot) more))
            [pivot]
            (qsort (filter #(>= % pivot) more)))))
(println (qsort [5 3 8 1 9 2 7 3 6]))

;; 字數統計
(def words ["the" "quick" "brown" "fox" "jumps" "over" "the" "lazy" "dog" "the" "end"])
(def freq (frequencies words))
(println freq)
(println "most common:" (first (sort-by (comp - val) freq)))
(println "unique words:" (count (distinct words)) "| total:" (count words))
(println (join " " (map name [:alpha :beta :gamma])))

;; 帳戶 (atom + map)
(def account (atom {:balance 100 :history []}))
(defn deposit [amt]
  (swap! account (fn [a] (-> a (update :balance + amt) (update :history conj [:deposit amt])))))
(defn withdraw [amt]
  (if (> amt (:balance @account))
    (println "insufficient funds for" amt)
    (swap! account (fn [a] (-> a (update :balance - amt) (update :history conj [:withdraw amt]))))))
(deposit 50) (withdraw 30) (withdraw 500) (deposit 5)
(println @account)
(println "final balance:" (:balance @account))

;; 堆疊機 (reduce + case)
(defn run-program [prog]
  (reduce (fn [stack op]
            (case op
              :add (conj (pop (pop stack)) (+ (peek (pop stack)) (peek stack)))
              :mul (conj (pop (pop stack)) (* (peek (pop stack)) (peek stack)))
              :dup (conj stack (peek stack))
              (conj stack op)))
          []
          prog))
(println (run-program [2 3 :add :dup :mul 4 :add]))

;; Collatz 最長序列
(defn collatz-len [n]
  (loop [n n steps 1]
    (if (= n 1) steps (recur (if (even? n) (quot n 2) (inc (* 3 n))) (inc steps)))))
(println "longest collatz under 30:"
         (reduce (fn [best n] (if (> (collatz-len n) (collatz-len best)) n best)) 1 (range 1 30)))
