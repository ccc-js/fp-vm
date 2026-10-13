;; 01_basics.clj : 基礎語法 —— def / defn / let / if / cond / case / 字串 / 集合字面值
;; 執行:  node cljc.js clj/01_basics.clj && node lispvm.js clj/01_basics.lbc

(def pi 3.14159)
(def greeting "Hello, Clojure!")
(println greeting)
(println "pi =" pi "| 2pi =" (* 2 pi))

;; 函式
(defn square [x] (* x x))
(defn hypot2 [a b] (+ (square a) (square b)))
(println "hypot2 3 4 =" (hypot2 3 4))

;; let 與條件
(defn classify [n]
  (cond
    (neg? n)  "negative"
    (zero? n) "zero"
    (< n 10)  "small"
    :else     "large"))
(println (map classify [-5 0 7 100]))

(defn describe [x]
  (case x
    1 "one"
    2 "two"
    (3 4) "three-or-four"
    :a "keyword a"
    "other"))
(println (map describe [1 2 3 4 :a 99]))

;; nil 與 false 才是假；0、空字串、空 list 都是真
(println (map #(if % "truthy" "falsey") [nil false 0 "" '() []]))
(println (and 1 2 3) (and 1 nil 3) (or nil false 7) (or nil false))

;; 集合字面值
(def v [10 20 30])
(def m {:name "Ada" :age 36 :langs ["lisp" "ml"]})
(println v m)
(println (:name m) (:age m) (:missing m) (:missing m "default"))
(println (get m :langs) (get-in m [:langs 1]) (count v) (first v) (last v))

;; 字串
(println (str "a" 1 :k nil true [1 2] {:x 1}))
(println (pr-str "quoted" 42 :kw [1 "two"]))
(prn "prn quotes strings" [1 "two" :three])

;; when / if-let / when-let
(when (> (count v) 2) (println "v has more than 2 items"))
(if-let [x (first [])] (println "got" x) (println "empty, no first"))
(when-let [x (get m :age)] (println "age is" x))

;; 數學
(println (mod 17 5) (rem -17 5) (quot 17 5) (max 3 9 4) (min 3 9 4) (abs -8) (inc 41) (dec 43))
