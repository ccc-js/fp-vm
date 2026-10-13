;; 03_collections.clj : 向量 / map / 序列函式 / 解構 / for / doseq / 串接

;; 序列函式 (eager)
(println (range 5) (range 2 8) (range 0 20 5) (range 10 0 -3))
(println (take 3 (range 100)) (drop 97 (range 100)) (take-while #(< % 5) (range 10)) (drop-while #(< % 5) (range 10)))
(println (map + [1 2 3] [10 20 30]) (mapcat #(list % %) [1 2 3]) (concat [1 2] '(3) [4 5]))
(println (reverse [1 2 3]) (sort [5 2 9 1]) (sort > [5 2 9 1]) (sort-by count ["ccc" "a" "bb"]))
(println (distinct [1 2 1 3 2]) (flatten [1 [2 [3 [4]]]]) (partition 2 [1 2 3 4 5]) (interleave [:a :b :c] [1 2 3]))
(println (some even? [1 3 4]) (every? odd? [1 3 5]) (not-any? neg? [1 2]))

;; map 操作
(def person {:name "Ada" :age 36})
(def p2 (-> person (assoc :lang "lisp") (update :age inc) (dissoc :name)))
(println person p2)
(println (keys p2) (vals p2) (contains? p2 :age) (contains? p2 :name))
(println (merge {:a 1} {:b 2} {:a 99}) (select-keys {:a 1 :b 2 :c 3} [:a :c]))
(println (zipmap [:x :y :z] [1 2 3]) (frequencies ["a" "b" "a" "c" "a"]))
(println (group-by even? (range 8)))
(println (assoc-in {} [:a :b :c] 1) (update-in {:a {:n 1}} [:a :n] + 10) (get-in {:a {:b 2}} [:a :b]))
(println (= {:a 1 :b 2} {:b 2 :a 1}) (= [1 [2 3]] [1 [2 3]]) (= "a" "a") (not= 1 2))

;; vector 操作
(def v [1 2 3])
(println (conj v 4) (conj '(1 2) 0) (assoc v 1 :x) (nth v 2) (get v 9 :none) (vec '(7 8)) (into [] (range 3)))
(println (into {} [[:a 1] [:b 2]]) (mapv inc v) (peek v) (pop v))

;; 把關鍵字當函式用
(def people [{:name "Bob" :age 25} {:name "Alice" :age 31} {:name "Carol" :age 19}])
(println (map :name people))
(println (map :name (sort-by :age people)))
(println (filter #(> (:age %) 20) people))
(println (reduce + (map :age people)))

;; 解構
(let [[a b & more] [1 2 3 4 5]
      {:keys [name age] :or {age 0}} {:name "Zed"}
      [[x y] z] [[10 20] 30]]
  (println a b more name age x y z))
(defn show-person [{:keys [name age]}] (str name " is " age))
(println (map show-person people))
(let [[k v :as pair] [:key "val"]] (println k v pair))

;; for / doseq
(println (for [x (range 4)] (* x x)))
(println (for [x (range 1 4) y (range 1 4) :when (< x y)] [x y]))
(doseq [[k v] {:a 1 :b 2}] (println k "->" v))
(dotimes [i 3] (print i " "))
(println)

;; 串接巨集
(println (->> (range 20) (filter even?) (map #(* % %)) (take 5) (reduce +)))
(println (-> {:n 5} (update :n * 2) (assoc :done true)))
