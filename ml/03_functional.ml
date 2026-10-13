(* 03_functional.ml : 函數式程式設計 —— 高階函式、柯里化、閉包、ref、尾遞迴、排序 *)

(* ── 高階函式與自訂運算子 ── *)
let compose f g x = f (g x)
let ( >> ) f g x = g (f x)                  (* 自訂運算子: 先 f 後 g *)
let twice f x = f (f x)
let add a b = a + b
let inc = add 1
let double x = x * 2
let () = Printf.printf "%d %d %d\n" (compose double inc 5) ((double >> inc) 5) (twice double 3)

(* 管線運算子 |> *)
let result =
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
  |> List.filter (fun x -> x mod 2 = 1)
  |> List.map (fun x -> x * x)
  |> List.fold_left (+) 0
let () = Printf.printf "sum of odd squares = %d\n" result

(* 自己實作 map / filter / fold *)
let rec my_map f = function [] -> [] | x :: xs -> f x :: my_map f xs
let rec my_filter p = function
  | [] -> []
  | x :: xs -> if p x then x :: my_filter p xs else my_filter p xs
let rec my_fold f acc = function [] -> acc | x :: xs -> my_fold f (f acc x) xs
let show_list l = "[" ^ String.concat "; " (List.map string_of_int l) ^ "]"
let () = print_endline (show_list (my_map (fun x -> x + 100) [1; 2; 3]))
let () = print_endline (show_list (my_filter (fun x -> x > 2) [1; 2; 3; 4]))
let () = Printf.printf "%d\n" (my_fold (fun a b -> a * b) 1 [1; 2; 3; 4; 5])

(* 回傳函式的函式、閉包 *)
let make_adder n = fun x -> x + n
let add5 = make_adder 5
let () = Printf.printf "%d %d\n" (add5 1) ((make_adder 100) 1)

let make_counter () =
  let c = ref 0 in
  (fun () -> c := !c + 1; !c)
let c1 = make_counter ()
let c2 = make_counter ()
let _ = c1 ()
let _ = c1 ()
let () = Printf.printf "counters: %d %d\n" (c1 ()) (c2 ())

(* 用 ref 做記憶化: fib 40 只需 40 次遞迴 *)
let memo_fib =
  let cache = ref [] in
  let rec fib n =
    if n < 2 then n
    else match List.assoc_opt n !cache with
      | Some v -> v
      | None ->
        let v = fib (n - 1) + fib (n - 2) in
        cache := (n, v) :: !cache;
        v in
  fib
let () = Printf.printf "fib 40 = %d\n" (memo_fib 40)

(* ── 遞迴 ── *)
let rec even n = if n = 0 then true else odd (n - 1)
and odd n = if n = 0 then false else even (n - 1)
let () = Printf.printf "even 1000 = %b, odd 7 = %b\n" (even 1000) (odd 7)

let rec loop i acc = if i = 0 then acc else loop (i - 1) (acc + i)        (* 尾遞迴: 不會爆堆疊 *)
let () = Printf.printf "loop 1,000,000 = %d\n" (loop 1000000 0)
let rec depth n = if n = 0 then 0 else 1 + depth (n - 1)                  (* 非尾遞迴 *)
let () = Printf.printf "depth 50,000 = %d\n" (depth 50000)

let sum_to n =
  let rec go i acc = if i > n then acc else go (i + 1) (acc + i) in
  go 1 0
let () = Printf.printf "sum_to 100 = %d\n" (sum_to 100)

(* ── 排序 ── *)
let rec qsort = function
  | [] -> []
  | p :: rest ->
    let smaller = List.filter (fun x -> x < p) rest in
    let larger = List.filter (fun x -> x >= p) rest in
    qsort smaller @ [p] @ qsort larger
let data = [5; 3; 9; 1; 5; 8; 2; 7]
let () = print_endline (show_list (qsort data))
let () = print_endline (show_list (List.sort compare data))
let () = print_endline (show_list (List.sort (fun a b -> compare b a) data))

(* ── 質數篩 ── *)
let rec sieve = function
  | [] -> []
  | p :: xs -> p :: sieve (List.filter (fun x -> x mod p <> 0) xs)
let () = print_endline (show_list (sieve (List.init 49 (fun i -> i + 2))))

(* ── 命令式風格: while / for / ref ── *)
let collatz n =
  let steps = ref 0 and cur = ref n in
  while !cur <> 1 do
    cur := (if !cur mod 2 = 0 then !cur / 2 else 3 * !cur + 1);
    incr steps
  done;
  !steps
let () = Printf.printf "collatz 27 = %d steps\n" (collatz 27)

let sum_squares n =
  let total = ref 0 in
  for i = 1 to n do total := !total + i * i done;
  !total
let () = Printf.printf "sum of squares 1..10 = %d\n" (sum_squares 10)
let () = for i = 3 downto 1 do Printf.printf "%d..." i done; print_endline "liftoff!"

(* ── 型別推論的多型: 同一個函式用在不同型別 ── *)
let pair_up a b = (a, b)
let rec zip a b = match a, b with
  | x :: xs, y :: ys -> (x, y) :: zip xs ys
  | _ -> []
let () = List.iter (fun (n, s) -> Printf.printf "%d=%s " n s) (zip [1; 2; 3] ["one"; "two"; "three"])
let () = print_newline ()
