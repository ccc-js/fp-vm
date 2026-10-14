(* 01_basics.ml : 基礎 —— 值、函式、遞迴、浮點、tuple、list、字串、Printf、柯里化
   執行:  node mlc.js ml/01_basics.ml && node lispvm.js ml/01_basics.lbc
   查看型別:  node mlc.js ml/01_basics.ml --types *)

let pi = 3.14159
let greeting = "Hello, ML!"
let () = print_endline greeting

(* 函式: 型別是自動推論出來的 *)
let square x = x * x
let hypot2 a b = square a + square b
let () = Printf.printf "hypot2 3 4 = %d\n" (hypot2 3 4)

(* 遞迴 *)
let rec fact n = if n <= 1 then 1 else n * fact (n - 1)
let rec fib n = if n < 2 then n else fib (n - 1) + fib (n - 2)
let () = Printf.printf "fact 10 = %d, fib 20 = %d\n" (fact 10) (fib 20)

(* 浮點數使用另一組運算子 (+. -. *. /.)，int 與 float 不會混用 *)
let circle_area r = pi *. r *. r
let () = Printf.printf "area(2.0) = %.2f\n" (circle_area 2.0)
let () = print_endline (string_of_float (float_of_int 7 /. 2.0))

(* tuple 與樣式解構 *)
let swap (a, b) = (b, a)
let (x, y) = swap (1, "one")
let () = Printf.printf "%s %d\n" x y

(* list *)
let nums = [1; 2; 3; 4; 5]
let rec sum l = match l with [] -> 0 | h :: rest -> h + sum rest
let () = Printf.printf "length=%d sum=%d sum'=%d\n" (List.length nums) (sum nums) (List.fold_left (+) 0 nums)
let doubled = List.map (fun x -> x * 2) nums
let evens = List.filter (fun x -> x mod 2 = 0) nums
let show_list l = "[" ^ String.concat "; " (List.map string_of_int l) ^ "]"
let () = print_endline (show_list doubled ^ " " ^ show_list evens ^ " " ^ show_list (List.rev nums))
let () = print_endline (show_list (1 :: 2 :: [3] @ [4; 5]))

(* 字串 *)
let () = print_endline ("con" ^ "cat" ^ "enation")
let () = Printf.printf "%s has %d chars\n" greeting (String.length greeting)

(* 條件 *)
let describe n = if n < 0 then "negative" else if n = 0 then "zero" else "positive"
let () = List.iter (fun n -> Printf.printf "%d is %s\n" n (describe n)) [-5; 0; 5]

(* let ... in 區域綁定 *)
let ring_area r1 r2 =
  let outer = circle_area r2 in
  let inner = circle_area r1 in
  outer -. inner
let () = Printf.printf "ring = %.3f\n" (ring_area 1.0 2.0)

(* 柯里化與部分套用: 函式只接受一個參數，多參數其實是回傳函式 *)
let add a b = a + b
let add10 = add 10
let () = Printf.printf "%d %d\n" (add10 5) (List.fold_left add 0 [1; 2; 3])

(* 多型: id 的型別是 'a -> 'a，可用於任何型別 *)
let id x = x
let () = Printf.printf "%d %s %b\n" (id 42) (id "poly") (id true)

(* Printf 格式化 *)
let () = Printf.printf "|%5d|%-5d|%05d|%8.3f|%-6s|%6s|\n" 42 42 42 3.14159 "ab" "cd"
let () = print_endline (Printf.sprintf "%d%%" 95)
