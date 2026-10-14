(* 02_adt.ml : 代數資料型別 (variant) 與模式匹配 —— ML 的招牌功能 *)

(* ── 1. 符號運算: 運算式、求值、微分、化簡 ── *)
type expr =
  | Num of int
  | Var of string
  | Add of expr * expr
  | Mul of expr * expr
  | Neg of expr

let rec to_string e = match e with
  | Num n -> string_of_int n
  | Var v -> v
  | Add (a, b) -> "(" ^ to_string a ^ " + " ^ to_string b ^ ")"
  | Mul (a, b) -> to_string a ^ " * " ^ to_string b
  | Neg a -> "-" ^ to_string a

let rec eval env e = match e with
  | Num n -> Some n
  | Var v -> List.assoc_opt v env
  | Add (a, b) ->
    (match eval env a, eval env b with Some x, Some y -> Some (x + y) | _ -> None)
  | Mul (a, b) ->
    (match eval env a, eval env b with Some x, Some y -> Some (x * y) | _ -> None)
  | Neg a -> (match eval env a with Some x -> Some (-x) | None -> None)

let rec deriv x e = match e with
  | Num _ -> Num 0
  | Var v -> if v = x then Num 1 else Num 0
  | Add (a, b) -> Add (deriv x a, deriv x b)
  | Mul (a, b) -> Add (Mul (deriv x a, b), Mul (a, deriv x b))
  | Neg a -> Neg (deriv x a)

let rec simplify e = match e with
  | Add (a, b) ->
    (match simplify a, simplify b with
     | Num 0, e2 -> e2
     | e1, Num 0 -> e1
     | Num x, Num y -> Num (x + y)
     | e1, e2 -> Add (e1, e2))
  | Mul (a, b) ->
    (match simplify a, simplify b with
     | Num 0, _ -> Num 0
     | _, Num 0 -> Num 0
     | Num 1, e2 -> e2
     | e1, Num 1 -> e1
     | Num x, Num y -> Num (x * y)
     | e1, e2 -> Mul (e1, e2))
  | Neg a -> (match simplify a with Num n -> Num (-n) | e1 -> Neg e1)
  | _ -> e

let f = Add (Mul (Var "x", Var "x"), Mul (Num 3, Var "x"))         (* x*x + 3*x *)
let df = simplify (deriv "x" f)
let () = Printf.printf "f(x)   = %s\n" (to_string f)
let () = Printf.printf "f'(x)  = %s\n" (to_string df)
let show_opt o = match o with Some n -> string_of_int n | None -> "unbound variable"
let () = Printf.printf "f(5)=%s  f'(5)=%s  f(y)=%s\n"
    (show_opt (eval [("x", 5)] f)) (show_opt (eval [("x", 5)] df)) (show_opt (eval [("x", 5)] (Var "y")))

(* ── 2. 多型二元搜尋樹 ── *)
type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree

let rec insert x t = match t with
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (l, v, r) ->
    if x < v then Node (insert x l, v, r)
    else if x > v then Node (l, v, insert x r)
    else t

let rec contains x t = match t with
  | Leaf -> false
  | Node (l, v, r) -> x = v || (if x < v then contains x l else contains x r)
let rec size t = match t with Leaf -> 0 | Node (l, _, r) -> size l + 1 + size r
let rec height t = match t with Leaf -> 0 | Node (l, _, r) -> 1 + max (height l) (height r)
let rec inorder t = match t with Leaf -> [] | Node (l, v, r) -> inorder l @ [v] @ inorder r
let rec map_tree f t = match t with
  | Leaf -> Leaf
  | Node (l, v, r) -> Node (map_tree f l, f v, map_tree f r)
let of_list l = List.fold_left (fun t x -> insert x t) Leaf l

let show_list l = "[" ^ String.concat "; " (List.map string_of_int l) ^ "]"
let t = of_list [5; 3; 8; 1; 4; 7; 9; 2; 6]
let () = Printf.printf "inorder=%s size=%d height=%d\n" (show_list (inorder t)) (size t) (height t)
let () = Printf.printf "contains 7: %b, contains 10: %b\n" (contains 7 t) (contains 10 t)
let () = print_endline (show_list (inorder (map_tree (fun x -> x * 10) t)))
let floats = of_list [2.5; 1.5; 3.5]                      (* 同一個 tree 型別，換成 float *)
let () = print_endline (String.concat ", " (List.map string_of_float (inorder (map_tree (fun x -> x *. 2.0) floats))))
let () = Printf.printf "floats: size=%d\n" (size floats)

(* ── 3. option 與 result: 用型別表達「可能失敗」 ── *)
let safe_div a b = if b = 0 then None else Some (a / b)
let () = match safe_div 10 2 with
  | Some q -> Printf.printf "10/2 = %d\n" q
  | None -> print_endline "division by zero"
let () = match safe_div 1 0 with
  | Some q -> Printf.printf "1/0 = %d\n" q
  | None -> print_endline "1/0 = undefined"
let () = print_int (Option.value (Option.map (fun x -> x + 1) (safe_div 9 3)) 0); print_newline ()

let parse_age n =
  if n < 0 then Error "negative"
  else if n > 150 then Error "too large"
  else Ok n
let show_age r = match r with
  | Ok n -> "age " ^ string_of_int n
  | Error msg -> "error: " ^ msg
let () = List.iter (fun n -> print_endline (show_age (parse_age n))) [30; -1; 200]

(* ── 4. record 與 variant 組合 ── *)
type point = { x : float; y : float }
type shape = Circle of point * float | Rect of point * point | Triangle of point * point * point

let origin = { x = 0.0; y = 0.0 }
let dist p q = sqrt ((p.x -. q.x) *. (p.x -. q.x) +. (p.y -. q.y) *. (p.y -. q.y))
let area s = match s with
  | Circle (_, r) -> 3.14159 *. r *. r
  | Rect (p, q) -> abs_float ((q.x -. p.x) *. (q.y -. p.y))
  | Triangle (a, b, c) -> abs_float ((a.x *. (b.y -. c.y) +. b.x *. (c.y -. a.y) +. c.x *. (a.y -. b.y)) /. 2.0)
let name s = match s with Circle _ -> "circle" | Rect _ -> "rect" | Triangle _ -> "triangle"
let shapes = [Circle (origin, 2.0); Rect (origin, { x = 3.0; y = 4.0 }); Triangle (origin, { x = 4.0; y = 0.0 }, { x = 0.0; y = 3.0 })]
let () = List.iter (fun s -> Printf.printf "%-8s area = %6.2f\n" (name s) (area s)) shapes
let () = Printf.printf "dist = %.2f\n" (dist origin { x = 3.0; y = 4.0 })
let moved = { origin with y = 2.5 }
let () = Printf.printf "moved = (%.1f, %.1f)\n" moved.x moved.y
