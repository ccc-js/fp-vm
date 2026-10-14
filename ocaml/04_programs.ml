(* 04_programs.ml : 完整的小程式 —— RPN 計算機、N 皇后、佇列 + 廣度優先搜尋、Result 串接 *)

(* ── 1. RPN (逆波蘭) 計算機: 用 variant 表示 token，result 表示成功或錯誤 ── *)
type token = Int of int | Plus | Minus | Times | Divide

let eval_rpn tokens =
  let rec go stack tokens = match stack, tokens with
    | [x], [] -> Ok x
    | _, [] -> Error "malformed expression"
    | _, Int n :: rest -> go (n :: stack) rest
    | y :: x :: stack', op :: rest ->
      (match op with
       | Plus -> go ((x + y) :: stack') rest
       | Minus -> go ((x - y) :: stack') rest
       | Times -> go ((x * y) :: stack') rest
       | Divide -> if y = 0 then Error "division by zero" else go ((x / y) :: stack') rest
       | Int _ -> Error "unreachable")
    | _, _ :: _ -> Error "stack underflow" in
  go [] tokens

let show_result r = match r with
  | Ok n -> "= " ^ string_of_int n
  | Error msg -> "error: " ^ msg
let () =
  List.iter (fun toks -> print_endline (show_result (eval_rpn toks)))
    [ [Int 3; Int 4; Plus; Int 2; Times];          (* (3 + 4) * 2 *)
      [Int 10; Int 2; Divide; Int 3; Minus];       (* 10 / 2 - 3 *)
      [Int 1; Int 0; Divide];
      [Int 1; Plus];
      [Int 1; Int 2] ]

(* ── 2. N 皇后問題: 計算解的個數 ── *)
let rec range a b = if a > b then [] else a :: range (a + 1) b
let safe q qs =
  let rec ok d l = match l with
    | [] -> true
    | x :: xs -> x <> q && x <> q + d && x <> q - d && ok (d + 1) xs in
  ok 1 qs
let rec place n k qs =
  if k = 0 then 1
  else List.fold_left (fun acc q -> if safe q qs then acc + place n (k - 1) (q :: qs) else acc) 0 (range 1 n)
let () = List.iter (fun n -> Printf.printf "queens %d = %d\n" n (place n n [])) [4; 5; 6; 7]

(* ── 3. 佇列 (兩個 list) 與廣度優先搜尋 ── *)
type 'a queue = { front : 'a list; back : 'a list }
let empty = { front = []; back = [] }
let push x q = { q with back = x :: q.back }
let pop q = match q.front with
  | x :: rest -> Some (x, { q with front = rest })
  | [] ->
    (match List.rev q.back with
     | [] -> None
     | x :: rest -> Some (x, { front = rest; back = [] }))

let graph = [(1, [2; 3]); (2, [4]); (3, [4; 5]); (4, [6]); (5, [6]); (6, [])]
let neighbors n = match List.assoc_opt n graph with Some l -> l | None -> []

let bfs start goal =
  let rec loop q visited =
    match pop q with
    | None -> None
    | Some ((node, dist), q') ->
      if node = goal then Some dist
      else
        let fresh = List.filter (fun n -> not (List.mem n visited)) (neighbors node) in
        let q'' = List.fold_left (fun acc n -> push (n, dist + 1) acc) q' fresh in
        loop q'' (visited @ fresh) in
  loop (push (start, 0) empty) [start]
let () =
  List.iter (fun (a, b) ->
      match bfs a b with
      | Some d -> Printf.printf "shortest path %d -> %d: %d steps\n" a b d
      | None -> Printf.printf "no path from %d to %d\n" a b)
    [(1, 6); (1, 5); (3, 6); (6, 1)]

(* ── 4. 帳戶: record + result 的串接 (>>= 是自訂的 bind 運算子) ── *)
type account = { owner : string; balance : int }

let ( >>= ) r f = match r with Ok x -> f x | Error e -> Error e
let deposit amt acc = Ok { acc with balance = acc.balance + amt }
let withdraw amt acc =
  if amt > acc.balance
  then Error (Printf.sprintf "%s: insufficient funds (balance %d, requested %d)" acc.owner acc.balance amt)
  else Ok { acc with balance = acc.balance - amt }

let report r = match r with
  | Ok a -> Printf.printf "%s now has %d\n" a.owner a.balance
  | Error e -> print_endline e
let start = Ok { owner = "Ada"; balance = 100 }
let () = report (start >>= deposit 50 >>= withdraw 30)
let () = report (start >>= deposit 50 >>= withdraw 30 >>= withdraw 500)

(* ── 5. 矩陣 (list of list) ── *)
let rec transpose m = match m with
  | [] | [] :: _ -> []
  | rows -> List.map List.hd rows :: transpose (List.map List.tl rows)
let dot a b = List.fold_left (+) 0 (List.map2 (fun x y -> x * y) a b)
let mat_mul a b = let bt = transpose b in List.map (fun row -> List.map (fun col -> dot row col) bt) a
let show_row r = String.concat " " (List.map (Printf.sprintf "%3d") r)
let () = List.iter (fun r -> print_endline (show_row r)) (mat_mul [[1; 2]; [3; 4]; [5; 6]] [[7; 8; 9]; [10; 11; 12]])
