(* 05_monads.ml : Monad —— 用 let* / let+ / and+ (binding operators) 寫 monadic 程式
   OCaml 沒有 higher-kinded 型別，所以每個 monad 各自定義 return 與 ( let* )。
   (泛用的 map_m 需要 functor，本編譯器尚未支援 module，因此每個 monad 各寫一份) *)

(* ── 1. Option monad: 任何一步失敗就整個失敗 ── *)
let ( let* ) = Option.bind
let ( let+ ) o f = Option.map f o
let ( and+ ) a b = match a, b with Some x, Some y -> Some (x, y) | _ -> None

let safe_div a b = if b = 0 then None else Some (a / b)
let compute a b c =
  let* x = safe_div a b in
  let* y = safe_div x c in
  Some (x + y)
let add_opt a b = let+ x = a and+ y = b in x + y
let show_opt o = match o with Some n -> string_of_int n | None -> "None"
let () = Printf.printf "compute 100 5 2 = %s, compute 1 0 2 = %s, add = %s/%s\n"
    (show_opt (compute 100 5 2)) (show_opt (compute 1 0 2))
    (show_opt (add_opt (Some 3) (Some 4))) (show_opt (add_opt (Some 3) None))

(* ── 2. Result monad: 失敗時帶著錯誤訊息 (取代 exception) ── *)
let ( let* ) = Result.bind

let parse_positive n = if n > 0 then Ok n else Error ("not positive: " ^ string_of_int n)
let check_even n = if n mod 2 = 0 then Ok n else Error ("not even: " ^ string_of_int n)
let process n =
  let* p = parse_positive n in
  let* e = check_even p in
  Ok (e / 2)
let show_res r = match r with Ok n -> "Ok " ^ string_of_int n | Error m -> "Error (" ^ m ^ ")"
let () = List.iter (fun n -> Printf.printf "process %d -> %s\n" n (show_res (process n))) [10; 7; -4]

(* ── 3. List monad: 非決定性 (所有可能的組合) ── *)
let ( let* ) m f = List.concat_map f m
let return x = [x]
let guard b = if b then [()] else []
let range a b = List.init (b - a + 1) (fun i -> i + a)

let triples n =
  let* a = range 1 n in
  let* b = range a n in
  let* c = range b n in
  let* () = guard (a * a + b * b = c * c) in
  return (a, b, c)
let () = List.iter (fun (a, b, c) -> Printf.printf "(%d,%d,%d) " a b c) (triples 20)
let () = print_newline ()

(* ── 4. State monad: 狀態用函式傳遞 ── *)
let return x = fun s -> (x, s)
let ( let* ) m f = fun s -> let (a, s') = m s in f a s'
let get = fun s -> (s, s)
let put s' = fun _ -> ((), s')
let modify f = fun s -> ((), f s)

let fresh_label =
  let* n = get in
  let* () = put (n + 1) in
  return ("L" ^ string_of_int n)

let rec map_m f l = match l with
  | [] -> return []
  | x :: xs ->
    let* y = f x in
    let* ys = map_m f xs in
    return (y :: ys)

let label_all items = map_m (fun x -> let* l = fresh_label in return (l ^ ":" ^ x)) items
let (labeled, next) = label_all ["a"; "b"; "c"] 0
let () = Printf.printf "%s (next label = %d)\n" (String.concat " " labeled) next

let rec sum_to n = if n = 0 then return () else let* () = modify (fun s -> s + n) in sum_to (n - 1)
let ((), total) = sum_to 100000 0                      (* 十萬次 bind，堆疊不會增長 *)
let () = Printf.printf "sum_to 100000 = %d\n" total

(* ── 5. Writer monad: 邊計算邊記錄日誌 ── *)
let return x = (x, [])
let ( let* ) (a, w) f = let (b, w') = f a in (b, w @ w')
let tell msg = ((), [msg])

let rec fact n =
  if n <= 1 then
    let* () = tell "fact 1 = 1" in return 1
  else
    let* r = fact (n - 1) in
    let v = n * r in
    let* () = tell (Printf.sprintf "fact %d = %d" n v) in
    return v
let (value, log) = fact 5
let () = Printf.printf "%d\n" value
let () = List.iter print_endline log

(* ── 6. Parser monad: 用 record 包裝 parser，組合出遞迴下降的運算式解析器 ── *)
type tok = Num of int | Plus | Times | LParen | RParen
type 'a parser = { run : tok list -> ('a * tok list) option }

let return x = { run = fun ts -> Some (x, ts) }
let ( let* ) p f = { run = fun ts -> match p.run ts with None -> None | Some (a, rest) -> (f a).run rest }
let ( <|> ) p q = { run = fun ts -> match p.run ts with Some r -> Some r | None -> q.run ts }
let token t = { run = fun ts -> match ts with x :: rest when x = t -> Some ((), rest) | _ -> None }
let number = { run = fun ts -> match ts with Num n :: rest -> Some (n, rest) | _ -> None }

(* expr := term ('+' term)*      term := factor ('*' factor)*      factor := number | '(' expr ')' *)
let rec expr = { run = fun ts ->
    (let* t = term in
     let rec loop acc = (let* () = token Plus in let* t2 = term in loop (acc + t2)) <|> return acc in
     loop t).run ts }
and term = { run = fun ts ->
    (let* f = factor in
     let rec loop acc = (let* () = token Times in let* f2 = factor in loop (acc * f2)) <|> return acc in
     loop f).run ts }
and factor = { run = fun ts ->
    (number <|> (let* () = token LParen in let* e = expr in let* () = token RParen in return e)).run ts }

let parse ts = match expr.run ts with Some (v, []) -> Some v | _ -> None
let () =
  List.iter (fun ts -> print_endline (show_opt (parse ts)))
    [ [Num 2; Plus; Num 3; Times; Num 4];                                   (* 2 + 3 * 4 = 14 *)
      [LParen; Num 2; Plus; Num 3; RParen; Times; Num 4];                   (* (2 + 3) * 4 = 20 *)
      [Num 1; Plus];                                                        (* 解析失敗 *)
      [Num 2; Times; LParen; Num 1; Plus; Num 1; RParen; Times; Num 5] ]    (* 2 * (1 + 1) * 5 = 20 *)
