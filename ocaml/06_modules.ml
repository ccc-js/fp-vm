(* 06_modules.ml : module、簽章、抽象型別、functor —— 含「泛用的 monad 工具」
   functor 的實作方式: 每次套用時展開並重新型別檢查 (見 mlc.js 檔頭)。 *)

(* ── 1. 簽章與抽象型別: 外部看不到 Stack 的內部表示 ── *)
module type STACK = sig
  type 'a t
  val empty : 'a t
  val push : 'a -> 'a t -> 'a t
  val pop : 'a t -> ('a * 'a t) option
  val size : 'a t -> int
end

module ListStack : STACK = struct
  type 'a t = 'a list
  let empty = []
  let push x s = x :: s
  let pop s = match s with [] -> None | x :: rest -> Some (x, rest)
  let size s = List.length s
  let internal_only = 42                       (* 沒列在簽章中: 外部無法使用 *)
end

let s = ListStack.(push 3 (push 2 (push 1 empty)))          (* M.(expr): 局部 open *)
let () = match ListStack.pop s with
  | Some (top, rest) -> Printf.printf "top=%d size=%d rest=%d\n" top (ListStack.size s) (ListStack.size rest)
  | None -> print_endline "empty"
(* 若寫 ListStack.size [1; 2; 3]，型別檢查會擋下來: ListStack.t 是抽象型別，不等於 list *)

(* ── 2. Functor: 對任何「有順序的型別」產生 Set 與 Map ── *)
module type ORDERED = sig
  type t
  val compare : t -> t -> int
end

module IntOrd = struct
  type t = int
  let compare a b = if a < b then -1 else if a = b then 0 else 1
end

module MakeSet (Ord : ORDERED) : sig
  type elt = Ord.t
  type t
  val empty : t
  val add : elt -> t -> t
  val mem : elt -> t -> bool
  val to_list : t -> elt list
  val size : t -> int
end = struct
  type elt = Ord.t
  type t = elt list                            (* 排序且無重複的 list *)
  let empty = []
  let rec add x s = match s with
    | [] -> [x]
    | y :: rest ->
      let c = Ord.compare x y in
      if c = 0 then s else if c < 0 then x :: s else y :: add x rest
  let rec mem x s = match s with
    | [] -> false
    | y :: rest -> let c = Ord.compare x y in c = 0 || (c > 0 && mem x rest)
  let to_list s = s
  let size s = List.length s
end

module IntSet = MakeSet (IntOrd)
module FloatSet = MakeSet (struct type t = float let compare = compare end)     (* 匿名 module 當引數 *)

let show_ints l = "{" ^ String.concat ", " (List.map string_of_int l) ^ "}"
let nums = List.fold_left (fun s x -> IntSet.add x s) IntSet.empty [5; 3; 8; 3; 1; 5]
let () = Printf.printf "IntSet = %s size=%d mem 8=%b mem 7=%b\n"
    (show_ints (IntSet.to_list nums)) (IntSet.size nums) (IntSet.mem 8 nums) (IntSet.mem 7 nums)
let fs = List.fold_left (fun s x -> FloatSet.add x s) FloatSet.empty [2.5; 1.5; 2.5]
let () = print_endline ("FloatSet = " ^ String.concat ", " (List.map string_of_float (FloatSet.to_list fs)))

module MakeMap (Ord : ORDERED) = struct
  type key = Ord.t
  type 'a t = (key * 'a) list
  let empty = []
  let rec add k v m = match m with
    | [] -> [(k, v)]
    | (k', v') :: rest ->
      let c = Ord.compare k k' in
      if c = 0 then (k, v) :: rest else if c < 0 then (k, v) :: m else (k', v') :: add k v rest
  let rec find_opt k m = match m with
    | [] -> None
    | (k', v) :: rest -> let c = Ord.compare k k' in if c = 0 then Some v else if c < 0 then None else find_opt k rest
  let bindings m = m
end
module IntMap = MakeMap (IntOrd)
let squares = List.fold_left (fun m n -> IntMap.add n (n * n) m) IntMap.empty [4; 2; 7; 1]
let () = List.iter (fun (k, v) -> Printf.printf "%d->%d " k v) (IntMap.bindings squares)
let () = Printf.printf "| find 4 = %s, find 5 = %s\n"
    (match IntMap.find_opt 4 squares with Some v -> string_of_int v | None -> "none")
    (match IntMap.find_opt 5 squares with Some v -> string_of_int v | None -> "none")

(* ── 3. 泛用的 monad 工具: 一份程式碼，套用到任何 monad ── *)
module type MONAD = sig
  type 'a t
  val return : 'a -> 'a t
  val bind : 'a t -> ('a -> 'b t) -> 'b t
end

module MonadUtils (M : MONAD) = struct
  let ( let* ) = M.bind
  let map f m = let* x = m in M.return (f x)
  let rec map_m f l = match l with
    | [] -> M.return []
    | x :: xs -> let* y = f x in let* ys = map_m f xs in M.return (y :: ys)
  let sequence l = map_m (fun m -> m) l
  let rec fold_m f acc l = match l with
    | [] -> M.return acc
    | x :: xs -> let* acc' = f acc x in fold_m f acc' xs
end

module OptionMonad = struct
  type 'a t = 'a option
  let return x = Some x
  let bind m f = match m with None -> None | Some x -> f x
end
module ListMonad = struct
  type 'a t = 'a list
  let return x = [x]
  let bind m f = List.concat_map f m
end
module StateMonad = struct
  type 'a t = int -> 'a * int                       (* 狀態是 int *)
  let return x = fun s -> (x, s)
  let bind m f = fun s -> let (a, s') = m s in f a s'
  let get = fun s -> (s, s)
  let put s' = fun _ -> ((), s')
end

module OptU = MonadUtils (OptionMonad)
module ListU = MonadUtils (ListMonad)
module StateU = MonadUtils (StateMonad)

let half n = if n mod 2 = 0 then Some (n / 2) else None
let show_opt l = match l with Some l -> show_ints l | None -> "None"
let () = Printf.printf "Option: map_m half [2;4;6] = %s, [2;3] = %s, sequence = %s\n"
    (show_opt (OptU.map_m half [2; 4; 6])) (show_opt (OptU.map_m half [2; 3])) (show_opt (OptU.sequence [Some 1; Some 2]))

let () = print_string "List:   map_m (fun x -> [x; x*10]) [1; 2] = "
let () = List.iter (fun l -> print_string (show_ints l ^ " ")) (ListU.map_m (fun x -> [x; x * 10]) [1; 2])
let () = print_newline ()

let label x = StateU.(let* n = StateMonad.get in let* () = StateMonad.put (n + 1) in StateMonad.return (n, x))
let (labeled, next) = StateU.map_m label ["a"; "b"; "c"] 10
let () = Printf.printf "State:  %s next=%d\n"
    (String.concat " " (List.map (fun (n, x) -> string_of_int n ^ x) labeled)) next
let (total, _) = StateU.fold_m (fun acc x -> StateMonad.return (acc + x)) 0 [1; 2; 3; 4] 0
let () = Printf.printf "State:  fold_m sum = %d\n" total

(* ── 4. 巢狀 module、open、include、各自獨立狀態的 functor ── *)
module Geometry = struct
  type point = { x : float; y : float }
  module Vec = struct
    let add p q = { x = p.x +. q.x; y = p.y +. q.y }
    let scale k p = { x = k *. p.x; y = k *. p.y }
    let norm2 p = p.x *. p.x +. p.y *. p.y
  end
  let origin = { x = 0.0; y = 0.0 }
end
open Geometry
let p = Vec.add { x = 1.0; y = 2.0 } (Vec.scale 2.0 { x = 1.0; y = 1.0 })
let () = Printf.printf "p = (%.1f, %.1f)  |p|^2 = %.1f\n" p.x p.y (Vec.norm2 p)

module ListPlus = struct
  include List                                      (* 把 List 的所有成員帶進來再擴充 *)
  let sum l = fold_left (+) 0 l
  let average l = float (sum l) /. float (length l)
end
let () = Printf.printf "ListPlus: sum=%d average=%.2f squares=%s\n"
    (ListPlus.sum [1; 2; 3; 4]) (ListPlus.average [1; 2; 3; 4]) (show_ints (ListPlus.map (fun x -> x * x) [1; 2; 3]))

module MakeCounter () = struct                      (* 每次套用都產生獨立的狀態 *)
  let count = ref 0
  let next () = incr count; !count
end
module C1 = MakeCounter ()
module C2 = MakeCounter ()
let () = ignore (C1.next ()); ignore (C1.next ())
let () = Printf.printf "counters: C1=%d C2=%d\n" (C1.next ()) (C2.next ())
