(* 07_p0.ml : P0 新功能示範 —— char、array、bytes、mutable record、位運算、
   浮點數學、字串比較、Printf %c/%x/%X/%o、Hashtbl、Seq、or-pattern 綁定 *)

(* ── 1. char ── *)
let () = print_endline (string_of_char 'A' ^ string_of_char '\n' ^ string_of_char '\x42')
let () = Printf.printf "A=%d newline=%d\n" (Char.code 'A') (Char.code '\n')
let () = Printf.printf "%c%c%c\n" 'x' 'y' 'z'
let up s = String.init (String.length s) (fun i -> Char.uppercase_ascii (String.get s i))
let () = print_endline (up "hello, ocaml!")

(* ── 2. array ── *)
let a = [|1; 2; 3; 4|]
let () = Printf.printf "len=%d a0=%d\n" (Array.length a) a.(0)
let () = a.(1) <- 99
let squares = Array.init 5 (fun i -> i * i)
let () = Array.iter (fun x -> Printf.printf "%d " x) squares; print_newline ()
let doubled = Array.map (fun x -> x * 2) squares
let () = Printf.printf "sum=%d\n" (Array.fold_left (+) 0 doubled)
let l = Array.to_list doubled
let back = Array.of_list l
let () = Printf.printf "roundtrip=%b\n" (back = doubled)
let empty_arr : int array = [||]
let () = Printf.printf "empty len=%d\n" (Array.length empty_arr)

(* ── 3. bytes ── *)
let b = Bytes.of_string "hello"
let () = Bytes.set b 0 'H'
let () = print_endline (Bytes.to_string b)
let bb = Bytes.make 4 'a'
let () = Bytes.fill bb 1 2 'b'
let () = print_endline (Bytes.to_string bb)
let () = Printf.printf "bytes len=%d get=%c\n" (Bytes.length b) (Bytes.get b 1)

(* ── 4. mutable record ── *)
type counter = { mutable n : int; name : string }
let c = { n = 0; name = "hits" }
let () = c.n <- c.n + 1; c.n <- c.n + 1
let () = Printf.printf "%s=%d\n" c.name c.n

(* ── 5. 位運算 ── *)
let () = Printf.printf "land=%d lor=%d lxor=%d\n" (12 land 10) (12 lor 10) (12 lxor 10)
let () = Printf.printf "lsl=%d asr=%d lsr=%d\n" (1 lsl 10) (-16 asr 2) (-16 lsr 2)
let has_flag flags mask = flags land mask <> 0
let () = Printf.printf "flag=%b %b\n" (has_flag 6 4) (has_flag 6 1)

(* ── 6. 浮點數學 ── *)
let () = Printf.printf "sqrt=%.3f sin=%.3f cos=%.3f\n" (sqrt 2.0) (sin Float.pi) (cos 0.0)
let () = Printf.printf "pow=%.1f exp=%.3f log=%.3f\n" (2.0 ** 10.0) (exp 1.0) (log Float.e)
let () = Printf.printf "atan2=%.3f mod_float=%.1f\n" (atan2 1.0 1.0) (mod_float 5.5 2.0)

(* ── 7. 字串比較與結構 compare ── *)
let () = Printf.printf "cmp=%b %b %d\n" ("abc" < "abd") ("b" > "a") (compare [1; 2] [1; 3])
let words = ["pear"; "apple"; "fig"; "banana"]
let () = List.iter (fun w -> print_endline w) (List.sort compare words)

(* ── 8. Printf %x %X %o ── *)
let () = Printf.printf "hex=%x HEX=%X oct=%o\n" 255 255 8
let () = Printf.printf "%05d|%-6s|%04x|\n" 42 "ab" 27

(* ── 9. Hashtbl ── *)
let h = Hashtbl.create 8
let () = Hashtbl.add h "apple" 5; Hashtbl.add h "banana" 3
let () = Printf.printf "apple=%d mem=%b len=%d hash=%d\n"
    (match Hashtbl.find_opt h "apple" with Some v -> v | None -> -1)
    (Hashtbl.mem h "cherry") (Hashtbl.length h) (Hashtbl.hash "apple" mod 1000)
let () = Hashtbl.replace h "apple" 6
let () = Printf.printf "apple now=%d\n"
    (match Hashtbl.find_opt h "apple" with Some v -> v | None -> -1)

(* ── 10. Seq ── *)
let first5 = Seq.to_list (Seq.take 5 (Seq.map (fun x -> x * x) (Seq.ints 1)))
let () = List.iter (fun x -> Printf.printf "%d " x) first5; print_newline ()
let fibs = Seq.unfold (fun (x, y) -> Some (x, (y, x + y))) (0, 1)
let () = List.iter (fun x -> Printf.printf "%d " x) (Seq.to_list (Seq.take 8 fibs)); print_newline ()

(* ── 11. or-pattern 綁定與 String 工具 ── *)
type shape = Circle of int | Square of int | Point
let area = function Circle r | Square r -> r * r | Point -> 0
let () = Printf.printf "area=%d %d %d\n" (area (Circle 3)) (area (Square 4)) (area Point)
let f = function Some x | Some x -> x | None -> 0
let () = Printf.printf "opt=%d %d\n" (f (Some 5)) (f None)
let parts = String.split_on_char ',' "a,b,c"
let () = print_endline (String.concat ";" parts)
let () = Printf.printf "starts=%b ends=%b contains=%b\n"
    (String.starts_with "https://" "https://ocaml.org")
    (String.ends_with ".ml" "hello.ml")
    (String.contains "hello" 'e')
let found = List.find_map (fun s -> let n = int_of_string_opt s in match n with Some _ -> n | None -> None) ["x"; "42"; "y"]
let () = Printf.printf "find_map=%s rev_map=%s\n"
    (match found with Some n -> string_of_int n | None -> "none")
    (String.concat "," (List.map string_of_int (List.rev_map (fun x -> x + 1) [1; 2; 3])))
