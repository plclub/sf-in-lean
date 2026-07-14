open Norm

let rec ty2s tt = match tt with
  TBool -> "Bool"
| TArrow (tt1,tt2) -> "(" ^ ty2s tt1 ^ "->" ^ ty2s tt2 ^ ")" 
| TProd (tt1,tt2) -> "(" ^ ty2s tt1 ^ "*" ^ ty2s tt2 ^ ")" ;;

let rec tm2s t = match t with
| Tvar y -> string_of_int y
| Tapp (t1, t2) -> "(" ^ tm2s t1 ^ " " ^ tm2s t2 ^ ")" 
| Tabs (y, t0, t1) -> "(\\" ^ string_of_int y ^ ":" ^ ty2s t0 ^ ". " ^ tm2s t1 ^ ")"
| Tpair (t1, t2) -> "(" ^ tm2s t1 ^ "," ^ tm2s t2 ^ ")" 
| Tfst t1 -> "fst " ^ tm2s t1
| Tsnd t1 -> "snd " ^ tm2s t1
| Tfalse -> "false"
| Ttrue -> "true"
| Tif (t0, t1, t2) -> "(if" ^ tm2s t0 ^ " then " ^ tm2s t1 ^ " else " ^ tm2s t2 ^ ")" 


(* ---------------------------------------------------------------- *)

let x = 0;;

let witness e = match e with Ex_intro (x,y) -> x;;

let tm_from (x:tm) = x;;

let test t =
  print_endline ("Checking " ^ (tm2s t) ^ "...");
  match type_check empty t with
    None -> print_endline "No type"
  | Some tt ->
      print_endline ("Type: " ^ ty2s tt);
      let d = type_checking_sound empty t tt in
      let res = tm_from (witness (normalization t tt d)) in
      print_endline ("Result: " ^ tm2s res);
      print_newline ();;

test (Tapp (Tabs (x, TBool, Tvar x) , Ttrue));;
test (Tapp (Tabs (x, TBool, Tvar x) , Tfalse));;
