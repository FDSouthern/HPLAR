(* ========================================================================= *)
(* Term orderings.                                                           *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

let rec termsize tm =
  match tm with
    Var x -> 1
  | Fn(f,args) -> itlist (fun t n -> termsize t + n) args 1;;

(* ------------------------------------------------------------------------- *)
(* This fails the rewrite properties.                                        *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let s = <<|f(x,x,x)|>> and t = <<|g(x,y)|>>;;

termsize s > termsize t;;

let i = ("y" := <<|f(x,x,x)|>>);;

termsize (termsubst i s) > termsize (termsubst i t);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* However we can do better with the following.                              *)
(* ------------------------------------------------------------------------- *)

let rec occurrences x tm =
  match tm with
    Var y -> if x = y then 1 else 0
  | Fn(f,args) -> itlist (fun t n -> occurrences x t + n) args 0;;

(* ------------------------------------------------------------------------- *)
(* Lexicographic path order.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec lexord ord l1 l2 =
  match (l1,l2) with
    (h1::t1,h2::t2) -> if ord h1 h2 then length t1 = length t2
                       else h1 = h2 & lexord ord t1 t2
  | _ -> false;;

let rec lpo_gt w s t =
  match (s,t) with
    (_,Var x) ->
        not(s = t) & mem x (fvt s)
  | (Fn(f,fargs),Fn(g,gargs)) ->
        exists (fun si -> lpo_ge w si t) fargs or
        forall (lpo_gt w s) gargs &
        (f = g & lexord (lpo_gt w) fargs gargs or
         w (f,length fargs) (g,length gargs))
  | _ -> false

and lpo_ge w s t = (s = t) or lpo_gt w s t;;

(* ------------------------------------------------------------------------- *)
(* More convenient way of specifying weightings.                             *)
(* ------------------------------------------------------------------------- *)

let weight lis (f,n) (g,m) =
  let i = index f lis and j = index g lis in
  i > j or i = j & n > m;;
