(* ========================================================================= *)
(* Rewriting.                                                                *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Matching of terms.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec tmatch (vtm,ctm) env =
  match (vtm,ctm) with
    (Var x,t) ->
        if not (defined env x) then (x |-> t) env
        else if apply env x = t then env else failwith "tmatch"
  | Fn(f,fargs),Fn(g,gargs) ->
        if f = g then itlist tmatch (zip fargs gargs) env
        else failwith "tmatch"
  | _ -> failwith "tmatch";;

let term_match vtm ctm = tmatch(vtm,ctm) undefined;;

(* ------------------------------------------------------------------------- *)
(* Rewriting with a single equation.                                         *)
(* ------------------------------------------------------------------------- *)

let rewrite1 eq t =
  match eq with
    Atom(R("=",[l;r])) -> termsubst (term_match l t) r
  | _ -> failwith "rewrite1";;

(* ------------------------------------------------------------------------- *)
(* Rewriting with first in a list of equations.                              *)
(* ------------------------------------------------------------------------- *)

let rewrite eqs tm = tryfind (fun eq -> rewrite1 eq tm) eqs;;

(* ------------------------------------------------------------------------- *)
(* Applying a term transformation at depth.                                  *)
(* ------------------------------------------------------------------------- *)

let rec depth fn tm =
  try depth fn (fn tm) with Failure _ ->
  match tm with
    Var x -> tm
  | Fn(f,args) -> let tm' = Fn(f,map (depth fn) args) in
                  if tm' = tm then tm' else depth fn tm';;

(* ------------------------------------------------------------------------- *)
(* Example: 3 * 2 + 4 in successor notation.                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let eqs =
 [<<0 + x = x>>; <<S(x) + y = S(x + y)>>; <<x + S(y) = S(x + y)>>;
  <<0 * x = 0>>; <<S(x) * y = y + x * y>>];;

depth (rewrite eqs) <<|S(S(S(0))) * S(S(0)) + S(S(S(S(0))))|>>;;

(* ------------------------------------------------------------------------- *)
(* Combinatory logic.                                                        *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<((S * f) * g) * x = (f * x) * (g * x)>>;
  <<(K * x) * y = x>>];;

depth (rewrite eqs) <<|((S * K) * K) * x|>>;;

(* ------------------------------------------------------------------------- *)
(* The 3x + 1 problem (Collatz conjecture).                                  *)
(* ------------------------------------------------------------------------- *)

let eqs =
  [<<1 = S(0)>>;
   <<2 = S(1)>>;
   <<3 = S(2)>>;
   <<0 + x = x>>;
   <<S(x) + y = S(x + y)>>;
   <<0 * y = 0>>;
   <<S(x) * y = y + x * y>>;
   <<run(S(S(x)),y) = run(x,S(y))>>;
   <<run(S(0),S(y)) = run(3 * (2 * y + 1) + 1,0)>>;
   <<run(0,S(y)) = run(S(y),0)>>;
   <<run(S(0),0) = one>>;
   <<run(0,0) = zero>>];;

(* ------------------------------------------------------------------------- *)
(* The calamitously inefficient example.                                     *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<S(x) + (y + z) = x + (S(S(y)) + z)>>;
  <<S(u) + (v + (w + x)) = u + (w + (v + x))>>];;

depth (rewrite eqs) <<|S(x) + (y + z)|>>;;

depth (rewrite eqs) <<|S(a) + b + c + d + e + f + g + h|>>;;

depth (rewrite eqs) <<|S(a) + b + c + d|>>;;

depth (rewrite eqs) <<|S(a) + b + c + d + e|>>;;

depth (rewrite eqs) <<|S(a) + b + c + d + e + f|>>;;

depth (rewrite eqs) <<|S(a) + S(b) + S(c) + S(d) + S(e) + S(f)|>>;;

let eqs =
 [<<S(u) + (v + (w + x)) = u + (w + (v + x))>>;
  <<S(x) + (y + z) = x + (S(S(y)) + z)>>];;

depth (rewrite eqs) <<|S(a) + S(b) + S(c) + S(d) + S(e) + S(f)|>>;;

depth (rewrite eqs) <<|S(a) + b + c + d + e + f|>>;;

depth (rewrite eqs) <<|(S(a) + S(b)) + (S(c) + S(d)) + (S(e) + S(f))|>>;;

depth (rewrite eqs)
  <<|S(0) + (S(a) + S(b)) + (S(c) + S(d)) + (S(e) + S(f))|>>;;

END_INTERACTIVE;;
