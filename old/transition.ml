(* ========================================================================= *)
(* Finite state transition systems.                                          *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

let default_parser = parsep;;

(* ------------------------------------------------------------------------- *)
(* Transition relation for modulo-5 counter.                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let counter_trans =
 <<(v0' <=> ~v0 /\ ~v2) /\
   (v1' <=> ~(v0 <=> v1)) /\
   (v2' <=> v0 /\ v1)>>;;

(* ------------------------------------------------------------------------- *)
(* Transition relation for incorrect mutex algorithm.                        *)
(* ------------------------------------------------------------------------- *)

let mutex_trans =
 <<(q2' <=> q2) /\ (q1' <=> q1) /\ (q0' <=> q0) /\
  (~p2 /\ ~p1 /\ ~p0 /\ ~v1 /\ ~v0
   ==> ~p2' /\ ~p1' /\ p0' /\ ~v1' /\ ~v0') /\
  (~p2 /\ ~p1 /\ ~p0 /\ (v1 \/ v0)
   ==> ~p2' /\ ~p1' /\ ~p0' /\ (v1' <=> v1) /\ (v0' <=> v0)) /\
  (~p2 /\ ~p1 /\ p0
   ==> ~p2' /\ p1' /\ ~p0' /\ ~v1' /\ v0') /\
  (~p2 /\ p1 /\ ~p0
   ==> ~p2' /\ p1' /\ p0' /\ (v1' <=> v1) /\ (v0' <=> v0)) /\
  (~p2 /\ p1 /\ p0
   ==> p2' /\ ~p1' /\ ~p0' /\ ~v1' /\ ~v0') /\
  (p2 /\ ~p1 /\ ~p0
   ==> ~p2' /\ ~p1' /\ ~p0' /\ (v1' <=> v1) /\ (v0' <=> v0)) \/
  (p2' <=> p2) /\ (p1' <=> p1) /\ (p0' <=> p0) /\
  (~q2 /\ ~q1 /\ ~q0 /\ ~v1 /\ ~v0
   ==> ~q2' /\ ~q1' /\ q0' /\ ~v1' /\ ~v0') /\
  (~q2 /\ ~q1 /\ ~q0 /\ (v1 \/ v0)
   ==> ~q2' /\ ~q1' /\ ~q0' /\ (v1' <=> v1) /\ (v0' <=> v0)) /\
  (~q2 /\ ~q1 /\ q0
   ==> ~q2' /\ q1' /\ ~q0' /\ v1' /\ ~v0') /\
  (~q2 /\ q1 /\ ~q0
   ==> ~q2' /\ q1' /\ q0' /\ (v1' <=> v1) /\ (v0' <=> v0)) /\
  (~q2 /\ q1 /\ q0
   ==> q2' /\ ~q1' /\ ~q0' /\ ~v1' /\ ~v0') /\
  (q2 /\ ~q1 /\ ~q0
   ==> ~q2' /\ ~q1' /\ ~q0' /\ (v1' <=> v1) /\ (v0' <=> v0))>>;;

(* ------------------------------------------------------------------------- *)
(* Same for Peterson's algorithm.                                            *)
(* ------------------------------------------------------------------------- *)

let peter_trans =
 <<(q2' <=> q2) /\ (q1' <=> q1) /\ (q0' <=> q0) /\
  (~p2 /\ ~p1 /\ ~p0
   ==> ~p2' /\ ~p1' /\ p0' /\ f1' /\ (f2' <=> f2) /\ (t' <=> t)) /\
  (~p2 /\ ~p1 /\ p0
   ==> ~p2' /\ p1' /\ ~p0' /\ (f1' <=> f1) /\ (f2' <=> f2) /\ t') /\
  (~p2 /\ p1 /\ ~p0 /\ f2
   ==> ~p2' /\ p1' /\ p0' /\ f2' /\ (f1' <=> f1) /\ (t' <=> t)) /\
  (~p2 /\ p1 /\ ~p0 /\ ~f2
   ==> p2' /\ ~p1' /\ ~p0' /\ ~f2' /\ (f1' <=> f1) /\ (t' <=> t)) /\
  (~p2 /\ p1 /\ p0 /\ t
   ==> ~p2' /\ p1' /\ ~p0' /\ t' /\ (f1' <=> f1) /\ (f2' <=> f2)) /\
  (~p2 /\ p1 /\ p0 /\ ~t
   ==> p2' /\ ~p1' /\ ~p0' /\ ~t' /\ (f1' <=> f1) /\ (f2' <=> f2)) /\
  (p2 /\ ~p1 /\ ~p0
   ==> p2' /\ ~p1' /\ p0' /\
       (f1' <=> f1) /\ (f2' <=> f2) /\ (t' <=> t)) /\
  (p2 /\ ~p1 /\ p0
   ==> p2' /\ p1' /\ ~p0' /\ ~f1' /\ (f2' <=> f2) /\ (t' <=> t)) /\
  (p2 /\ p1 /\ ~p0
   ==> ~p2' /\ ~p1' /\ ~p0' /\
       (f1' <=> f1) /\ (f2' <=> f2) /\ (t' <=> t)) \/
  (p2' <=> p2) /\ (p1' <=> p1) /\ (p0' <=> p0) /\
  (~q2 /\ ~q1 /\ ~q0
   ==> ~q2' /\ ~q1' /\ q0' /\ f2' /\ (f1' <=> f1) /\ (t' <=> t)) /\
  (~q2 /\ ~q1 /\ q0
   ==> ~q2' /\ q1' /\ ~q0' /\ (f1' <=> f1) /\ (f2' <=> f2) /\ ~t') /\
  (~q2 /\ q1 /\ ~q0 /\ f1
   ==> ~q2' /\ q1' /\ q0' /\ f1' /\ (f2' <=> f2) /\ (t' <=> t)) /\
  (~q2 /\ q1 /\ ~q0 /\ ~f1
   ==> q2' /\ ~q1' /\ ~q0' /\ ~f1' /\ (f2' <=> f2) /\ (t' <=> t)) /\
  (~q2 /\ q1 /\ q0 /\ ~t
   ==> ~q2' /\ q1' /\ ~q0' /\ ~t' /\ (f1' <=> f1) /\ (f2' <=> f2)) /\
  (~q2 /\ q1 /\ q0 /\ t
   ==> q2' /\ ~q1' /\ ~q0' /\ t' /\ (f1' <=> f1) /\ (f2' <=> f2)) /\
  (q2 /\ ~q1 /\ ~q0
   ==> q2' /\ ~q1' /\ q0' /\
       (f1' <=> f1) /\ (f2' <=> f2) /\ (t' <=> t)) /\
  (q2 /\ ~q1 /\ q0
   ==> q2' /\ q1' /\ ~q0' /\ ~f2' /\ (f1' <=> f1) /\ (t' <=> t)) /\
  (q2 /\ q1 /\ ~q0
   ==> ~q2' /\ ~q1' /\ ~q0' /\
       (f1' <=> f1) /\ (f2' <=> f2) /\ (t' <=> t))>>;;

(* ------------------------------------------------------------------------- *)
(* Example of "induction" method for reachability.                           *)
(* ------------------------------------------------------------------------- *)

tautology(Imp(counter_trans,<<~(v0 /\ v2) ==> ~(v0' /\ v2')>>));;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Useful combinators for applying functions maintaining bdd state.          *)
(* ------------------------------------------------------------------------- *)

let single f bst x fn = let bst1,x' = f bst x in fn bst1 x';;

let double f bst x y fn =
  let bst1,x' = f bst x in let bst2,y' = f bst1 y in fn bst2 (x',y');;

(* ------------------------------------------------------------------------- *)
(* More uniform BDD operations all with BDD and two computed tables.         *)
(* ------------------------------------------------------------------------- *)

let bdd_And (bdd,acomp,pcomp) (m,n) =
  let (bdd',acomp'),p = bdd_and (bdd,acomp) (m,n) in
  (bdd',acomp',pcomp),p;;

let bdd_Node s (bdd,acomp,pcomp as bst) (l,r) =
  let bdd',n = mk_node bdd (s,l,r) in (bdd',acomp,pcomp),n;;

let bdd_Make (bdd,acomp,pcomp) fm =
  let (bdd',acomp'),n = bddify [] (bdd,acomp) fm in
  (bdd',acomp',pcomp),n;;

(* ------------------------------------------------------------------------- *)
(* Iterative version of bdd_Make for a list of formulas.                     *)
(* ------------------------------------------------------------------------- *)

let rec bdd_Makes bst fms =
  match fms with
    [] -> bst,[]
  | fm::ofms -> let bst1,n = bdd_Make bst fm in
                let bst2,ns = bdd_Makes bst1 ofms in bst2,n::ns;;

(* ------------------------------------------------------------------------- *)
(* Derived BDD logical operations.                                           *)
(* ------------------------------------------------------------------------- *)

let bdd_Or bst (m,n) =
  let bst',p = bdd_And bst (-m,-n) in bst',-p;;

let bdd_Imp bst (m,n) = bdd_Or bst (-m,n);;

let bdd_Not bst n = (bst,-n);;

let bdd_Iff bst (m,n) = double bdd_Imp bst (m,n) (n,m) bdd_And;;

(* ------------------------------------------------------------------------- *)
(* Combined "Pre" operation, doing relational product and priming second     *)
(* BDD's variables at the same time.                                         *)
(*                                                                           *)
(* Given arguments vs', r[vs,vs'] and p[vs], this produces the BDD for       *)
(*                                                                           *)
(*         exists vs'. r[vs,vs'] /\ p[vs']                                   *)
(*                                                                           *)
(* We must have the same relative orders of primed and unprimed variables!   *)
(* ------------------------------------------------------------------------- *)

let rec bdd_Pre evs (bdd,acomp,pcomp as bst) (m1,m2) =
  if m1 = -1 or m2 = -1 then bst,-1
  else if m1 = 1 then bst,1 else
  try bst,apply pcomp (m1,m2) with Failure _ ->
  let (s1,l1,r1) = expand_node bdd m1
  and (s0,l2,r2) = expand_node bdd m2 in
  let s0' = P(pname s0^"'") in
  let (s,lpair,rpair) =
      if s1 = s0' then s1,(l1,l2),(r1,r2)
      else if s0 = P "" or order bdd s1 s0' then s1,(l1,m2),(r1,m2)
      else s0',(m1,l2),(m1,r2) in
  let bdd_orex = if mem s evs then bdd_Or else bdd_Node s in
  let (bdd',acomp',pcomp'),n =
    double (bdd_Pre evs) bst lpair rpair bdd_orex in
  (bdd',acomp',((m1,m2) |-> n) pcomp'),n;;

(* ------------------------------------------------------------------------- *)
(* Iterate a BDD operation till a fixpoint is reached.                       *)
(* ------------------------------------------------------------------------- *)

let rec iterate_to_fixpoint f bst n =
  let bst',n' = f bst n in
  if n' = n then bst',n' else iterate_to_fixpoint f bst' n';;

(* ------------------------------------------------------------------------- *)
(* Model-check EF(p) by iterating a |-> p \/ Pre(a).                         *)
(* ------------------------------------------------------------------------- *)

let step_EF evs r p bst a =
  let bst',a' = bdd_Pre evs bst (r,a) in bdd_Or bst' (p,a');;

let check_EF evs r bst p =
  iterate_to_fixpoint (step_EF evs r p) bst (-1);;

(* ------------------------------------------------------------------------- *)
(* Simple reachability. (Can we get from s to p via relation r?)             *)
(* ------------------------------------------------------------------------- *)

let reachable vars s r p =
  let vars' = map (fun s -> P(s^"'")) vars in
  let bst0 = mk_bdd (fun s1 s2 -> s1 < s2),undefined,undefined in
  let bst1,[n_s;n_r;n_p] = bdd_Makes bst0 [s;r;p] in
  let bst2,n_f = check_EF vars' n_r bst1 n_p in
  snd(bdd_And bst2 (n_s,n_f)) <> -1;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
reachable ["v2"; "v1"; "v0"]
  <<true>> counter_trans <<v2 /\ v1>>;;

reachable ["v2"; "v1"; "v0"]
  <<~v2 /\ ~v1 /\ ~v0>> counter_trans <<v2 /\ v1>>;;

reachable ["p2"; "p1"; "p0"; "q2"; "q1"; "q0"; "v1"; "v0"]
  <<~p2 /\ ~p1 /\ ~p0 /\ ~q2 /\ ~q1 /\ ~q0 /\ ~v1 /\ ~v0>>
  mutex_trans
  <<~p2 /\ p1 /\ ~p0 /\ ~q2 /\ q1 /\ ~q0>>;;

reachable ["p2"; "p1"; "p0"; "q2"; "q1"; "q0"; "f2"; "f1"; "t"]
  <<~p2 /\ ~p1 /\ ~p0 /\ ~q2 /\ ~q1 /\ ~q0>>
  peter_trans
  <<p2 /\ ~p1 /\ ~p0 /\ q2 /\ ~q1 /\ ~q0>>;;
END_INTERACTIVE;;
