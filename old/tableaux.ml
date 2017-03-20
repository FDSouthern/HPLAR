(* ========================================================================= *)
(* Tableaux, seen as an optimized version of a Prawitz-like procedure.       *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Unify literals (just pretend the toplevel relation is a function).        *)
(* ------------------------------------------------------------------------- *)

let rec unify_literals env =
  function (Atom(R(p1,a1)),Atom(R(p2,a2))) ->
                       unify env [Fn(p1,a1),Fn(p2,a2)]
         | (Not(p),Not(q)) -> unify_literals env (p,q)
         | (False,False) -> env
         | _ -> failwith "Can't unify literals";;

(* ------------------------------------------------------------------------- *)
(* Unify complementary literals.                                             *)
(* ------------------------------------------------------------------------- *)

let unify_complements env (p,q) = unify_literals env (p,negate q);;

(* ------------------------------------------------------------------------- *)
(* Unify and refute a set of disjuncts.                                      *)
(* ------------------------------------------------------------------------- *)

let rec unify_refute djs env =
  match djs with
    [] -> env
  | cjs::odjs -> let pos,neg = partition positive cjs in
                 tryfind (unify_refute odjs ** unify_complements env)
                         (allpairs (fun p q -> (p,q)) pos neg);;

(* ------------------------------------------------------------------------- *)
(* Hence a Prawitz-like procedure (using unification on DNF).                *)
(* ------------------------------------------------------------------------- *)

let rec prawitz_loop djs0 fvs djs n =
  let newvars =
    map (fun k -> "_" ^ string_of_int (n + k)) (1 -- length fvs) in
  let inst = instantiate fvs (map (fun x -> Var x) newvars) in
  let djs1 = distrib (smap (smap (formsubst inst)) djs0) djs in
  try unify_refute djs1 undefined,(n / length fvs + 1)
  with Failure _ -> prawitz_loop djs0 fvs djs1 (n + length fvs);;

let prawitz fm =
  let fm0 = skolemize(Not(generalize fm)) in
  if fm0 = False then 0
  else if fm0 = True then failwith "prawitz" else
  snd(prawitz_loop (simpdnf fm0) (fv fm0) [[]] 0);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let p20 = prawitz
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Comparison of number of ground instances.                                 *)
(* ------------------------------------------------------------------------- *)

let compare fm =
  prawitz fm,davisputnam fm;;

START_INTERACTIVE;;
let p19 = compare
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = compare
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

let p24 = compare
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x))
   ==> (exists x. P(x) /\ R(x))>>;;

let p39 = compare
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p42 = compare
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

let p44 = compare
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y)))
   ==> (exists x. J(x) /\ ~P(x))>>;;

let p59 = compare
 <<(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\ ~P(f(x)))>>;;

let p60 = compare
 <<forall x. P(x,f(x)) <=>
             exists y. (forall z. P(z,y) ==> P(z,f(x))) /\ P(x,y)>>;;

END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* More standard tableau procedure, effectively doing DNF incrementally.     *)
(* ------------------------------------------------------------------------- *)

let rec tableau (fms,lits,n) cont (env,k) =
  if n < 0 then failwith "no proof at this level" else
  match fms with
    [] -> failwith "tableau: no proof"
  | And(p,q)::unexp ->
      tableau (p::q::unexp,lits,n) cont (env,k)
  | Or(p,q)::unexp ->
      tableau (p::unexp,lits,n) (tableau (q::unexp,lits,n) cont) (env,k)
  | Forall(x,p)::unexp ->
      let y = Var("_" ^ string_of_int k) in
      let p' = formsubst (x := y) p in
      tableau (p'::unexp@[Forall(x,p)],lits,n-1) cont (env,k+1)
  | fm::unexp ->
      try tryfind (fun l -> cont(unify_complements env (fm,l),k)) lits
      with Failure _ -> tableau (unexp,fm::lits,n) cont (env,k);;

let rec deepen f n =
  try print_string "Searching with depth limit ";
      print_int n; print_newline(); f n
  with Failure _ -> deepen f (n + 1);;

let tabrefute fms =
  deepen (fun n -> tableau (fms,[],n) (fun x -> x) (undefined,0); n) 0;;

let tab fm =
  let sfm = askolemize(Not(generalize fm)) in
  if sfm = False then 0
  else if sfm = True then failwith "tab: no proof"
  else tabrefute [sfm];;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let p38 = tab
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

let p45 = tab
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;

let gilmore_9 = tab
 <<forall x. exists y. forall z.
     ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
       ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
          ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
     ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
      ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
          ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
              (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Try to split up the initial formula first; often a big improvement.       *)
(* ------------------------------------------------------------------------- *)

let splittab fm =
  map tabrefute (simpdnf(askolemize(Not(generalize fm))));;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let p34 = splittab
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
    ((exists x. forall y. Q(x) <=> Q(y)) <=>
   ((exists x. P(x)) <=> (forall y. P(y))))>>;;

let p46 = splittab
 <<(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
    ((exists x. P(x) /\ ~G(x)) ==>
     (exists x. P(x) /\ ~G(x) /\
                (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
    (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
    (forall x. P(x) ==> G(x))>>;;

(* ------------------------------------------------------------------------- *)
(* Another nice example from EWD 1602.                                       *)
(* ------------------------------------------------------------------------- *)

let ewd1062 = splittab
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
       (forall x y. x <= y ==> g(x) <= g(y))>>;;

(* ------------------------------------------------------------------------- *)
(* Well-known "Agatha" example; cf. Manthey and Bry, CADE-9.                 *)
(* ------------------------------------------------------------------------- *)

let p55 = time splittab
 <<lives(agatha) /\ lives(butler) /\ lives(charles) /\
   (killed(agatha,agatha) \/ killed(butler,agatha) \/
    killed(charles,agatha)) /\
   (forall x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
   (forall x. hates(agatha,x) ==> ~hates(charles,x)) /\
   (hates(agatha,agatha) /\ hates(agatha,charles)) /\
   (forall x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\
   (forall x. hates(agatha,x) ==> hates(butler,x)) /\
   (forall x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles))
   ==> killed(agatha,agatha) /\
       ~killed(butler,agatha) /\
       ~killed(charles,agatha)>>;;

(* ------------------------------------------------------------------------- *)
(* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
(* ------------------------------------------------------------------------- *)

let davis_putnam_example = time splittab
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

END_INTERACTIVE;;
