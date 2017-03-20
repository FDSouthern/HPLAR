(* ========================================================================= *)
(* Resolution.                                                               *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Barber's paradox is an example of why we need factoring.                  *)
(* ------------------------------------------------------------------------- *)

let barb = <<~(exists b. forall x. shaves(b,x) <=> ~shaves(x,x))>>;;

START_INTERACTIVE;;
clausal(skolemize(Not barb));;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* MGU of a set of literals.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec mgu l env =
  match l with
    a::b::rest -> mgu (b::rest) (unify_literals env (a,b))
  | _ -> solve env;;

let unifiable p q = can (unify_literals undefined) (p,q);;

(* ------------------------------------------------------------------------- *)
(* Rename a clause.                                                          *)
(* ------------------------------------------------------------------------- *)

let rename pfx cls =
  let fvs = fv(list_disj cls) in
  let vvs = map (fun s -> Var(pfx^s)) fvs  in
  map (formsubst(instantiate fvs vvs)) cls;;

(* ------------------------------------------------------------------------- *)
(* General resolution rule, incorporating factoring as in Robinson's paper.  *)
(* ------------------------------------------------------------------------- *)

let resolvents cl1 cl2 p acc =
  let ps2 = filter (unifiable(negate p)) cl2 in
  if ps2 = [] then acc else
  let ps1 = filter (fun q -> q <> p & unifiable p q) cl1 in
  let pairs = allpairs (fun s1 s2 -> s1,s2)
                       (map (fun pl -> p::pl) (allsubsets ps1))
                       (allnonemptysubsets ps2) in
  itlist (fun (s1,s2) sof ->
           try smap (formsubst (mgu (s1 @ map negate s2) undefined))
                    (union (subtract cl1 s1) (subtract cl2 s2)) :: sof
           with Failure _ -> sof) pairs acc;;

let resolve_clauses cls1 cls2 =
  let cls1' = rename "x" cls1 and cls2' = rename "y" cls2 in
  itlist (resolvents cls1' cls2') cls1' [];;

(* ------------------------------------------------------------------------- *)
(* Basic "Argonne" loop.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec resloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cls::ros ->
        print_string(string_of_int(length used) ^ " used; "^
                     string_of_int(length unused) ^ " unused.");
        print_newline();
        let used' = insert cls used in
        let news =
          itlist (@) (mapfilter (resolve_clauses cls) used') [] in
        if mem [] news then true else resloop (used',ros@news);;

let pure_resolution fm =
  resloop([],clausal(specialize(pnf fm)));;

let resolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_resolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Simple example that works well.                                           *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let davis_putnam_example = resolution
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Tautology checking for a clause (re-using dual code).                     *)
(* ------------------------------------------------------------------------- *)

let tautologous = contradictory;;

(* ------------------------------------------------------------------------- *)
(* Test for subsumption                                                      *)
(* ------------------------------------------------------------------------- *)

let subsumes_clause cls1 cls2 =
  let fvs = itlist (union ** fv) cls2 [] in
  let ifn = formsubst
    (itlist (fun x -> x |-> Fn("_"^x,[])) fvs undefined) in
  let cls2' = map ifn cls2 in
  let rec subsume env cls =
    match cls with
      [] -> env
    | l1::cls' ->
        tryfind (fun l2 -> subsume (unify_literals env (l1,l2)) cls')
                cls2' in
  can (subsume undefined) cls1;;

(* ------------------------------------------------------------------------- *)
(* With deletion of tautologies and bi-subsumption with "unused".            *)
(* ------------------------------------------------------------------------- *)

let rec replace cl lis =
  match lis with
    [] -> [cl]
  | c::cls -> if subsumes_clause cl c then cl::cls
              else c::(replace cl cls);;

let incorporate gcl cl unused =
  if tautologous cl or
     exists (fun c -> subsumes_clause c cl) (gcl::unused)
  then unused else replace cl unused;;

let rec resloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cls::ros ->
        print_string(string_of_int(length used) ^ " used; "^
                     string_of_int(length unused) ^ " unused.");
        print_newline();
        let used' = insert cls used in
        let news =
          itlist (@) (mapfilter (resolve_clauses cls) used') [] in
        if mem [] news then true else
        resloop(used',itlist (incorporate cls) news ros);;

let pure_resolution fm =
  resloop([],filter (non tautologous) (clausal(specialize(pnf fm))));;

let resolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_resolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* This is now a lot quicker.                                                *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let davis_putnam_example = resolution
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Positive (P1) resolution.                                                 *)
(* ------------------------------------------------------------------------- *)

let presolve_clauses cls1 cls2 =
  if forall positive cls1 or forall positive cls2
  then resolve_clauses  cls1 cls2 else [];;

let rec presloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cls::ros ->
        print_string(string_of_int(length used) ^ " used; "^
                     string_of_int(length unused) ^ " unused.");
        print_newline();
        let used' = insert cls used in
        let news =
          itlist (@) (mapfilter (presolve_clauses cls) used') [] in
        if mem [] news then true else
        presloop(used',itlist (incorporate cls) news ros);;

let pure_presolution fm =
  presloop([],filter (non tautologous) (clausal(specialize(pnf fm))));;

let presolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_presolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Example: the (in)famous Los problem.                                      *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let los = time presolution
 <<(forall x y z. P(x,y) ==> P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) ==> Q(y,z) ==> Q(x,z)) /\
   (forall x y. Q(x,y) ==> Q(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))>>;;

(* ------------------------------------------------------------------------- *)
(* Example from Manthey and Bry, CADE-9.                                     *)
(* ------------------------------------------------------------------------- *)

let p55 = time presolution
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
(* From Gilmore's classic paper.                                             *)
(* ------------------------------------------------------------------------- *)

let gilmore_1 = time presolution
 <<exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)>>;;

let gilmore_3 = time presolution
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> H(z)) /\
        F(x,y)
        ==> F(z,z)>>;;

let gilmore_4 = time presolution
 <<exists x y. forall z.
        (F(x,y) ==> F(y,z) /\ F(z,z)) /\
        (F(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

let gilmore_5 = time presolution
 <<(forall x. exists y. F(x,y) \/ F(y,x)) /\
   (forall x y. F(y,x) ==> F(y,y))
   ==> exists z. F(z,z)>>;;

let gilmore_6 = time presolution
 <<forall x. exists y.
        (exists u. forall v. F(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. F(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

let gilmore_7 = time presolution
 <<(forall x. K(x) ==> exists y. L(y) /\ (F(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> F(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

let gilmore_8 = time presolution
 <<exists x. forall y z.
        ((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\
        ((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        F(x,y)
        ==> F(z,z)>>;;

(* ------------------------------------------------------------------------- *)
(* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
(* ------------------------------------------------------------------------- *)

let davis_putnam_example = time presolution
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Introduce a set-of-support restriction.                                   *)
(* ------------------------------------------------------------------------- *)

let pure_resolution fm =
  let cls = filter (non tautologous) (clausal(specialize(pnf fm))) in
  resloop(partition (exists positive) cls);;

let resolution fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_resolution ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Example                                                                   *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let gilmore_1 = resolution
 <<exists x. forall y z.
      ((F(y) ==> G(y)) <=> F(x)) /\
      ((F(y) ==> H(y)) <=> G(x)) /\
      (((F(y) ==> G(y)) ==> H(y)) <=> H(x))
      ==> F(z) /\ G(z) /\ H(z)>>;;

(* ------------------------------------------------------------------------- *)
(* Some Pelletier problems.                                                  *)
(* ------------------------------------------------------------------------- *)

let p1 = time resolution
 <<p ==> q <=> ~q ==> ~p>>;;

let p2 = time resolution
 <<~ ~p <=> p>>;;

let p3 = time resolution
 <<~(p ==> q) ==> q ==> p>>;;

let p4 = time resolution
 <<~p ==> q <=> ~q ==> p>>;;

let p5 = time resolution
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let p6 = time resolution
 <<p \/ ~p>>;;

let p7 = time resolution
 <<p \/ ~ ~ ~p>>;;

let p8 = time resolution
 <<((p ==> q) ==> p) ==> p>>;;

let p9 = time resolution
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let p10 = time resolution
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let p11 = time resolution
 <<p <=> p>>;;

let p12 = time resolution
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let p13 = time resolution
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let p14 = time resolution
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let p15 = time resolution
 <<p ==> q <=> ~p \/ q>>;;

let p16 = time resolution
 <<(p ==> q) \/ (q ==> p)>>;;

let p17 = time resolution
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

let p18 = time resolution
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = time resolution
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = time resolution
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==>
   (exists x y. P(x) /\ Q(y)) ==>
   (exists z. R(z))>>;;

let p21 = time resolution
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))>>;;

let p22 = time resolution
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

let p23 = time resolution
 <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

let p24 = time resolution
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))>>;;

let p25 = time resolution
 <<(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
   (exists x. Q(x) /\ P(x))>>;;

let p26 = time resolution
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p27 = time resolution
 <<(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x)) ==>
   (forall x. U(x) ==> ~R(x)) ==>
   (forall x. U(x) ==> ~V(x))>>;;

let p28 = time resolution
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p29 = time resolution
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

let p30 = time resolution
 <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==>
     P(x) /\ H(x)) ==>
   (forall x. U(x))>>;;

let p31 = time resolution
 <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x)) ==>
   (exists x. Q(x) /\ J(x))>>;;

let p32 = time resolution
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x)) ==>
   (forall x. P(x) /\ R(x) ==> J(x))>>;;

let p33 = time resolution
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

let p34 = time resolution
 <<((exists x. forall y. P(x) <=> P(y)) <=>
   ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
  ((exists x. P(x)) <=> (forall y. P(y))))>>;;

let p35 = time resolution
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

let p36 = time resolution
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))>>;;

let p37 = time resolution
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))>>;;

let p39 = time resolution
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p40 = time resolution
 <<(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

let p41 = time resolution
 <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))>>;;

let p44 = time resolution
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))>>;;

let p55 = time resolution
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

let p57 = time resolution
 <<P(f((a),b),f(b,c)) /\
   P(f(b,c),f(a,c)) /\
   (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
   ==> P(f(a,b),f(a,c))>>;;

END_INTERACTIVE;;
