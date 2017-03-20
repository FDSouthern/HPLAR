(* ========================================================================= *)
(* Model elimination procedure (MESON version, based on Stickel's PTTP).     *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Example of naivety of tableau prover.                                     *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
tab <<forall a. ~(P(a) /\ (forall y z. Q(y) \/ R(z)) /\ ~P(a))>>;;

tab <<forall a. ~(P(a) /\ ~P(a) /\ (forall y z. Q(y) \/ R(z)))>>;;

(* ------------------------------------------------------------------------- *)
(* The interesting example where tableaux connections make the proof longer. *)
(* Unfortuntely this gets hammered by normalization first...                 *)
(* ------------------------------------------------------------------------- *)

let th = tab
 <<~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\
   (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\
   (~s \/ ~v) /\ (~s \/ ~w) ==> false>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Generation of contrapositives.                                            *)
(* ------------------------------------------------------------------------- *)

let contrapositives cls =
  let base = map (fun c -> map negate (subtract cls [c]),c) cls in
  if forall negative cls then (map negate cls,False)::base else base;;

(* ------------------------------------------------------------------------- *)
(* The core of MESON: ancestor unification or Prolog-style extension.        *)
(* ------------------------------------------------------------------------- *)

let rec expand rules ancestors g cont (env,n,k) =
  if n < 0 then failwith "Too deep" else
  try tryfind (fun a -> cont (unify_literals env (g,negate a),n,k))
              ancestors
  with Failure _ -> tryfind
    (fun rule -> let (asm,c),k' = renamer k rule in
                 itlist (expand rules (g::ancestors)) asm cont
                        (unify_literals env (g,c),n-length asm,k'))
    rules;;

(* ------------------------------------------------------------------------- *)
(* Full MESON procedure.                                                     *)
(* ------------------------------------------------------------------------- *)

let puremeson fm =
  let cls = clausal(specialize(pnf fm)) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  deepen (fun n ->
     expand rules [] False (fun x -> x) (undefined,n,0); n) 0;;

let meson fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (puremeson ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let davis_putnam_example = meson
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

let p38 = time meson
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

let gilmore_9a = meson
 <<(forall x y. P(x,y) <=>
                forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
   ==> forall x. exists y. forall z.
             (P(y,x) ==> (P(x,z) ==> P(x,y))) /\
             (P(x,y) ==> (~P(x,z) ==> P(y,x) /\ P(z,y)))>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* With repetition checking and divide-and-conquer search.                   *)
(* ------------------------------------------------------------------------- *)

let rec equal env fm1 fm2 =
  try unify_literals env (fm1,fm2) == env with Failure _ -> false;;

let expand2 expfn goals1 n1 goals2 n2 n3 cont env k =
   expfn goals1 (fun (e1,r1,k1) ->
        expfn goals2 (fun (e2,r2,k2) ->
                        if n2 + r1 <= n3 + r2 then failwith "pair"
                        else cont(e2,r2,k2))
              (e1,n2+r1,k1))
        (env,n1,k);;

let rec expand rules ancestors g cont (env,n,k) =
  if n < 0 then failwith "Too deep"
  else if exists (equal env g) ancestors then failwith "repetition" else
  try tryfind (fun a -> cont (unify_literals env (g,negate a),n,k))
              ancestors
  with Failure _ -> tryfind
    (fun r -> let (asm,c),k' = renamer k r in
              expands rules (g::ancestors) asm cont
                      (unify_literals env (g,c),n-length asm,k'))
    rules

and expands rules ancestors gs cont (env,n,k) =
  if n < 0 then failwith "Too deep" else
  let m = length gs in
  if m <= 1 then itlist (expand rules ancestors) gs cont (env,n,k) else
  let n1 = n / 2 in
  let n2 = n - n1 in
  let goals1,goals2 = chop_list (m / 2) gs in
  let expfn = expand2 (expands rules ancestors) in
  try expfn goals1 n1 goals2 n2 (-1) cont env k
  with Failure _ -> expfn goals2 n1 goals1 n2 n1 cont env k;;

let puremeson fm =
  let cls = clausal(specialize(pnf fm)) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  deepen (fun n ->
     expand rules [] False (fun x -> x) (undefined,n,0); n) 0;;

let meson fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (puremeson ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Test it on some of the Pelletiers.                                        *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;

let prop_1 = time meson
 <<p ==> q <=> ~q ==> ~p>>;;

let prop_2 = time meson
 <<~ ~p <=> p>>;;

let prop_3 = time meson
 <<~(p ==> q) ==> q ==> p>>;;

let prop_4 = time meson
 <<~p ==> q <=> ~q ==> p>>;;

let prop_5 = time meson
 <<(p \/ q ==> p \/ r) ==> p \/ (q ==> r)>>;;

let prop_6 = time meson
 <<p \/ ~p>>;;

let prop_7 = time meson
 <<p \/ ~ ~ ~p>>;;

let prop_8 = time meson
 <<((p ==> q) ==> p) ==> p>>;;

let prop_9 = time meson
 <<(p \/ q) /\ (~p \/ q) /\ (p \/ ~q) ==> ~(~q \/ ~q)>>;;

let prop_10 = time meson
 <<(q ==> r) /\ (r ==> p /\ q) /\ (p ==> q /\ r) ==> (p <=> q)>>;;

let prop_11 = time meson
 <<p <=> p>>;;

let prop_12 = time meson
 <<((p <=> q) <=> r) <=> (p <=> (q <=> r))>>;;

let prop_13 = time meson
 <<p \/ q /\ r <=> (p \/ q) /\ (p \/ r)>>;;

let prop_14 = time meson
 <<(p <=> q) <=> (q \/ ~p) /\ (~q \/ p)>>;;

let prop_15 = time meson
 <<p ==> q <=> ~p \/ q>>;;

let prop_16 = time meson
 <<(p ==> q) \/ (q ==> p)>>;;

let prop_17 = time meson
 <<p /\ (q ==> r) ==> s <=> (~p \/ q \/ s) /\ (~p \/ ~r \/ s)>>;;

let p18 = time meson
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = time meson
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = time meson
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w)) ==>
   (exists x y. P(x) /\ Q(y)) ==>
   (exists z. R(z))>>;;

let p21 = time meson
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))>>;;

let p22 = time meson
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

let p23 = time meson
 <<(forall x. P \/ Q(x)) <=> P \/ (forall x. Q(x))>>;;

let p24 = time meson
 <<~(exists x. U(x) /\ Q(x)) /\
   (forall x. P(x) ==> Q(x) \/ R(x)) /\
   ~(exists x. P(x) ==> (exists x. Q(x))) /\
   (forall x. Q(x) /\ R(x) ==> U(x)) ==>
   (exists x. P(x) /\ R(x))>>;;

let p25 = time meson
 <<(exists x. P(x)) /\
   (forall x. U(x) ==> ~G(x) /\ R(x)) /\
   (forall x. P(x) ==> G(x) /\ U(x)) /\
   ((forall x. P(x) ==> Q(x)) \/ (exists x. Q(x) /\ P(x))) ==>
   (exists x. Q(x) /\ P(x))>>;;

let p26 = time meson
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p27 = time meson
 <<(exists x. P(x) /\ ~Q(x)) /\
   (forall x. P(x) ==> R(x)) /\
   (forall x. U(x) /\ V(x) ==> P(x)) /\
   (exists x. R(x) /\ ~Q(x)) ==>
   (forall x. U(x) ==> ~R(x)) ==>
   (forall x. U(x) ==> ~V(x))>>;;

let p28 = time meson
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p29 = time meson
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

let p30 = time meson
 <<(forall x. P(x) \/ G(x) ==> ~H(x)) /\ (forall x. (G(x) ==> ~U(x)) ==>
     P(x) /\ H(x)) ==>
   (forall x. U(x))>>;;

let p31 = time meson
 <<~(exists x. P(x) /\ (G(x) \/ H(x))) /\ (exists x. Q(x) /\ P(x)) /\
   (forall x. ~H(x) ==> J(x)) ==>
   (exists x. Q(x) /\ J(x))>>;;

let p32 = time meson
 <<(forall x. P(x) /\ (G(x) \/ H(x)) ==> Q(x)) /\
   (forall x. Q(x) /\ H(x) ==> J(x)) /\
   (forall x. R(x) ==> H(x)) ==>
   (forall x. P(x) /\ R(x) ==> J(x))>>;;

let p33 = time meson
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

let p34 = time meson
 <<((exists x. forall y. P(x) <=> P(y)) <=>
   ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
  ((exists x. P(x)) <=> (forall y. P(y))))>>;;

let p35 = time meson
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

let p36 = time meson
 <<(forall x. exists y. P(x,y)) /\
   (forall x. exists y. G(x,y)) /\
   (forall x y. P(x,y) \/ G(x,y)
   ==> (forall z. P(y,z) \/ G(y,z) ==> H(x,z)))
       ==> (forall x. exists y. H(x,y))>>;;

let p37 = time meson
 <<(forall z.
     exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\ P(y,z) /\
     (P(y,w) ==> (exists u. Q(u,w)))) /\
   (forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\
   ((exists x y. Q(x,y)) ==> (forall x. R(x,x))) ==>
   (forall x. exists y. R(x,y))>>;;

let p38 = time meson
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

let p39 = time meson
 <<~(exists x. forall y. P(y,x) <=> ~P(y,y))>>;;

let p40 = time meson
 <<(exists y. forall x. P(x,y) <=> P(x,x))
  ==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))>>;;

let p41 = time meson
 <<(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\ ~P(x,x))
  ==> ~(exists z. forall x. P(x,z))>>;;

let p42 = time meson
 <<~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\ P(z,x)))>>;;

let p43 = time meson
 <<(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y))
   ==> forall x y. Q(x,y) <=> Q(y,x)>>;;

let p44 = time meson
 <<(forall x. P(x) ==> (exists y. G(y) /\ H(x,y)) /\
   (exists y. G(y) /\ ~H(x,y))) /\
   (exists x. J(x) /\ (forall y. G(y) ==> H(x,y))) ==>
   (exists x. J(x) /\ ~P(x))>>;;

let p45 = time meson
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;

let p46 = time meson
 <<(forall x. P(x) /\ (forall y. P(y) /\ H(y,x) ==> G(y)) ==> G(x)) /\
   ((exists x. P(x) /\ ~G(x)) ==>
    (exists x. P(x) /\ ~G(x) /\
               (forall y. P(y) /\ ~G(y) ==> J(x,y)))) /\
   (forall x y. P(x) /\ P(y) /\ H(x,y) ==> ~J(y,x)) ==>
   (forall x. P(x) ==> G(x))>>;;

let p55 = time meson
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

let p57 = time meson
 <<P(f((a),b),f(b,c)) /\
  P(f(b,c),f(a,c)) /\
  (forall (x) y z. P(x,y) /\ P(y,z) ==> P(x,z))
  ==> P(f(a,b),f(a,c))>>;;

(* ------------------------------------------------------------------------- *)
(* Translation of Gilmore procedure using separate definitions.              *)
(* ------------------------------------------------------------------------- *)

let gilmore_9a = time meson
 <<(forall x y. P(x,y) <=>
                forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
   ==> forall x. exists y. forall z.
             (P(y,x) ==> (P(x,z) ==> P(x,y))) /\
             (P(x,y) ==> (~P(x,z) ==> P(y,x) /\ P(z,y)))>>;;

(* ------------------------------------------------------------------------- *)
(* Example from Davis-Putnam papers where Gilmore procedure is poor.         *)
(* ------------------------------------------------------------------------- *)

let davis_putnam_example = time meson
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

(* ------------------------------------------------------------------------- *)
(* The "connections make things worse" example once again.                   *)
(* ------------------------------------------------------------------------- *)

let th = meson
 <<~p /\ (p \/ q) /\ (r \/ s) /\ (~q \/ t \/ u) /\
   (~r \/ ~t) /\ (~r \/ ~u) /\ (~q \/ v \/ w) /\
   (~s \/ ~v) /\ (~s \/ ~w) ==> false>>;;

END_INTERACTIVE;;
