(* ========================================================================= *)
(* First order reasoning by derived rules atop the LCF core.                 *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ---------------------------------------------------------------------- *)
(* Symmetry and transitivity of equality.                                 *)
(* ---------------------------------------------------------------------- *)

let eq_sym s t =
  let rth = axiom_eqrefl s in
  funpow 2 (fun th -> modusponens (imp_swap th) rth)
           (axiom_predcong "=" [s; s] [t; s]);;

let eq_trans s t u =
  let th1 = axiom_predcong "=" [t; u] [s; u] in
  let th2 = modusponens (imp_swap th1) (axiom_eqrefl u) in
  imp_trans (eq_sym s t) th2;;

(* ------------------------------------------------------------------------- *)
(* Congruences.                                                              *)
(* ------------------------------------------------------------------------- *)

let rec congruence s t tm =
  if s = tm then imp_refl(mk_eq s t)
  else if not (occurs_in s tm)
  then add_assum (mk_eq s t) (axiom_eqrefl tm) else
  let (Fn(f,args)) = tm in
  let ths = map (congruence s t) args in
  let tms = map (consequent ** concl) ths in
  imp_trans_chain ths (axiom_funcong f (map lhs tms) (map rhs tms));;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
congruence <<|s|>>  <<|t|>>
           <<|f(s,g(s,t,s),u,h(h(s)))|>> ;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q then |- ~q ==> ~p                                           *)
(* ------------------------------------------------------------------------- *)

let contrapos th =
  let p,q = dest_imp(concl th) in
  imp_trans (imp_trans (iff_imp1(axiom_not q)) (imp_add_concl False th))
            (iff_imp2(axiom_not p));;

(* ------------------------------------------------------------------------- *)
(* |- ~ ~p ==> p                                                             *)
(* ------------------------------------------------------------------------- *)

let neg_neg p =
  let th1 = iff_imp1(axiom_not (Not p))
  and th2 = imp_add_concl False (iff_imp2(axiom_not p)) in
  imp_trans (imp_trans th1 th2) (axiom_doubleneg p);;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q then |- (forall x. p) ==> (forall x. q)                     *)
(* ------------------------------------------------------------------------- *)

let genimp x th =
  let p,q = dest_imp(concl th) in
  modusponens (axiom_allimp x p q) (gen x th);;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q then |- (exists x. p) ==> (exists x. q)                     *)
(* ------------------------------------------------------------------------- *)

let eximp x th =
  let p,q = dest_imp(concl th) in
  let th1 = contrapos(genimp x (contrapos th)) in
  end_itlist imp_trans
   [iff_imp1(axiom_exists x p); th1; iff_imp2(axiom_exists x q)];;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q[x] then |- p ==> forall x. q[x]                             *)
(* ------------------------------------------------------------------------- *)

let gen_right x th =
  let p,q = dest_imp(concl th) in
  let th1 = axiom_allimp x p q in
  let th2 = modusponens th1 (gen x th) in
  imp_trans (axiom_impall x p) th2;;

(* ------------------------------------------------------------------------- *)
(* If |- p(x) ==> q then |- (exists x. p(x)) ==> q                           *)
(* ------------------------------------------------------------------------- *)

let exists_left x th =
  let th1 = contrapos(gen_right x (contrapos th))
  and p,q = dest_imp(concl th) in
  let th2 = imp_trans (iff_imp1(axiom_exists x p)) th1 in
  imp_trans th2 (neg_neg q);;

(* ------------------------------------------------------------------------- *)
(* If |- exists x. p(x) ==> q then |- (forall x. p(x)) ==> q                 *)
(* ------------------------------------------------------------------------- *)

let exists_imp th =
  match concl th with
    Exists(x,(Imp(p,q) as pq)) ->
      let xpq = Forall(x,Not pq) and q' = Imp(q,False) in
      let th0 = iff_imp2(axiom_not pq) in
      let th1 = gen_right x (imp_trans (imp_truefalse p q) th0) in
      let th2 = imp_trans th1 (axiom_allimp x p (Not pq)) in
      let th3 = modusponens (iff_imp1(axiom_exists x pq)) th in
      let th4 = imp_trans th3 (iff_imp1(axiom_not xpq)) in
      let th5 = modusponens (imp_trans_th q' xpq False) th4 in
      imp_trans (imp_trans (imp_swap th2) th5) (axiom_doubleneg q)
  | _ -> failwith "exists_imp: wrong sort of theorem";;

(* ------------------------------------------------------------------------- *)
(* Equivalence properties of logical equivalence.                            *)
(* ------------------------------------------------------------------------- *)

let iff_refl p = let th = imp_refl p in imp_antisym th th;;

let iff_sym th =
  let p,q = dest_iff(concl th) in
  let th1 = modusponens (axiom_iffimp1 p q) th
  and th2 = modusponens (axiom_iffimp2 p q) th in
  modusponens (modusponens (axiom_impiff q p) th2) th1;;

let iff_trans_th =
  let pfn = lcfptaut <<(p <=> q) ==> (q <=> r) ==> (p <=> r)>> in
  fun p q r -> pfn(Imp(Iff(p,q),Imp(Iff(q,r),Iff(p,r))));;

let iff_trans th1 th2 =
  let p,q = dest_iff(concl th1) in
  let q,r = dest_iff(concl th2) in
  modusponens (modusponens (iff_trans_th p q r) th1) th2;;

(* ------------------------------------------------------------------------- *)
(* Congruence properties of the propositional connectives.                   *)
(* ------------------------------------------------------------------------- *)

let cong_not =
  let pfn = lcfptaut <<(p <=> p') ==> (~p <=> ~p')>> in
  fun p p' -> pfn(Imp(Iff(p,p'),Iff(Not p,Not p')));;

let cong_bin =
  let ap = <<p>>  and ap' = <<p'>>
  and aq = <<q>>  and aq' = <<q'>>
  and app' = <<p <=> p'>>  and aqq' = <<q <=> q'>>  in
  fun c p p' q q' ->
    let pat = Imp(app',Imp(aqq',Iff(c(ap,aq),c(ap',aq')))) in
    lcfptaut pat (Imp(Iff(p,p'),Imp(Iff(q,q'),Iff(c(p,q),c(p',q')))));;

(* ------------------------------------------------------------------------- *)
(* |- (forall x. P(x) <=> Q(x)) ==> ((forall x. P(x)) <=> (forall x. Q(x)))  *)
(* ------------------------------------------------------------------------- *)

let forall_iff x p q =
  imp_trans_chain
    [imp_trans (genimp x (axiom_iffimp1 p q)) (axiom_allimp x p q);
     imp_trans (genimp x (axiom_iffimp2 p q)) (axiom_allimp x q p)]
    (axiom_impiff (Forall(x,p)) (Forall(x,q)));;

(* ------------------------------------------------------------------------- *)
(* |- (forall x. P(x) <=> Q(x)) ==> ((exists x. P(x)) <=> (exists x. Q(x)))  *)
(* ------------------------------------------------------------------------- *)

let exists_iff x p q =
  let th1 = genimp x (cong_not p q) in
  let th2 = imp_trans th1 (forall_iff x (Not p) (Not q)) in
  let xnp = Forall(x,Not p) and xnq = Forall(x,Not q) in
  let th3 = imp_trans th2 (cong_not xnp xnq) in
  let th4 = iff_trans_th (Exists(x,p)) (Not xnp) (Not xnq) in
  let th5 = imp_trans th3 (modusponens th4 (axiom_exists x p)) in
  let th6 = iff_trans_th (Exists(x,p)) (Not xnq) (Exists(x,q)) in
  let th7 = modusponens (imp_swap th6) (iff_sym(axiom_exists x q)) in
  imp_trans th5 th7;;

(* ------------------------------------------------------------------------- *)
(* Substitution...                                                           *)
(* ------------------------------------------------------------------------- *)

let rec isubst s t fm =
  if not (free_in s fm) then add_assum (mk_eq s t) (iff_refl fm) else
  match fm with
    Atom(R(p,args)) ->
      if args = [] then add_assum (mk_eq s t) (iff_refl fm) else
      let ths = map (congruence s t) args in
      let lts,rts = unzip (map (dest_eq ** consequent ** concl) ths) in
      let ths' = map2 imp_trans ths (map2 eq_sym lts rts) in
      let th = imp_trans_chain ths (axiom_predcong p lts rts)
      and th' = imp_trans_chain ths' (axiom_predcong p rts lts) in
      let fm' = consequent(consequent(concl th)) in
      imp_trans_chain [th; th'] (axiom_impiff fm fm')
  | Not(p) ->
      let th = isubst s t p in
      let p' = snd(dest_iff(consequent(concl th))) in
      imp_trans th (cong_not p p')
  | And(p,q) -> isubst_binary (fun (p,q) -> And(p,q)) s t p q
  | Or(p,q) -> isubst_binary (fun (p,q) -> Or(p,q)) s t p q
  | Imp(p,q) -> isubst_binary (fun (p,q) -> Imp(p,q)) s t p q
  | Iff(p,q) -> isubst_binary (fun (p,q) -> Iff(p,q)) s t p q
  | Forall(x,p) ->
      if mem x (fvt t) then
         let z = variant x (union (fvt t) (fv p)) in
         let th1 = alpha z fm in
         let fm' = consequent(concl th1) in
         let th2 = imp_antisym th1 (alpha x fm')
         and th3 = isubst s t fm' in
         let fm'' = snd(dest_iff(consequent(concl th3))) in
         imp_trans th3 (modusponens (iff_trans_th fm fm' fm'') th2)
      else
         let th = isubst s t p in
         let p' = snd(dest_iff(consequent(concl th))) in
         imp_trans (gen_right x th) (forall_iff x p p')
  | Exists(x,p) ->
      let th0 = axiom_exists x p in
      let th1 = isubst s t (snd(dest_iff(concl th0))) in
      let Imp(_,Iff(fm',(Not(Forall(y,Not(p'))) as q))) = concl th1 in
      let th2 = imp_trans th1 (modusponens (iff_trans_th fm fm' q) th0)
      and th3 = iff_sym(axiom_exists y p') in
      let r = snd(dest_iff(concl th3)) in
      imp_trans th2 (modusponens (imp_swap(iff_trans_th fm q r)) th3)
  | _ -> add_assum (mk_eq s t) (iff_refl fm)

and isubst_binary cons s t p q =
  let th_p = isubst s t p and th_q = isubst s t q in
  let p' = snd(dest_iff(consequent(concl th_p)))
  and q' = snd(dest_iff(consequent(concl th_q))) in
  let th1 = imp_trans th_p (cong_bin cons p p' q q') in
  imp_unduplicate (imp_trans th_q (imp_swap th1))

(* ------------------------------------------------------------------------- *)
(* ...specialization...                                                      *)
(* ------------------------------------------------------------------------- *)

and ispec t fm =
  match fm with
    Forall(x,p) ->
      if mem x (fvt t) then
        let th1 = alpha (variant x (union (fvt t) (fv p))) fm in
        imp_trans th1 (ispec t (consequent(concl th1)))
      else
        let th1 = isubst (Var x) t p in
        let eq,bod = dest_imp(concl th1) in
        let p' = snd(dest_iff bod) in
        let th2 = imp_trans th1 (axiom_iffimp1 p p') in
        exists_imp(modusponens (eximp x th2) (axiom_existseq x t))
  | _ -> failwith "ispec: non-universal formula"

(* ------------------------------------------------------------------------- *)
(* ...and renaming, all mutually recursive.                                  *)
(* ------------------------------------------------------------------------- *)

and alpha z fm =
  let th1 = ispec (Var z) fm in
  let ant,cons = dest_imp(concl th1) in
  let th2 = modusponens (axiom_allimp z ant cons) (gen z th1) in
  imp_trans (axiom_impall z fm) th2;;

(* ------------------------------------------------------------------------- *)
(* Specialization rule.                                                      *)
(* ------------------------------------------------------------------------- *)

let spec t th = modusponens (ispec t (concl th)) th;;

(* ------------------------------------------------------------------------- *)
(* Tests.                                                                    *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
isubst <<|x + x|>> <<|2 * x|>> <<x + x = x + x + x>> ;;

ispec <<|y|>> <<forall x y z. x + y + z = z + y + x>> ;;

isubst <<|x + x|>> <<|2 * x|>> <<x + x = x ==> x = 0>> ;;

isubst <<|x + x|>>  <<|2 * x|>>
       <<(x + x = y + y) ==> (y + y + y = x + x + x)>> ;;

ispec <<|x|>> <<forall x y z. x + y + z = y + z + z>> ;;

ispec <<|x|>> <<forall x. x = x>> ;;

ispec <<|w + y + z|>> <<forall x y z. x + y + z = y + z + z>> ;;

ispec <<|x + y + z|>> <<forall x y z. x + y + z = y + z + z>> ;;

ispec <<|x + y + z|>> <<forall x y z. nothing_much>> ;;

isubst <<|x + x|>> <<|2 * x|>>
       <<(x + x = y + y) <=> (something \/ y + y + y = x + x + x)>> ;;

isubst <<|x + x|>>  <<|2 * x|>>
       <<(exists x. x = 2) <=> exists y. y + x + x = y + y + y>> ;;

isubst <<|x|>>  <<|y|>>
       <<(forall z. x = z) <=> (exists x. y < z) /\ (forall y. y < x)>> ;;
END_INTERACTIVE;;
