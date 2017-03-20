(* ========================================================================= *)
(* Propositional reasoning by derived rules atop the LCF core.               *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

let dest_iff fm =
  match fm with
    Iff(p,q) -> (p,q)
  | _ -> failwith "dest_iff: not an equivalence";;

let dest_and fm =
  match fm with
    And(p,q) -> (p,q)
  | _ -> failwith "dest_and: not a conjunction";;

let consequent = snd ** dest_imp;;
let antecedent = fst ** dest_imp;;

(* ------------------------------------------------------------------------- *)
(* If |- q then |- p ==> q                                                   *)
(* ------------------------------------------------------------------------- *)

let add_assum p th = modusponens (axiom_addimp (concl th) p) th;;

(* ------------------------------------------------------------------------- *)
(* If |- q ==> r then |- (p ==> q) ==> (p ==> r)                             *)
(* ------------------------------------------------------------------------- *)

let imp_add_assum p th =
  let (q,r) = dest_imp(concl th) in
  modusponens (axiom_distribimp p q r) (add_assum p th);;

(* ------------------------------------------------------------------------- *)
(* If |- p1 ==> .. ==> pn ==> q & |- q ==> r then |- p1 ==> .. ==> pn ==> r  *)
(* ------------------------------------------------------------------------- *)

let imp_trans =
  let rec break s q =
    if s = q then [] else let p,t = dest_imp s in p::(break t q) in
  fun th1 th2 ->
    let q = antecedent(concl th2) in
    let ps = break (concl th1) q in
    modusponens (itlist imp_add_assum ps th2) th1;;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> r then |- p ==> q ==> r                                       *)
(* ------------------------------------------------------------------------- *)

let imp_insert q th =
  let (p,r) = dest_imp(concl th) in
  imp_trans th (axiom_addimp r q);;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q ==> r then |- q ==> p ==> r                                 *)
(* ------------------------------------------------------------------------- *)

let imp_swap th =
  let p,qr = dest_imp(concl th) in
  let q,r = dest_imp qr in
  imp_trans (axiom_addimp q p)
            (modusponens (axiom_distribimp p q r) th);;

(* ------------------------------------------------------------------------- *)
(* |- p ==> p                                                                *)
(* ------------------------------------------------------------------------- *)

let imp_refl p =
  modusponens (modusponens (axiom_distribimp p (Imp(p,p)) p)
                           (axiom_addimp p (Imp(p,p))))
              (axiom_addimp p p);;

(* ------------------------------------------------------------------------- *)
(* |- (q ==> r) ==> (p ==> q) ==> (p ==> r)                                  *)
(* ------------------------------------------------------------------------- *)

let imp_trans_th p q r =
   imp_trans (axiom_addimp (Imp(q,r)) p)
             (axiom_distribimp p q r);;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q then |- (q ==> r) ==> (p ==> r)                             *)
(* ------------------------------------------------------------------------- *)

let imp_add_concl r th =
  let (p,q) = dest_imp(concl th) in
  modusponens (imp_swap(imp_trans_th p q r)) th;;

(* ------------------------------------------------------------------------- *)
(* |- (p ==> q ==> r) ==> (q ==> p ==> r)                                    *)
(* ------------------------------------------------------------------------- *)

let imp_swap_th p q r =
  imp_trans (axiom_distribimp p q r)
            (imp_add_concl (Imp(p,r)) (axiom_addimp q p));;

(* ------------------------------------------------------------------------- *)
(* Mappings between |- p <=> q, |- p ==> q and |- q ==> p                    *)
(* ------------------------------------------------------------------------- *)

let iff_imp1 th =
  let (p,q) = dest_iff(concl th) in
  modusponens (axiom_iffimp1 p q) th;;

let iff_imp2 th =
  let (p,q) = dest_iff(concl th) in
  modusponens (axiom_iffimp2 p q) th;;

let imp_antisym th1 th2 =
  let (p,q) = dest_imp(concl th1) in
  modusponens (modusponens (axiom_impiff p q) th1) th2;;

(* ------------------------------------------------------------------------- *)
(* |- p ==> q ==> p /\ q                                                     *)
(* ------------------------------------------------------------------------- *)

let and_pair p q =
  let th1 = iff_imp2(axiom_and p q)
  and th2 = imp_swap_th (Imp(p,Imp(q,False))) q False in
  let th3 = imp_add_assum p (imp_trans th2 th1) in
  modusponens th3 (imp_swap (imp_refl (Imp(p,Imp(q,False)))));;

(* ------------------------------------------------------------------------- *)
(* |- p /\ q ==> p                                                           *)
(* ------------------------------------------------------------------------- *)

let and_left p q =
  let th1 = imp_add_assum p (axiom_addimp False q) in
  let th2 = imp_trans (imp_add_concl False th1) (axiom_doubleneg p) in
  imp_trans (iff_imp1(axiom_and p q)) th2;;

(* ------------------------------------------------------------------------- *)
(* |- p /\ q ==> q                                                           *)
(* ------------------------------------------------------------------------- *)

let and_right p q =
  let th1 = axiom_addimp (Imp(q,False)) p in
  let th2 = imp_trans (imp_add_concl False th1) (axiom_doubleneg q) in
  imp_trans (iff_imp1(axiom_and p q)) th2;;

(* ------------------------------------------------------------------------- *)
(* |- p1 /\ ... /\ pn ==> pi for each 1 <= i <= n (input term right assoc)   *)
(* ------------------------------------------------------------------------- *)

let rec conjths fm =
  try let p,q = dest_and fm in
      (and_left p q)::map (imp_trans (and_right p q)) (conjths q)
  with Failure _ -> [imp_refl fm];;

(* ------------------------------------------------------------------------- *)
(* |- false ==> p                                                            *)
(* ------------------------------------------------------------------------- *)

let ex_falso p =
  imp_trans (axiom_addimp False (Imp(p,False))) (axiom_doubleneg p);;

(* ------------------------------------------------------------------------- *)
(* |- (q ==> false) ==> p ==> (p ==> q) ==> false                            *)
(* ------------------------------------------------------------------------- *)

let imp_truefalse p q =
  imp_trans (imp_trans_th p q False) (imp_swap_th (Imp(p,q)) p False);;

(* ------------------------------------------------------------------------- *)
(* |- true                                                                   *)
(* ------------------------------------------------------------------------- *)

let truth = modusponens (iff_imp2 axiom_true) (imp_refl False);;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> p ==> q then |- p ==> q                                       *)
(* ------------------------------------------------------------------------- *)

let imp_unduplicate th =
  let p,pq = dest_imp(concl th) in
  let q = consequent pq in
  modusponens (modusponens (axiom_distribimp p p q) th) (imp_refl p);;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> qi for 1<=i<=n and |- q1 ==> ... ==> qn ==> r then |- p ==> r *)
(* ------------------------------------------------------------------------- *)

let imp_trans_chain ths th =
  itlist (fun a b -> imp_unduplicate (imp_trans a (imp_swap b)))
         (rev(tl ths)) (imp_trans (hd ths) th);;

(* ------------------------------------------------------------------------- *)
(* |- (p <=> q) <=> (p ==> q) /\ (q ==> p)                                   *)
(* ------------------------------------------------------------------------- *)

let iff_expand p q =
  let pq = Imp(p,q) and qp = Imp(q,p) in
  let th1 = and_pair pq qp and th2 = axiom_impiff p q in
  imp_antisym
   (imp_trans_chain [axiom_iffimp1 p q; axiom_iffimp2 p q] th1)
   (imp_trans_chain [and_left pq qp; and_right pq qp] th2);;

(* ------------------------------------------------------------------------- *)
(* Recursively evaluate expression.                                          *)
(* ------------------------------------------------------------------------- *)

let rec peval cnj ths fmp =
  match fmp with
    False,False -> add_assum cnj (imp_refl False)
  | True,True -> add_assum cnj truth
  | Imp(p0,q0),Imp(p,q) ->
        let pth = peval cnj ths (p0,p)
        and qth = peval cnj ths (q0,q) in
        if consequent(concl qth) = q then
          imp_insert p qth
        else if consequent(concl pth) = Imp(p,False) then
          imp_trans pth (ex_falso q)
        else
          let th1 = imp_trans qth (imp_truefalse p q) in
          let th2 = axiom_distribimp cnj p (Imp(Imp(p,q),False)) in
          modusponens (modusponens th2 th1) pth
  | Not(p0),Not(p) ->
        repeval cnj ths (axiom_not p) (axiom_not p0)
  | Or(p0,q0),Or(p,q) ->
        repeval cnj ths (axiom_or p q) (axiom_or p0 q0)
  | And(p0,q0),And(p,q) ->
        repeval cnj ths (axiom_and p q) (axiom_and p0 q0)
  | Iff(p0,q0),Iff(p,q) ->
        repeval cnj ths (iff_expand p q) (iff_expand p0 q0)
  | _,fm ->
        try find (fun th -> consequent(concl th) = fm) ths
        with Failure _ -> try
            find (fun th -> consequent(concl th) = Imp(fm,False)) ths
        with Failure _ -> failwith "no assignment for atom"

and repeval cnj ths th th0 =
  let (old,nw) = dest_iff(concl th)
  and nw0 = snd(dest_iff(concl th0)) in
  let eth = peval cnj ths (nw0,nw) in
  if consequent(concl eth) = nw then imp_trans eth (iff_imp2 th)
  else imp_trans eth (imp_add_concl False (iff_imp1 th));;

(* ------------------------------------------------------------------------- *)
(* If |- p /\ q ==> r then |- p ==> q ==> r                                  *)
(* ------------------------------------------------------------------------- *)

let shunt th =
  let p,q = dest_and(antecedent(concl th)) in
  modusponens (itlist imp_add_assum [p;q] th) (and_pair p q);;

(* ------------------------------------------------------------------------- *)
(* If |- (p ==> false) ==> p then |- p                                       *)
(* ------------------------------------------------------------------------- *)

let contrad th =
  let p = consequent(concl th) in
  let p' = Imp(p,False) in
  let th1 = modusponens (axiom_distribimp p' p False) (imp_refl p') in
  modusponens (axiom_doubleneg p) (modusponens th1 th);;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q and |- (p ==> false) ==> q then |- q                        *)
(* ------------------------------------------------------------------------- *)

let bool_cases th1 th2 =
  contrad(imp_trans (imp_add_concl False th1) th2);;

(* ------------------------------------------------------------------------- *)
(* Collect the atoms (including quantified subformulas).                     *)
(* ------------------------------------------------------------------------- *)

let rec patoms fmp =
  match fmp with
    False,False -> []
  | True,True -> []
  | Not(p0),Not(p) -> patoms (p0,p)
  | And(p0,q0),And(p,q) -> union (patoms (p0,p)) (patoms (q0,q))
  | Or(p0,q0),Or(p,q) -> union (patoms (p0,p)) (patoms (q0,q))
  | Imp(p0,q0),Imp(p,q) -> union (patoms (p0,p)) (patoms (q0,q))
  | Iff(p0,q0),Iff(p,q) -> union (patoms (p0,p)) (patoms (q0,q))
  | _,fm -> [fm];;

(* ------------------------------------------------------------------------- *)
(* Prove tautology using pattern term to identify atoms.                     *)
(*                                                                           *)
(* Essentially implements Kalmar's completeness proof (in Mendelson's book). *)
(* ------------------------------------------------------------------------- *)

let lcfptaut =
  let rec splt ats asm fmp =
    match ats with
      [] -> peval asm (conjths asm) fmp
    | a::oats ->
          bool_cases (shunt(splt oats (And(a,asm)) fmp))
                     (shunt(splt oats (And(Imp(a,False),asm)) fmp)) in
  fun pat fm ->
    let fmp = (pat,fm) in
    let th = modusponens (splt (patoms fmp) True fmp) truth in
    if concl th = fm then th else failwith "lcftaut";;

(* ------------------------------------------------------------------------- *)
(* Simple case using formula itself as a pattern.                            *)
(* ------------------------------------------------------------------------- *)

let lcftaut fm = lcfptaut fm fm;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
lcftaut <<(p ==> q) \/ (q ==> p)>>;;

lcftaut <<p /\ q <=> ((p <=> q) <=> p \/ q)>>;;

lcftaut <<((p ==> q) ==> p) ==> p>>;;

(* ------------------------------------------------------------------------- *)
(* Indication of why we sometimes need lcfptaut                              *)
(* ------------------------------------------------------------------------- *)

let fm = let p = <<a /\ b /\ c /\ d /\ e /\ f /\ g>> in Imp(p,p);;
lcftaut fm;;
lcfptaut <<p ==> p>> fm;;

(* ------------------------------------------------------------------------- *)
(* More examples/tests.                                                      *)
(* ------------------------------------------------------------------------- *)

time lcftaut <<true>>;;

time lcftaut <<false ==> (false ==> false)>>;;

time lcftaut <<p ==> p>>;;

time lcftaut <<(p ==> q) \/ (q ==> p)>>;;

time lcftaut <<(p ==> ~p) \/ p>>;;

time lcftaut <<(p <=> q) <=> (q <=> p)>>;;

time lcftaut <<p \/ (q <=> r) <=> (p \/ q <=> p \/ r)>>;;

time lcftaut <<p /\ q <=> ((p <=> q) <=> p \/ q)>>;;

time lcftaut <<p \/ (q <=> r) <=> (p \/ q <=> p \/ r)>>;;

time lcftaut <<(p ==> q) ==> (q ==> r) ==> p ==> r>>;;

time lcftaut <<((p ==> q) ==> p) ==> p>>;;

time lcftaut <<((p ==> q) ==> q) ==> (p ==> false) ==> q>>;;

time lcftaut <<((p ==> q) ==> false) ==> q ==> p>>;;

time lcftaut <<(p ==> p ==> q) ==> p ==> q>>;;

time lcftaut <<((p ==> q) ==> q) ==> (q ==> false) ==> p>>;;

time lcftaut
 <<(p ==> p) ==> (p ==> q ==> q ==> r ==> s ==> t ==> p)>>;;
END_INTERACTIVE;;
