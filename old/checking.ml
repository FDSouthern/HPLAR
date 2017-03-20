(* ========================================================================= *)
(* Storing proof logs for tableaux and constructing LCF proofs from them.    *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Conversionals.                                                            *)
(* ------------------------------------------------------------------------- *)

let then_conv conv1 conv2 fm =
  let th1 = conv1 fm in
  let fm1 = snd(dest_iff(concl th1)) in
  iff_trans th1 (conv2 fm1);;

let rec sub_conv conv fm =
  match fm with
  | Not(p) ->
        let pth = conv p in
        let p' = snd(dest_iff(concl pth)) in
        modusponens (cong_not p p') pth
  | And(p,q) -> binconv conv (fun (p,q) -> And(p,q)) (p,q)
  | Or(p,q) -> binconv conv (fun (p,q) -> Or(p,q)) (p,q)
  | Imp(p,q) -> binconv conv (fun (p,q) -> Imp(p,q)) (p,q)
  | Iff(p,q) -> binconv conv (fun (p,q) -> Iff(p,q)) (p,q)
  | Forall(x,p) -> quantconv conv forall_iff (x,p)
  | Exists(x,p) -> quantconv conv exists_iff (x,p)
  | _ -> iff_refl fm

and binconv conv cons (p,q) =
  let pth = conv p and qth = conv q in
  let p' = snd(dest_iff(concl pth)) and q' = snd(dest_iff(concl qth)) in
  let th = cong_bin cons p p' q q' in
  modusponens (modusponens th pth) qth

and quantconv conv crule (x,p) =
  let pth = conv p in
  let p' = snd(dest_iff(concl pth)) in
  let th = crule x p p' in
  modusponens th (gen x pth);;

(* ------------------------------------------------------------------------- *)
(* Depth conversions.                                                        *)
(* ------------------------------------------------------------------------- *)

let rec single_depth_conv conv fm =
  (then_conv (sub_conv (single_depth_conv conv)) conv) fm;;

let rec top_depth_conv conv fm =
  try then_conv conv (top_depth_conv conv) fm
  with Failure _ -> sub_conv (top_depth_conv conv) fm;;

(* ------------------------------------------------------------------------- *)
(* Aid to tautology-based simplification.                                    *)
(* ------------------------------------------------------------------------- *)

let tsimp fm fm' pat pat' = lcfptaut (Iff(pat,pat')) (Iff(fm,fm'));;

(* ------------------------------------------------------------------------- *)
(* Simplification, once and at depth, by proof.                              *)
(* ------------------------------------------------------------------------- *)

let forall_triv x p =
  imp_antisym (ispec (Var x) (Forall(x,p))) (axiom_impall x p);;

let exists_triv =
  let pfn = lcfptaut <<(p <=> ~q) ==> (q <=> ~r) ==> (p <=> r)>> in
  fun x p ->
  let th = pfn
   (Imp(Iff(Exists(x,p),Not(Forall(x,Not p))),
        Imp(Iff(Forall(x,Not p),Not p),Iff(Exists(x,p),p)))) in
  modusponens (modusponens th (axiom_exists x p))
              (forall_triv x (Not p));;

let simplify1_conv =
  let a = Atom(R("dummy",[])) in
  fun fm ->
    match fm with
      Not False -> tsimp fm True (Not False) True
    | Not True -> tsimp fm False (Not True) False
    | And(False,q) -> tsimp fm False (And(False,a)) False
    | And(p,False) -> tsimp fm False (And(a,False)) False
    | And(True,q) -> tsimp fm q (And(True,a)) a
    | And(p,True) -> tsimp fm p (And(a,True)) a
    | Or(False,q) -> tsimp fm q (Or(False,a)) a
    | Or(p,False) -> tsimp fm p (Or(a,False)) a
    | Or(True,q) -> tsimp fm True (Or(True,a)) True
    | Or(p,True) -> tsimp fm True (Or(a,True)) True
    | Imp(False,q) -> tsimp fm True (Imp(False,a)) True
    | Imp(True,q) -> tsimp fm q (Imp(True,a)) a
    | Imp(p,True) -> tsimp fm True (Imp(a,True)) True
    | Imp(p,False) -> tsimp fm (Not p) (Imp(a,False)) (Not a)
    | Iff(True,q) -> tsimp fm q (Iff(True,a)) a
    | Iff(p,True) -> tsimp fm p (Iff(a,True)) a
    | Iff(False,q) -> tsimp fm (Not q) (Iff(False,a)) (Not a)
    | Iff(p,False) -> tsimp fm (Not p) (Iff(a,False)) (Not a)
    | Forall(x,p) ->
           if mem x (fv p) then iff_refl fm else forall_triv x p
    | Exists(x,p) ->
          if mem x (fv p) then iff_refl fm else exists_triv x p
    | _ -> iff_refl fm;;

let simplify_conv = single_depth_conv simplify1_conv;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

let fm = <<forall x y. (P(x) /\ false) \/ (true ==> Q(y))>>;;

START_INTERACTIVE;;
simplify_conv fm;;

simplify fm;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Negation normal form by proof.                                            *)
(* ------------------------------------------------------------------------- *)

let not_exists =
  let pfn = lcfptaut <<(p <=> ~q) ==> (~p <=> q)>> in
  fun x p ->
    modusponens
     (pfn(Imp(Iff(Exists(x,p),Not(Forall(x,Not p))),
                  Iff(Not(Exists(x,p)),Forall(x,Not p)))))
     (axiom_exists x p);;

let not_forall =
  let pfn = lcfptaut <<~(~p) <=> p>> in
  fun x p ->
    let th1 = gen x (pfn(Iff(Not(Not p),p))) in
    let th2 = modusponens (forall_iff x (Not(Not p)) p) th1 in
    let th3 = cong_not (Forall(x,Not(Not p))) (Forall(x,p)) in
    let th4 = modusponens th3 th2 in
    iff_sym(iff_trans (axiom_exists x (Not p)) th4);;

let nnf1_conv =
  let a = Atom(R("dummy",[])) in
  fun fm ->
    match fm with
      Imp(p,q) -> tsimp fm (Or(Not p,q)) (Imp(a,a)) (Or(Not a,a))
    | Iff(p,q) -> tsimp fm (Or(And(p,q),And(Not p,Not q)))
                           (Iff(a,a)) (Or(And(a,a),And(Not a,Not a)))
    | Not(Not p) -> tsimp fm p (Not(Not a)) a
    | Not(And(p,q)) -> tsimp fm (Or(Not p,Not q))
                                (Not(And(a,a))) (Or(Not a,Not a))
    | Not(Or(p,q)) -> tsimp fm (And(Not p,Not q))
                               (Not(Or(a,a))) (And(Not a,Not a))
    | Not(Imp(p,q)) -> tsimp fm (And(p,Not q))
                                (Not(Imp(a,a))) (And(a,Not a))
    | Not(Iff(p,q)) -> tsimp fm (Or(And(p,Not q),And(Not p,q)))
                                (Not(Iff(a,a)))
                                (Or(And(a,Not a),And(Not a,a)))
    | Not(Forall(x,p)) -> not_forall x p
    | Not(Exists(x,p)) -> not_exists x p
    | _ -> failwith "nnf1_conv: no transformation";;

let nnf_conv = top_depth_conv nnf1_conv;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

let fm =
 <<(forall x. P(x)) ==> ((exists y. Q(y)) <=> exists z. P(z) /\ Q(z))>>;;

START_INTERACTIVE;;
nnf fm;;

concl (nnf_conv fm) = Iff(fm,nnf fm);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Proof format for tableaux.                                                *)
(* ------------------------------------------------------------------------- *)

type prooflog = Literal of int
              | Requeue
              | Univ of term;;

(* ------------------------------------------------------------------------- *)
(* Dummy ground term.                                                        *)
(* ------------------------------------------------------------------------- *)

let dummy = Fn("_Ground",[]);;

let rec ground tm =
  match tm with
    Var x -> dummy
  | Fn(f,args) -> Fn(f,map ground args);;

let startcont (env,k) =
  itlist (fun (x,t) -> (x|->ground t)) (funset(solve env))
         (itlist (fun i -> ("_"^string_of_int i) |-> dummy)
                 (0--k) undefined),[];;

(* ------------------------------------------------------------------------- *)
(* Tableau procedure with proof logging.                                     *)
(* ------------------------------------------------------------------------- *)

let logstep pstep (sfn,prf) = (sfn,pstep::prf);;

let logforall y (sfn,prf) = (sfn,Univ(tryapplyd sfn y (Var y))::prf);;

let rec tableau (fms,lits,n) cont (env,k) =
  if n < 0 then failwith "no proof at this level" else
  match fms with
    [] -> failwith "tableau: no proof"
  | And(p,q)::unexp ->
      tableau (p::q::unexp,lits,n) cont (env,k)
  | Or(p,q)::unexp ->
      tableau (p::unexp,lits,n) (tableau (q::unexp,lits,n) cont) (env,k)
  | Forall(x,p)::unexp ->
      let y = "_" ^ string_of_int k in
      let p' = formsubst (x := Var y) p in
      logforall y
       (tableau (p'::unexp@[Forall(x,p)],lits,n-1) cont (env,k+1))
  | fm::unexp ->
      try tryfind
           (fun l -> logstep (Literal(index l lits))
                             (cont(unify_complements env (fm,l),k)))
           lits
      with Failure _ ->
          logstep Requeue (tableau (unexp,fm::lits,n) cont (env,k));;

let tabrefute_log fms =
  deepen (fun n -> tableau (fms,[],n) startcont (undefined,0)) 0;;

(* ------------------------------------------------------------------------- *)
(* A trivial example.                                                        *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
tabrefute_log
  [<<(forall x. ~P(x) \/ P(f(x))) /\ P(1) /\ ~P(f(1))>>];;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* |- p ==> -p ==> false (p may be negated).                                 *)
(* ------------------------------------------------------------------------- *)

let imp_contrad p =
  if negative p then iff_imp1 (axiom_not (negate p))
  else imp_swap (iff_imp1 (axiom_not p));;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> q ==> r then |- p /\ q ==> r                                  *)
(* ------------------------------------------------------------------------- *)

let ante_conj th =
  let p,qr = dest_imp(concl th) in
  let q,r = dest_imp qr in
  imp_trans_chain [and_left p q; and_right p q] th;;

(* ------------------------------------------------------------------------- *)
(* If |- p ==> r and |- q ==> r then |- p \/ q ==> r                         *)
(* ------------------------------------------------------------------------- *)

let ante_disj th1 th2 =
  let p,r = dest_imp(concl th1)
  and q,s = dest_imp(concl th2) in
  let ths = map contrapos [th1; th2] in
  let th3 = imp_trans_chain ths (and_pair (Not p) (Not q)) in
  let th4 = contrapos(imp_trans (iff_imp2(axiom_not r)) th3) in
  let th5 = imp_trans(iff_imp1(axiom_or p q)) th4 in
  let th6 = imp_trans th5 (iff_imp1 (axiom_not (Imp(r,False)))) in
  imp_trans th6 (axiom_doubleneg r);;

(* ------------------------------------------------------------------------- *)
(* If |- p0 ==> ... ==> pn ==> q then |- pi ==> p0 ==> ..[no pi].. pn ==> q  *)
(* ------------------------------------------------------------------------- *)

let imp_front =
  let rec imp_front_th n fm =
    if n = 0 then imp_refl fm else
    let p1,pq = dest_imp fm in
    let th1 = imp_add_assum p1 (imp_front_th (n - 1) pq) in
    let (Imp(_,Imp(p,Imp(q,r)))) = concl th1 in
    imp_trans th1 (imp_swap_th p q r) in
  fun n th -> modusponens (imp_front_th n (concl th)) th;;

(* ------------------------------------------------------------------------- *)
(* If   |- (p0 ==> ... ==> pn ==> q)                                         *)
(* then |- (p1 ==> ... ==> p(i-1) ==> p0 ==> pi ==> ... ==> pn ==> q         *)
(* ------------------------------------------------------------------------- *)

let imp_back =
  let rec imp_back_th n fm =
    if n = 0 then imp_refl fm else
    let p0,p1q = dest_imp fm in
    let p1,pq = dest_imp p1q in
    let th1 = imp_swap_th p0 p1 pq in
    let th2 = imp_back_th (n-1) (Imp(p0,pq)) in
    imp_trans th1 (imp_add_assum p1 th2) in
  fun n th -> modusponens (imp_back_th n (concl th)) th;;

(* ------------------------------------------------------------------------- *)
(* If |- (p ==> q) ==> (q ==> r) then |- (p ==> q) ==> (p ==> r)             *)
(* ------------------------------------------------------------------------- *)

let imp_chain_imp th =
  match concl th with
    Imp(Imp(p,q),Imp(q',r)) ->
        imp_unduplicate (imp_trans th (imp_trans_th p q r))
  | _ -> failwith "imp_chain_imp: wrong kind of theorem";;

(* ------------------------------------------------------------------------- *)
(* Hack down Skolem instantiations list for existentials.                    *)
(* ------------------------------------------------------------------------- *)

let rec hack fm l =
  match fm with
    Exists(x,p) -> hack p (tl l)
  | Forall(x,p) -> hack p l
  | And(p,q) -> hack q (hack p l)
  | Or(p,q) -> hack q (hack p l)
  | _ -> l;;

(* ------------------------------------------------------------------------- *)
(* Reconstruct LCF proof from tableaux log, undoing Skolemization.           *)
(* ------------------------------------------------------------------------- *)

let rec reconstruct shyps rfn proof fms lits =
  match (proof,fms) with
    (prf,(Exists(y,p) as fm,skins)::unexp) ->
        let hfm = find (fun h -> antecedent h = fm) (hd skins) in
        let fm' = consequent hfm in
        let th1,prf' =
          reconstruct shyps rfn prf ((fm',tl skins)::unexp) lits in
        let i = length fms + length lits + index hfm shyps in
        imp_back i (imp_chain_imp (imp_front i th1)),prf'
  | (prf,(And(p,q),skins)::unexp) ->
        let th,prf' =
          reconstruct shyps rfn prf
             ((p,skins)::(q,hack p skins)::unexp) lits in
        ante_conj th,prf'
  | (prf,(Or(p,q),skins)::unexp) ->
        let thp,prf' =
          reconstruct shyps rfn prf ((p,skins)::unexp) lits in
        let thq,prf'' =
          reconstruct shyps rfn prf' ((q,hack p skins)::unexp) lits in
        ante_disj thp thq,prf''
  | (Univ(t)::prf,(Forall(x,p),skins)::unexp) ->
        let t' = replacet rfn t in
        let th1 = ispec t' (Forall(x,p)) in
        let th,prf' = reconstruct shyps rfn prf
          ((consequent(concl th1),skins)::
           unexp@[Forall(x,p),skins]) lits in
        imp_unduplicate (imp_front (length fms) (imp_trans th1 th)),prf'
  | (Literal(i)::prf,(fm,_)::unexp) ->
        let th = imp_contrad fm in
        let lits1,lits2 = chop_list i lits in
        let th1 =
          itlist imp_insert (tl lits2 @ shyps) (imp_refl False) in
        let th2 = imp_add_assum (hd lits2) th1 in
        let th3 = itlist imp_insert (map fst unexp @ lits1) th2 in
        modusponens (imp_add_assum fm th3) th,prf
  | (Requeue::prf,(fm,_)::unexp) ->
        let th,prf' =
           reconstruct shyps rfn prf unexp (fm::lits) in
        imp_front (length unexp) th,prf';;

(* ------------------------------------------------------------------------- *)
(* Remove Skolem-type hypotheses from theorem.                               *)
(* ------------------------------------------------------------------------- *)

let skoscrub th =
  match concl th with
    Imp(Imp((Exists(x,q) as p),p'),r) ->
        let [v] = subtract (fv p') (fv p) in
        let th1 = spec (Var x) (gen v th) in
        let th2 = exists_left x (imp_trans (axiom_addimp q p) th1)
        and th3 = imp_trans (imp_add_assum p (ex_falso p')) th in
        bool_cases th2 th3
  | _ -> failwith "skoscrub: no Skolem antecedent";;

(* ------------------------------------------------------------------------- *)
(* "Glass" Skolemization recording correspondences.                          *)
(* ------------------------------------------------------------------------- *)

let gaskolemize fm =
  let corr = map (fun (n,a) -> Fn(n,[]),False) (functions fm) in
  let fm',corr' = skolem fm corr in
  fm',rev(filter (fun x -> not(mem x corr)) corr');;

(* ------------------------------------------------------------------------- *)
(* Just get the existential instances from a proof.                          *)
(* ------------------------------------------------------------------------- *)

let rec exinsts proof fms lits =
  match (proof,fms) with
    (prf,(Exists(y,p),ifn,((t,fm)::osks as sks))::unexp) ->
        let p' = formsubst (y := t) p in
        let e,prf' = exinsts prf ((p',ifn,osks)::unexp) lits in
        insert (termsubst ifn t) e,prf'
  | (Univ(t)::prf,(Forall(x,p),ifn,sks)::unexp) ->
        let ifn' = (x |-> t) ifn in
        exinsts prf ((p,ifn',sks)::unexp@[Forall(x,p),ifn,sks]) lits
  | (prf,(And(p,q),ifn,sks)::unexp) ->
        exinsts prf ((p,ifn,sks)::(q,ifn,hack p sks)::unexp) (fm::lits)
  | (prf,(Or(p,q),ifn,sks)::unexp) ->
        let e1,prf' = exinsts prf ((p,ifn,sks)::unexp) lits in
        let e2,prf'' = exinsts prf' ((q,ifn,hack p sks)::unexp) lits in
        union e1 e2,prf''
  | (Literal(i)::prf,_) ->
        [],prf
  | (Requeue::prf,(fm,_,_)::unexp) ->
        exinsts prf unexp (fm::lits);;

(* ------------------------------------------------------------------------- *)
(* Set up hypotheses for Skolem functions, in left-to-right order.           *)
(* ------------------------------------------------------------------------- *)

let rec skolem_hyps rfn sks skts =
  match sks with
    [] -> []
  | (Fn(f,xs) as st,(Exists(y,q) as fm) as sk)::osks ->
        let sins,oskts = partition (fun (Fn(g,_)) -> g = f) skts in
        let mk_hyp (Fn(g,ts) as ti) =
          let ifn = itlist2 (fun (Var x) t -> x |-> t)
                            (Var y::xs) (ti ::ts)
                            undefined in
          (replace rfn (formsubst ifn (Imp(fm,q)))) in
        map mk_hyp sins :: skolem_hyps rfn osks oskts;;

(* ------------------------------------------------------------------------- *)
(* Sort Skolem hypotheses into wellfounded "term depth" order.               *)
(* ------------------------------------------------------------------------- *)

let rec sortskohyps shyps dun =
  if shyps = [] then rev dun else
  let h = find (fun h -> let p,q = dest_imp h in
                         let [v] = subtract (fv q) (fv p) in
                         not (exists (fun g -> free_in (Var v) g)
                                     (subtract shyps [h])))
               shyps in
  sortskohyps (subtract shyps [h]) (h::dun);;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let tab_rule fm0 =
  let fvs = fv fm0 in
  let fm1 = itlist (fun x p -> Forall(x,p)) fvs fm0 in
  let thn = iff_imp1((then_conv simplify_conv nnf_conv) (Not fm1)) in
  let fm = consequent(concl thn) in
  let sfm,sks = gaskolemize fm in
  let _,proof = tabrefute_log [sfm] in
  let skts,[] = exinsts proof [fm,undefined,sks] [] in
  let rfn = itlist2 (fun k t -> t |-> Var("_"^string_of_int k))
                     (1 -- length skts) skts undefined in
  let skins = skolem_hyps rfn sks skts in
  let shyps = sortskohyps(itlist (@) skins []) [] in
  let th1,[] = reconstruct shyps rfn proof [fm,skins] [] in
  let th2 = funpow (length shyps) (skoscrub ** imp_swap) th1 in
  let th3 = imp_trans (imp_trans (iff_imp2(axiom_not fm1)) thn) th2 in
  let th4 = modusponens (axiom_doubleneg fm1) th3 in
  itlist (fun x -> spec (Var x)) (rev fvs) th4;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;

let p58 = tab_rule
 <<forall P Q R. forall x. exists v. exists w. forall y. forall z.
   ((P(x) /\ Q(y)) ==> ((P(v) \/ R(w))  /\ (R(z) ==> Q(v))))>>;;

let p26 = time tab_rule
 <<((exists x. P(x)) <=> (exists x. Q(x))) /\
   (forall x y. P(x) /\ Q(y) ==> (R(x) <=> U(y))) ==>
   ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))>>;;

let p28 = time tab_rule
 <<(forall x. P(x) ==> (forall x. Q(x))) /\
   ((forall x. Q(x) \/ R(x)) ==> (exists x. Q(x) /\ R(x))) /\
   ((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) ==>
   (forall x. P(x) /\ L(x) ==> M(x))>>;;

let p33 = time tab_rule
 <<(forall x. P(a) /\ (P(x) ==> P(b)) ==> P(c)) <=>
   (forall x. P(a) ==> P(x) \/ P(c)) /\ (P(a) ==> P(b) ==> P(c))>>;;

let p35 = time tab_rule
 <<exists x y. P(x,y) ==> (forall x y. P(x,y))>>;;

let p38 = time tab_rule
 <<(forall x.
     P(a) /\ (P(x) ==> (exists y. P(y) /\ R(x,y))) ==>
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))) <=>
   (forall x.
     (~P(a) \/ P(x) \/ (exists z w. P(z) /\ R(x,w) /\ R(w,z))) /\
     (~P(a) \/ ~(exists y. P(y) /\ R(x,y)) \/
     (exists z w. P(z) /\ R(x,w) /\ R(w,z))))>>;;

let p45 = time tab_rule
 <<(forall x.
     P(x) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y)) ==>
       (forall y. G(y) /\ H(x,y) ==> R(y))) /\
   ~(exists y. L(y) /\ R(y)) /\
   (exists x. P(x) /\ (forall y. H(x,y) ==>
     L(y)) /\ (forall y. G(y) /\ H(x,y) ==> J(x,y))) ==>
   (exists x. P(x) /\ ~(exists y. G(y) /\ H(x,y)))>>;;

let davis_putnam_example = time tab_rule
 <<exists x. exists y. forall z.
        (F(x,y) ==> (F(y,z) /\ F(z,z))) /\
        ((F(x,y) /\ G(x,y)) ==> (G(x,z) /\ G(z,z)))>>;;

let gilmore_9 = time tab_rule
 <<forall x. exists y. forall z.
        ((forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x))
          ==> (forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))) /\
        ((forall u. exists v. F(x,u,v) /\ G(y,u) /\ ~H(x,y))
         ==> ~(forall u. exists v. F(x,u,v) /\ G(z,u) /\ ~H(x,z))
             ==> (forall u. exists v. F(y,u,v) /\ G(y,u) /\ ~H(y,x)) /\
                 (forall u. exists v. F(z,u,v) /\ G(y,u) /\ ~H(z,y)))>>;;

let ewd1062_1 = time tab_rule
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y))>>;;

let ewd1062_2 = time tab_rule
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> g(x) <= g(y))>>;;

(* ------------------------------------------------------------------------- *)
(* Some further examples.                                                    *)
(* ------------------------------------------------------------------------- *)

let gilmore_3 = time tab_rule
 <<exists x. forall y z.
        ((M(y,z) ==> (G(y) ==> H(x))) ==> M(x,x)) /\
        ((M(z,x) ==> G(x)) ==> H(z)) /\
        M(x,y)
        ==> M(z,z)>>;;

let gilmore_4 = time tab_rule
 <<exists x y. forall z.
        (M(x,y) ==> M(y,z) /\ M(z,z)) /\
        (M(x,y) /\ G(x,y) ==> G(x,z) /\ G(z,z))>>;;

let gilmore_5 = time tab_rule
 <<(forall x. exists y. M(x,y) \/ M(y,x)) /\
   (forall x y. M(y,x) ==> M(y,y))
   ==> exists z. M(z,z)>>;;

let gilmore_6 = time tab_rule
 <<forall x. exists y.
        (exists u. forall v. M(u,x) ==> G(v,u) /\ G(u,x))
        ==> (exists u. forall v. M(u,y) ==> G(v,u) /\ G(u,y)) \/
            (forall u v. exists w. G(v,u) \/ H(w,y,u) ==> G(u,w))>>;;

let gilmore_7 = time tab_rule
 <<(forall x. K(x) ==> exists y. L(y) /\ (M(x,y) ==> G(x,y))) /\
   (exists z. K(z) /\ forall u. L(u) ==> M(z,u))
   ==> exists v w. K(v) /\ L(w) /\ G(v,w)>>;;

let gilmore_8 = time tab_rule
 <<exists x. forall y z.
        ((M(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> M(x,x)) /\
        ((M(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\
        M(x,y)
        ==> M(z,z)>>;;

let ewd_1038' = time tab_rule
 <<(forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. x < y <=> ~(y <= x))
   ==> (forall x y z. x <= y /\ y < z ==> x < z) /\
       (forall x y z. x < y /\ y <= z ==> x < z)>>;;

END_INTERACTIVE;;
