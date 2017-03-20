(* ========================================================================= *)
(* Goals, LCF-like tactics and Mizar-like proofs.                            *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

type goals =
  Goals of ((string * fol formula) list * fol formula)list *
           (Proven.thm list -> Proven.thm);;

(* ------------------------------------------------------------------------- *)
(* Printer for goals (just shows first goal plus total number).              *)
(* ------------------------------------------------------------------------- *)

let print_goal =
  let print_hyp (l,fm) =
    open_hbox(); print_string(l^":"); print_space();
    print_formula print_atom 0 fm; print_newline(); close_box() in
  fun (Goals(gls,jfn)) ->
    match gls with
      (asl,w)::ogls ->
         print_newline();
         (if ogls = [] then print_string "1 subgoal:" else
          (print_int (length gls);
           print_string " subgoals starting with"));
         print_newline();
         do_list print_hyp (rev asl);
         print_string "---> ";
         open_hvbox 0; print_formula print_atom 0 w; close_box();
         print_newline()
    | [] -> print_string "No subgoals";;

START_INTERACTIVE;;
#install_printer print_goal;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Setting up goals and terminating them in a theorem.                       *)
(* ------------------------------------------------------------------------- *)

let set_goal fm =
  let chk th = if concl th = fm then th else failwith "wrong theorem" in
  Goals([[],fm],fun [th] -> chk(modusponens th truth));;

let extract_thm gls =
  match gls with
    Goals([],jfn) -> jfn []
  | _ -> failwith "extract_thm: unsolved goals";;

(* ------------------------------------------------------------------------- *)
(* Running a series of proof steps one by one on goals.                      *)
(* ------------------------------------------------------------------------- *)

let run prf g = itlist (fun f -> f) (rev prf) g;;

(* ------------------------------------------------------------------------- *)
(* Handy idiom for tactic that does not split subgoals.                      *)
(* ------------------------------------------------------------------------- *)

let jmodify jfn tfn ths =
  match ths with
    (th::oths) -> jfn(tfn th :: oths)
  | _ -> failwith "jmodify: no first theorem";;

(* ------------------------------------------------------------------------- *)
(* Append contextual hypothesis to unconditional theorem.                    *)
(* ------------------------------------------------------------------------- *)

let assumptate (Goals((asl,w)::gls,jfn)) th =
  add_assum (list_conj (map snd asl)) th;;

(* ------------------------------------------------------------------------- *)
(* Turn assumptions p1,...,pn into theorems |- p1 /\ ... /\ pn ==> pi        *)
(* ------------------------------------------------------------------------- *)

let rec assumps asl =
  match asl with
    [] -> []
  | [l,p] -> [l,imp_refl p]
  | (l,p)::lps ->
        let ths = assumps lps in
        let q = antecedent(concl(snd(hd ths))) in
        let rth = and_right p q in
        (l,and_left p q)::map (fun (l,th) -> l,imp_trans rth th) ths;;

let firstassum asl =
  let p = snd(hd asl) and q = list_conj(map snd (tl asl)) in
  if tl asl = [] then imp_refl p else and_left p q;;

(* ------------------------------------------------------------------------- *)
(* Another inference rule: |- P[t] ==> exists x. P[x]                        *)
(* ------------------------------------------------------------------------- *)

let right_exists x t p =
  let th1 = ispec t (Forall(x,Not p)) in
  let Not(p') = consequent(concl th1) in
  let th2 = imp_trans th1 (iff_imp1(axiom_not p')) in
  let th3 = imp_add_concl False th2 in
  let th4 = imp_trans (imp_swap(imp_refl(Imp(p',False)))) th3 in
  let th5 = imp_trans th4 (iff_imp2(axiom_not(Forall(x,Not p)))) in
  imp_trans th5 (iff_imp2(axiom_exists x p));;

(* ------------------------------------------------------------------------- *)
(* Two simple natural deduction constructs.                                  *)
(* ------------------------------------------------------------------------- *)

let fix a (Goals((asl,(Forall(x,p) as fm))::gls,jfn)) =
  if exists (mem a ** fv ** snd) asl
  then failwith "fix: variable free in assumptions" else
  let p' = formsubst(x := Var a) p in
  let jfn' = jmodify jfn
   (fun th -> imp_trans (gen_right a th) (alpha x (Forall(a,p')))) in
   Goals((asl,p')::gls,jfn');;

let take s (Goals((asl,(Exists(x,p) as fm))::gls,jfn)) =
  let t = parset s in
  let p' = formsubst(x := t) p in
  let jfn' = jmodify jfn
   (fun th -> imp_trans th (right_exists x t p)) in
  Goals((asl,p')::gls,jfn');;

(* ------------------------------------------------------------------------- *)
(* Parse a labelled formula, recognizing "thesis" and "antecedent"           *)
(* ------------------------------------------------------------------------- *)

let expand_atom thesis at =
  match at with
    R("antecedent",[]) ->
        (try fst(dest_imp thesis) with Failure _ -> Atom at)
  | R("thesis",[]) -> thesis
  | _ -> Atom at;;

let expand thesis fm = onatoms (expand_atom thesis) fm;;

(* ------------------------------------------------------------------------- *)
(* Restore old version.                                                      *)
(* ------------------------------------------------------------------------- *)

let thesis = "thesis";;

let parself (Goals((asl,w)::gls,jfn)) toks =
  match toks with
   name::":"::toks ->
      let fm,toks' = parse_formula parse_atom [] toks in
      (name,expand w fm),toks'
 | toks -> let fm,toks' = parse_formula parse_atom [] toks in
           ("",expand w fm),toks';;

let rec parselfs g toks =
  let res1,toks' = parself g toks in
  match toks' with
   "and"::toks'' ->
        let ress,toks''' = parselfs g toks'' in res1::ress,toks'''
  | _ -> [res1],toks';;

let parse_labelled_formulas g s =
  let fms,l = parselfs g (lex(explode s)) in
  let fm = end_itlist (fun p q -> And(p,q)) (map snd fms) in
  if l = [] then fms,fm
  else failwith "parse_labelled_formulas: unparsed input";;

let parse_labelled_formula g s =
  match parse_labelled_formulas g s with
    [s,p],p' -> s,p
  | _ -> failwith "too many formulas";;

(* ------------------------------------------------------------------------- *)
(* |- p1 /\ .. /\ pn ==> q to |- pi+1 /\ ... /\ pn ==> p1 /\ .. /\ pi ==> q  *)
(* ------------------------------------------------------------------------- *)

let multishunt i th =
  let th1 = funpow i (imp_swap ** shunt) th in
  let th2 = funpow (i-1) (ante_conj ** imp_front 2) (imp_swap th1) in
  imp_swap th2;;

(* ------------------------------------------------------------------------- *)
(* Add labelled formulas to the assumption list.                             *)
(* ------------------------------------------------------------------------- *)

let assume s (Goals((asl,Imp(p,q))::gls,jfn) as gl) =
  let (lps,p') = parse_labelled_formulas gl s in
  if p <> p' then failwith "assume: doesn't match antecedent" else
  let jfn' = jmodify jfn (fun th ->
    if asl = [] then add_assum True th
                else multishunt (length lps) th) in
  Goals((lps@asl,q)::gls,jfn');;

(* ------------------------------------------------------------------------- *)
(* Delayed version of tableau rule, for speed of first phase.                *)
(* ------------------------------------------------------------------------- *)

let delayed_tab_rule fm0 =
  let fvs = fv fm0 in
  let fm1 = itlist (fun x p -> Forall(x,p)) fvs fm0 in
  let fm = nnf(simplify(Not fm1)) in
  let sfm,sks = gaskolemize fm in
  let _,proof = tabrefute_log [sfm] in
  fun () ->
    let thn = iff_imp1((then_conv simplify_conv nnf_conv) (Not fm1)) in
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
(* Main automatic justification step.                                        *)
(* ------------------------------------------------------------------------- *)

let justify byfn hyps gl p =
  let ps,ths = byfn hyps p gl in
  if ps = [p] then fun () -> hd(ths()) else
  let fm = itlist (fun a b -> Imp(a,b)) ps p in
  let fn = delayed_tab_rule fm in
  fun () -> if ps = [] then assumptate gl (fn())
            else imp_trans_chain (ths()) (fn());;

(* ------------------------------------------------------------------------- *)
(* Produce canonical theorem from list of theorems or assumption labels.     *)
(* ------------------------------------------------------------------------- *)

let by hyps p (Goals((asl,w)::gls,jfn)) =
  map (fun s -> assoc s asl) hyps,
  fun () -> let ths = assumps asl in
            map (fun s -> assoc s ths) hyps;;

(* ------------------------------------------------------------------------- *)
(* Import "external" theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let using ths p g =
  let ths' = map (fun th -> itlist gen (fv(concl th)) th) ths in
  map concl ths',fun () -> map (assumptate g) ths';;

(* ------------------------------------------------------------------------- *)
(* Trivial justification, producing no hypotheses.                           *)
(* ------------------------------------------------------------------------- *)

let at once p gl = ([],fun x -> []) and once = [];;

(* ------------------------------------------------------------------------- *)
(* Main actions on canonical theorem.                                        *)
(* ------------------------------------------------------------------------- *)

let have s byfn hyps (Goals((asl,w)::gls,jfn) as gl) =
  let (l,p) = parse_labelled_formula gl s in
  let th = justify byfn hyps gl p in
  let mfn = if asl = [] then fun pth -> imp_trans (th()) pth
            else fun pth -> imp_unduplicate
                              (imp_trans (th()) (shunt pth)) in
  Goals(((l,p)::asl,w)::gls,jmodify jfn mfn);;

let case_split s byfn hyps (Goals((asl,w)::gls,jfn) as gl) =
  let (l,(Or(p,q) as fm)) = parse_labelled_formula gl s in
  let th = justify byfn hyps gl fm in
  let jfn' (pth::qth::ths) =
    let th1 = ante_disj (shunt pth) (shunt qth) in
    let th2 = imp_unduplicate(imp_trans (th()) th1) in
    jfn (th2::ths) in
  Goals(((l,p)::asl,w)::((l,q)::asl,w)::gls,jfn');;

let consider (a,s) byfn hyps (Goals((asl,w)::gls,jfn) as gl) =
  if exists (mem a ** fv) (w::map snd asl)
  then failwith "consider: variable free in assumptions" else
  let (l,p) = parse_labelled_formula gl s in
  let th = justify byfn hyps gl (Exists(a,p)) in
  let jfn' = jmodify jfn (fun pth ->
    imp_unduplicate (imp_trans (th()) (exists_left a (shunt pth)))) in
  Goals(((l,p)::asl,w)::gls,jfn');;

(* ------------------------------------------------------------------------- *)
(* Thesis modification.                                                      *)
(* ------------------------------------------------------------------------- *)

let modifythesis fm thesis =
  if fm = thesis then (True,fun fth tth -> fth) else
  match thesis with
    And(p,q) ->
        if fm <> p
        then failwith "modifythesis: doesn't match first conjunct" else
        (q,fun pth qth -> imp_trans_chain [pth; qth] (and_pair p q))
  | Iff(p,q) ->
        if fm <> Imp(p,q)
        then failwith "modifythesis: doesn't match implication" else
        (Imp(q,p),fun pth qth -> imp_trans_chain [pth; qth]
                                                 (axiom_impiff p q))
  | _ -> failwith "modifythesis: don't have anything to do";;

(* ------------------------------------------------------------------------- *)
(* Terminating steps.                                                        *)
(* ------------------------------------------------------------------------- *)

let thus s byfn hyps gl0 =
  let (Goals((asl,w)::gls,jfn) as gl) = have s byfn hyps gl0 in
  let fm = snd(hd asl) in
  let (p,rfn) = modifythesis fm w in
  Goals((asl,p)::gls,fun (pth::ths) ->
        let th = firstassum asl in jfn((rfn th pth) :: ths));;

let qed (Goals((asl,w)::gls,jfn) as gl) =
  if w <> True then failwith "qed: unproven thesis" else
  Goals(gls,fun ths -> jfn(truth :: ths));;

(* ------------------------------------------------------------------------- *)
(* The "so" continuation.                                                    *)
(* ------------------------------------------------------------------------- *)

let so cont args byfn hyps (Goals((asl,w)::gls,jfn) as gl) =
  cont args (fun hyps p g ->
          let ps,ths = byfn hyps p g in
          snd(hd asl)::ps,fun () -> firstassum asl::ths())
        hyps gl;;

let hence args byfn hyps gl = so thus args byfn hyps gl;;

(* ------------------------------------------------------------------------- *)
(* Nested sub-proof using same model.                                        *)
(* ------------------------------------------------------------------------- *)

let proof prf p (Goals((asl,w)::gls,jfn)) =
  match (run prf (Goals([asl,p],hd))) with
    Goals([],fn) -> [p],(fun () -> [fn []])
  | _ -> failwith "unsolved goals in nested proof";;

(* ------------------------------------------------------------------------- *)
(* General proof construct.                                                  *)
(* ------------------------------------------------------------------------- *)

let prove fm prf =
  let gls = run prf (set_goal fm) in
  print_string "Goals proved; reconstructing..."; print_newline();
  extract_thm gls;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
prove <<p(a) ==> (forall x. p(x) ==> p(f(x)))
        ==> exists y. p(y) /\ p(f(y))>>
      [thus thesis at once;
       qed];;

prove
 <<(forall x. x <= x) /\
   (forall x y z. x <= y /\ y <= z ==> x <= z) /\
   (forall x y. f(x) <= y <=> x <= g(y))
   ==> (forall x y. x <= y ==> f(x) <= f(y)) /\
       (forall x y. x <= y ==> g(x) <= g(y))>>
  [assume "A: antecedent";
   hence "forall x y. x <= y ==> f(x) <= f(y)" at once;
   thus thesis by ["A"];
   qed];;

prove
 <<(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x)))
   ==> exists y. p(f(f(f(f(y)))))>>
  [assume "A: exists x. p(x)";
   assume "B: forall x. p(x) ==> p(f(x))";
   have "C: forall x. p(x) ==> p(f(f(f(f(x)))))" proof
    [have "forall x. p(x) ==> p(f(f(x)))" by ["B"];
     hence thesis at once;
     qed];
   consider ("a","p(a)") by ["A"];
   take "a";
   hence thesis by ["C"];
   qed];;

END_INTERACTIVE;;
