(* ========================================================================= *)
(* Simple congruence closure.                                                *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Test whether subterms are congruent under an equivalence.                 *)
(* ------------------------------------------------------------------------- *)

let congruent eqv =
  function (Fn(f,a1),Fn(g,a2)) ->
             f = g &
             forall2 (fun s t -> canonize eqv s = canonize eqv t) a1 a2
         | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Merging of terms, with congruence closure.                                *)
(* ------------------------------------------------------------------------- *)

let rec emerge (s,t) (eqv,pfn) =
  let s' = canonize eqv s and t' = canonize eqv t in
  if s' = t' then (eqv,pfn) else
  let sp = tryapplyl pfn s' and tp = tryapplyl pfn t' in
  let eqv' = equate (s,t) eqv in
  let st' = canonize eqv' s' in
  let pfn' = (st' |-> union sp tp) pfn in
  itlist (fun (u,v) (eqv,pfn) ->
             if congruent eqv (u,v) then emerge (u,v) (eqv,pfn)
             else eqv,pfn)
         (allpairs (fun u v -> (u,v)) sp tp) (eqv',pfn');;

(* ------------------------------------------------------------------------- *)
(* Useful auxiliary functions.                                               *)
(* ------------------------------------------------------------------------- *)

let rec subterms tm acc =
  match tm with
    Var x -> tm::acc
  | Fn(f,args) -> tm::(itlist subterms args acc);;

let successors = function (Fn(f,args)) -> setify args | _ -> [];;

(* ------------------------------------------------------------------------- *)
(* Satisfiability of conjunction of ground equations and inequations.        *)
(* ------------------------------------------------------------------------- *)

let ccsatisfiable fms =
  let pos,neg = partition positive fms in
  let eqps = map dest_eq pos and eqns = map (dest_eq ** negate) neg in
  let lrs = map fst eqps @ map snd eqps @ map fst eqns @ map snd eqns in
  let tms = setify (itlist subterms lrs []) in
  let pfn = itlist
   (fun x -> itlist (fun y f -> (y |-> insert x (tryapplyl f y)) f)
                    (successors x)) tms undefined in
  let eqv,_ = itlist emerge eqps (unequal,pfn) in
  forall (fun (l,r) -> canonize eqv l <> canonize eqv r) eqns;;

(* ------------------------------------------------------------------------- *)
(* Convert uninterpreted predicates into functions.                          *)
(* ------------------------------------------------------------------------- *)

let atomize fm =
  let preds = predicates fm and funs = functions fm in
  let n = Int 1 +/ itlist (max_varindex "P" ** fst) funs (Int 0) in
  let preds' = map (fun i -> "P_"^string_of_num i)
                   (n---(n+/Int(length preds))) in
  let alist = zip preds (butlast preds') and tr = Fn(last preds',[]) in
  let equalize(R(p,args) as at) =
    if p = "=" & length args = 2 then Atom at else
    Atom(R("=",[Fn(assoc (p,length args) alist,args); tr])) in
  onatoms equalize fm;;

(* ------------------------------------------------------------------------- *)
(* Validity checking a universal formula (this theory is trivially convex).  *)
(* ------------------------------------------------------------------------- *)

let ccvalid fm =
  let fms = simpdnf(askolemize(Not(generalize(atomize fm)))) in
  not (exists ccsatisfiable fms);;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let fm =
 <<f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c
   ==> f(c) = c \/ f(g(c)) = g(f(c))>> in
ccvalid fm;;

let fm = <<f(f(f(f(c)))) = c /\ f(f(c)) = c ==> f(c) = c>> in
ccvalid fm;;

let fm =
 <<f(f(f(f(f(f(f(f(f(f(f(f(f(f(f(c))))))))))))))) = c /\
  f(f(f(f(c)))) = c
  ==> f(c) = c>> in
ccvalid fm;;

let fm =
 <<f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c /\ (P(c) <=> ~Q(f(c)))
   ==> P(f(c)) \/ Q(c)>> in
ccvalid fm;;

END_INTERACTIVE;;
