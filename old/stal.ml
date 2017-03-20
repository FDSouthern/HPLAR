(* ========================================================================= *)
(* Simple implementation of Stalmarck's algorithm.                           *)
(*                                                                           *)
(* NB! This algorithm is patented for commercial use (not that a toy version *)
(* like this would actually be useful in practice). See US patent 5 276 897, *)
(* Swedish patent 467 076 and European patent 0403 454 for example.          *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Triplet transformation, using functions defined earlier.                  *)
(* ------------------------------------------------------------------------- *)

let triplicate fm =
  let fm' = nenf(psimplify fm) in
  let n = Int 1 +/ overatoms (max_varindex "p_" ** pname) fm' (Int 0) in
  let (p,defs,_) = maincnf false (fm',undefined,n) in
  p,map (snd ** snd) (funset defs);;

(* ------------------------------------------------------------------------- *)
(* Automatically generate triggering rules to save writing them out.         *)
(* ------------------------------------------------------------------------- *)

let atom lit = if negative lit then negate lit else lit;;

let rec align (p,q) =
  if atom p < atom q then align(q,p) else
  if negative p then (negate p,negate q) else (p,q);;

let equate2 (p,q) eqv = equate (negate p,negate q) (equate (p,q) eqv);;

let rec irredundant rel eqs =
  match eqs with
    [] -> []
  | (p,q)::oth ->
      if canonize rel p = canonize rel q then irredundant rel oth
      else insert (p,q) (irredundant (equate2 (p,q) rel) oth);;

let consequences peq fm eqs =
  let pq = (fun (p,q) -> Iff(p,q)) peq in
  let raw = filter
    (fun (r,s) -> tautology(Imp(And(pq,fm),Iff(r,s)))) eqs in
  irredundant (equate2 peq unequal) raw;;

let triggers fm =
  let poslits = insert True (map (fun p -> Atom p) (atoms fm)) in
  let lits = union poslits (map (fun p -> Not p) poslits) in
  let pairs = allpairs (fun p q -> p,q) lits lits in
  let npairs = filter (fun (p,q) -> atom p <> atom q) pairs in
  let eqs = setify(map align npairs) in
  let raw = map (fun p -> p,consequences p fm eqs) eqs in
  filter (fun (p,c) -> c <> []) raw;;

(* ------------------------------------------------------------------------- *)
(* An example.                                                               *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
triggers <<p <=> (q /\ r)>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Precompute and instantiate triggers for standard triplets.                *)
(* ------------------------------------------------------------------------- *)

let ddnegate fm = match fm with Not(Not p) -> p | _ -> fm;;

let trigger =
  let [trig_and; trig_or; trig_imp; trig_iff] =
    map triggers
      [<<p <=> q /\ r>>; <<p <=> q \/ r>>;
       <<p <=> (q ==> r)>>; <<p <=> (q <=> r)>>]
  and p = <<p>> and q = <<q>> and r = <<r>> in
  let inst_fn [x;y;z] =
    let subfn = fpf [P"p" |-> x; P"q" |-> y; P"r" |-> z] in
    ddnegate ** propsubst subfn in
  let inst2_fn i (p,q) = align(inst_fn i p,inst_fn i q) in
  let instn_fn i (a,c) = inst2_fn i a,map (inst2_fn i) c in
  let inst_trigger = map ** instn_fn in
  function (Iff(x,And(y,z))) -> inst_trigger [x;y;z] trig_and
         | (Iff(x,Or(y,z))) -> inst_trigger [x;y;z] trig_or
         | (Iff(x,Imp(y,z))) -> inst_trigger [x;y;z] trig_imp
         | (Iff(x,Iff(y,z))) -> inst_trigger [x;y;z] trig_iff;;

(* ------------------------------------------------------------------------- *)
(* Finding variables in triggers, prioritized by fecundity estimate.         *)
(* ------------------------------------------------------------------------- *)

let rec fecundity ((p,q),conseqs) f =
  let vars = union (atoms p) (atoms q) in
  let n = (if atom q = True then 2 else 1) * length conseqs in
  itlist (fun x -> (x |-> n + tryapplyd f x 0)) vars f;;

let variable_list trigs =
  let fec = itlist fecundity trigs undefined in
  let repcounts = funset fec in
  map (fun (p,q) -> Atom p)
      (sort (fun (_,n) (_,m) -> m <= n) repcounts);;

(* ------------------------------------------------------------------------- *)
(* Compute a function mapping each variable/true to relevant triggers.       *)
(* ------------------------------------------------------------------------- *)

let insert_relevant p trg f = (p |-> insert trg (tryapplyl f p)) f;;

let insert_relevant2 ((p,q),_ as trg) f =
  insert_relevant p trg (insert_relevant q trg f);;

let relevance trigs =
  let vars = variable_list trigs
  and rfn = itlist insert_relevant2 trigs undefined in
  vars,rfn;;

(* ------------------------------------------------------------------------- *)
(* Merging of equiv classes and relevancies.                                 *)
(* ------------------------------------------------------------------------- *)

let equatecons (p0,q0) (eqv,rfn as erf) =
  let p = canonize eqv p0
  and q = canonize eqv q0 in
  if p = q then [],erf else
  let p' = canonize eqv (negate p0)
  and q' = canonize eqv (negate q0) in
  let eqv' = equate2(p,q) eqv
  and sp_pos = tryapplyl rfn p
  and sp_neg = tryapplyl rfn p'
  and sq_pos = tryapplyl rfn q
  and sq_neg = tryapplyl rfn q' in
  let rfn' = itlist identity
    [canonize eqv' p |-> union sp_pos sq_pos;
     canonize eqv' p' |-> union sp_neg sq_neg] rfn in
  let nw = union (intersect sp_pos sq_pos) (intersect sp_neg sq_neg) in
  itlist (union ** snd) nw [],(eqv',rfn');;

(* ------------------------------------------------------------------------- *)
(* Zero-saturation given an equivalence/relevance and new assignments.       *)
(* ------------------------------------------------------------------------- *)

let rec zero_saturate erf assigs =
  match assigs with
    [] -> erf
  | (p,q)::ts ->
      let news,erf' = equatecons (p,q) erf in
      zero_saturate erf' (union ts news);;

(* ------------------------------------------------------------------------- *)
(* Zero-saturate then check for contradictoriness.                           *)
(* ------------------------------------------------------------------------- *)

let contraeq pfn =
  let vars = filter positive (equated pfn) in
  exists (fun x -> canonize pfn x = canonize pfn (Not x)) vars;;

let zero_saturate_and_check erf trigs =
  let (eqv',rfn' as erf') = zero_saturate erf trigs in
  if contraeq eqv' then snd(equatecons (True,Not True) erf') else erf';;

(* ------------------------------------------------------------------------- *)
(* Iterated equivalening over a set.                                         *)
(* ------------------------------------------------------------------------- *)

let rec equateset s0 eqfn =
  match s0 with
    a::(b::s2 as s1) ->
      equateset s1 (snd(equatecons (a,b) eqfn))
  | _ -> eqfn;;

(* ------------------------------------------------------------------------- *)
(* Intersection operation on equivalence classes and relevancies.            *)
(* ------------------------------------------------------------------------- *)

let rec inter els (eq1,_ as erf1) (eq2,_ as erf2) rev1 rev2 erf =
  match els with
    [] -> erf
  | x::xs ->
      let (b1,n1) = tryterminus eq1 x
      and (b2,n2) = tryterminus eq2 x in
      let s1 = apply rev1 b1 and s2 = apply rev2 b2 in
      let s = intersect s1 s2 in
      inter (subtract xs s) erf1 erf2 rev1 rev2
            (if s = [x] then erf else equateset s erf);;

(* ------------------------------------------------------------------------- *)
(* Reverse the equivalence mappings.                                         *)
(* ------------------------------------------------------------------------- *)

let reverseq domain eqv =
  let al = map (fun x -> x,canonize eqv x) domain in
  itlist (fun (y,x) f -> (x |-> insert y (tryapplyl f x)) f)
         al undefined;;

(* ------------------------------------------------------------------------- *)
(* Special intersection taking contradictoriness into account.               *)
(* ------------------------------------------------------------------------- *)

let truefalse pfn = canonize pfn (Not True) = canonize pfn True;;

let stal_intersect (eq1,_ as erf1) (eq2,_ as erf2) erf =
  if truefalse eq1 then erf2
  else if truefalse eq2 then erf1 else
  let dom1 = equated eq1 and dom2 = equated eq2 in
  let comdom = intersect dom1 dom2 in
  let rev1 = reverseq dom1 eq1 and rev2 = reverseq dom2 eq2 in
  inter comdom erf1 erf2 rev1 rev2 erf;;

(* ------------------------------------------------------------------------- *)
(* General n-saturation for n >= 1                                           *)
(* ------------------------------------------------------------------------- *)

let saturate allvars =
  let rec saturate n erf assigs =
    let (eqv',_ as erf') = zero_saturate_and_check erf assigs in
    if n = 0 or truefalse eqv' then erf' else
    let (eqv'',_ as erf'') = splits n erf' allvars in
    if eqv'' = eqv' then erf''
    else saturate n erf'' []
  and splits n (eqv,_ as erf) vars =
    match vars with
      [] -> erf
    | p::ovars ->
          if canonize eqv p <> p then splits n erf ovars else
          let erf0 = saturate (n - 1) erf [p,Not True]
          and erf1 = saturate (n - 1) erf [p,True] in
          let (eqv',_ as erf') = stal_intersect erf0 erf1 erf in
          if truefalse eqv' then erf'
          else splits n erf' ovars in
  saturate;;

(* ------------------------------------------------------------------------- *)
(* Cleaning up the triggers to represent the equivalence relation.           *)
(* ------------------------------------------------------------------------- *)

let minatom fms =
  match fms with
    fm::ofms ->
      itlist (fun x y -> if atom x < atom y then x else y) ofms fm
  | _ -> failwith "minatom: empty list";;

let realcanon eqv =
  let domain = equated eqv in
  let rev = reverseq domain eqv in
  itlist (fun x -> (x |-> minatom(apply rev (canonize eqv x)))) domain
         undefined;;

let substitute eqv =
  let cfn = tryapply(realcanon eqv) in
  fun (p,q) -> align(cfn p,cfn q);;

let rec cleanup subfn trigs =
  match trigs with
    [] -> []
  | ((p,q),conseqs)::otr ->
        let (p',q') = subfn (p,q) in
        if p' = q' or p = negate q' then cleanup subfn otr else
        let conseqs' = map subfn conseqs in
        let useful,triv =
           partition (fun (p,q) -> atom p <> atom q) conseqs' in
        let news =
          if exists (fun (p,q) -> p = negate q) triv
          then (p',q'),[align(True,Not True)]
          else (p',q'),useful in
        insert news (cleanup subfn otr);;

(* ------------------------------------------------------------------------- *)
(* Saturate up to a limit.                                                   *)
(* ------------------------------------------------------------------------- *)

let rec saturate_upto n m trigs assigs =
  if n > m then
   (print_string("%%% Too deep for "^(string_of_int m)^"-saturation");
    print_newline();
    false)
  else
   (print_string("*** Starting "^(string_of_int n)^"-saturation");
    print_newline();
    let vars,rfn = relevance trigs in
    let (eqv',rfn') = saturate vars n (unequal,rfn) assigs in
    if truefalse eqv' then true else
    let trigs' = cleanup (substitute eqv') trigs in
    saturate_upto (n + 1) m trigs' []);;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let include_trigger (eq,conseqs) f =
  (eq |-> union conseqs (tryapplyl f eq)) f;;

let stalmarck fm =
  let fm' = psimplify(Not fm) in
  if fm' = False then true else if fm' = True then false else
  let p,triplets = triplicate fm' in
  let trigfn = itlist (itlist include_trigger ** trigger)
                      triplets undefined in
  saturate_upto 0 2 (funset trigfn) [p,True];;

(* ------------------------------------------------------------------------- *)
(* Try the primality examples.                                               *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;

do_list (time stalmarck)
  [prime 5;
   prime 13;
   prime 23;
   prime 43;
   prime 97];;

END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Artifical example of Urquhart formulas.                                   *)
(* ------------------------------------------------------------------------- *)

let urquhart n =
  let pvs = map (fun n -> Atom(P("p_"^(string_of_int n)))) (1 -- n) in
  end_itlist (fun p q -> Iff(p,q)) (pvs @ pvs);;

START_INTERACTIVE;;
map (time stalmarck ** urquhart) [1;2;4;8;16];;

END_INTERACTIVE;;
