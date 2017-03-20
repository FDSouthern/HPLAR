(* ========================================================================= *)
(* Binary decision diagrams (BDDs) using complement edges.                   *)
(*                                                                           *)
(* In practice one would use hash tables, but we use abstract finite         *)
(* partial functions here. They might also look nicer imperatively.          *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

type bddnode = prop * int * int;;

(* ------------------------------------------------------------------------- *)
(* A BDD contains a variable order, unique and computed table.               *)
(* ------------------------------------------------------------------------- *)

type bdd = Bdd of ((bddnode,int)func * (int,bddnode)func * int) *
                  (prop->prop->bool);;

let print_bdd (Bdd((unique,uback,n),ord)) =
  print_string ("<BDD with "^(string_of_int n)^" nodes>");;

START_INTERACTIVE;;
#install_printer print_bdd;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Map a BDD node back to its components.                                    *)
(* ------------------------------------------------------------------------- *)

let expand_node =
  let expand_pos (Bdd((unique,expand,_),_)) n =
    tryapplyd expand n (P"",1,1) in
  fun bdd n ->
    if n < 0 then let (s,l,r) = expand_pos bdd (-n) in (s,-l,-r)
    else expand_pos bdd n;;

(* ------------------------------------------------------------------------- *)
(* Lookup or insertion if not there in unique table.                         *)
(* ------------------------------------------------------------------------- *)

let lookup_unique (Bdd((unique,expand,n),ord) as bdd) node =
  try bdd,apply unique node with Failure _ ->
  Bdd(((node|->n) unique,(n|->node) expand,n+1),ord),n;;

(* ------------------------------------------------------------------------- *)
(* Produce a BDD node (old or new).                                          *)
(* ------------------------------------------------------------------------- *)

let mk_node bdd (s,l,r) =
  if l = r then bdd,l
  else if l < 0 then
    let bdd',n = lookup_unique bdd (s,-l,-r) in bdd',-n
  else lookup_unique bdd (s,l,r);;

(* ------------------------------------------------------------------------- *)
(* Create a new BDD with a given ordering.                                   *)
(* ------------------------------------------------------------------------- *)

let mk_bdd ord = Bdd((undefined,undefined,2),ord);;

(* ------------------------------------------------------------------------- *)
(* Extract the ordering field of a BDD.                                      *)
(* ------------------------------------------------------------------------- *)

let order (Bdd(_,ord)) =
  fun s1 s2 -> (s2 = P"" & s1 <> P"") or ord s1 s2;;

(* ------------------------------------------------------------------------- *)
(* Perform an AND operation on BDDs, maintaining canonicity.                 *)
(* ------------------------------------------------------------------------- *)

let rec bdd_and (bdd,comp as bddcomp) (m1,m2) =
  if m1 = -1 or m2 = -1 then bddcomp,-1
  else if m1 = 1 then bddcomp,m2 else if m2 = 1 then bddcomp,m1 else
  try bddcomp,apply comp (m1,m2) with Failure _ ->
  try  bddcomp,apply comp (m2,m1) with Failure _ ->
  let (s1,l1,r1) = expand_node bdd m1
  and (s2,l2,r2) = expand_node bdd m2 in
  let (s,lpair,rpair) =
      if s1 = s2 then s1,(l1,l2),(r1,r2)
      else if order bdd s1 s2 then s1,(l1,m2),(r1,m2)
      else s2,(m1,l2),(m1,r2) in
  let bddcomp1,lnew = bdd_and bddcomp lpair in
  let (bdd2,comp2),rnew = bdd_and bddcomp1 rpair in
  let bdd',n = mk_node bdd2 (s,lnew,rnew) in
  let comp' = ((m1,m2) |-> n) comp2 in (bdd',comp'),n;;

(* ------------------------------------------------------------------------- *)
(* Main formula to BDD conversion, with a store of previous subnodes.        *)
(* ------------------------------------------------------------------------- *)

let bddify subbdds =
  let rec mkbdd (bdd,comp as bddcomp) fm =
    match fm with
      False -> bddcomp,-1
    | True -> bddcomp,1
    | Atom(s) ->
       (try bddcomp,assoc s subbdds with Failure _ ->
        let bdd',n = mk_node bdd (s,1,-1) in (bdd',comp),n)
    | Not(p) -> let bdd1,n = mkbdd bddcomp p in bdd1,-n
    | And(l,r) -> let bddl,nl = mkbdd bddcomp l in
                  let bddr,nr = mkbdd bddl r in
                  bdd_and bddr (nl,nr)
    | Or(l,r) ->  mkbdd bddcomp (Not(And(Not l,Not r)))
    | Imp(l,r) -> mkbdd bddcomp (Not(And(l,Not r)))
    | Iff(l,r) -> mkbdd bddcomp (Not(And(Not(And(l,r)),
                                     Not(And(Not l,Not r))))) in
  mkbdd;;

(* ------------------------------------------------------------------------- *)
(* Test.                                                                     *)
(* ------------------------------------------------------------------------- *)

let bddtaut fm =
  let bdd = mk_bdd (fun s1 s2 -> s1 < s2) in
  snd(bddify [] (bdd,undefined) fm) = 1;;

START_INTERACTIVE;;
bddtaut (ramsey 3 3 6);;

bddtaut (prime 17);;

bddtaut (mk_adder_test 4 2);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Towards a more intelligent treatment of "definitions".                    *)
(* ------------------------------------------------------------------------- *)

let rec conjuncts fm acc =
  match fm with
   And(p,q) -> conjuncts p (conjuncts q acc)
  | _ -> insert fm acc;;

let dest_nimp fm =
  match fm with
    Imp(l,r) -> l,r
  | Not(p) -> p,False
  | _ -> failwith "dest_nimp: not an implication or negation";;

let rec dest_def fm =
  match fm with
    Iff(Atom(p),r) -> p,r
  | Iff(r,Atom(p)) -> p,r
  | _ -> failwith "not a defining equivalence";;

let restore_eqs defs fm =
  itlist (fun (p,fm) r -> Imp(Iff(Atom(p),fm),r)) defs fm;;

let rec sort_defs acc defs fm =
  if defs = [] then rev acc,fm else
  try let (p,q) = find
        (fun (p,q) -> let fvs = atoms q in
             not (exists (fun (p',_) -> mem p' fvs) defs)) defs in
      let ps,nonps = partition (fun (p',_) -> p' = p) defs in
      let ps' = subtract ps [p,q] in
      sort_defs ((p,q)::acc) nonps (restore_eqs  ps' fm)
  with Failure _ ->
      [],restore_eqs defs fm;;

(* ------------------------------------------------------------------------- *)
(* Also attempt to discover a more "topological" variable ordering.          *)
(* ------------------------------------------------------------------------- *)

let sinsert x s = if mem x s then s else x::s;;

let rec varorder pvs defs fm =
  match defs with
    [] -> rev(itlist sinsert (atoms fm) pvs)
  | ((p,q)::odefs) ->
        let pvs' = sinsert p (itlist sinsert (atoms q) pvs) in
        varorder pvs' odefs fm;;

(* ------------------------------------------------------------------------- *)
(* Improved setup.                                                           *)
(* ------------------------------------------------------------------------- *)

let rec process bdd subbdds defs fm =
  match defs with
    [] -> bddify subbdds bdd fm
  | (p,q)::odefs ->
        let bdd',b = bddify subbdds bdd q in
        process bdd' ((p,b)::subbdds) odefs fm;;

let ebddtaut fm =
  let l,r = try dest_nimp fm with Failure _ -> True,fm in
  let eqs,noneqs = partition (can dest_def) (conjuncts l []) in
  let defs,fm' = sort_defs [] (map dest_def eqs)
                         (itlist (fun l r -> Imp(l,r)) noneqs r) in
  let dvs = map fst defs in
  let vars = filter (fun v -> not(mem v dvs)) (varorder [] defs fm') in
  let bdd = mk_bdd (earlier vars) in
  snd(process (bdd,undefined) [] defs fm') = 1;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
ebddtaut (prime 101);;

ebddtaut (mk_adder_test 9 5);;

ebddtaut (mk_mult_test 7);;
END_INTERACTIVE;;
