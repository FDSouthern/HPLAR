(* ========================================================================= *)
(* Special procedures for decidable subsets of first order logic.            *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The Los example; see how Skolemized form has no non-nullary functions.    *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let los =
 <<(forall x y z. P(x,y) /\ P(y,z) ==> P(x,z)) /\
   (forall x y z. Q(x,y) /\ Q(y,z) ==> Q(x,z)) /\
   (forall x y. P(x,y) ==> P(y,x)) /\
   (forall x y. P(x,y) \/ Q(x,y))
   ==> (forall x y. P(x,y)) \/ (forall x y. Q(x,y))>>;;
skolemize(Not los);;

(* ------------------------------------------------------------------------- *)
(* The old DP procedure works.                                               *)
(* ------------------------------------------------------------------------- *)

davisputnam los;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* However, we can just form all the ground instances.                       *)
(* ------------------------------------------------------------------------- *)

let aedecide fm =
  let sfm = skolemize(Not fm) in
  let fvs = fv sfm
  and fns = functions sfm in
  let allfns =
     if exists (fun (_,ar) -> ar = 0) fns then fns
     else insert ("c",0) fns in
  let consts,funcs = partition (fun (_,ar) -> ar = 0) allfns in
  if funcs <> [] then failwith "Not decidable" else
  let cntms = smap (fun (c,_) -> Fn(c,[])) consts in
  let alltuples = groundtuples cntms [] 0 (length fvs) in
  let cjs = clausal sfm in
  let grounds = map
   (fun tup -> let inst = instantiate fvs tup in
               smap (smap (formsubst inst)) cjs) alltuples in
  not(dpll(unions grounds));;

(* ------------------------------------------------------------------------- *)
(* In this case it's quicker.                                                *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
aedecide los;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* A nicer alternative is to modify the Herbrand loop.                       *)
(* ------------------------------------------------------------------------- *)

let rec herbloop mfn tfn fl0 cntms funcs fvs n fl tried tuples =
  print_string(string_of_int(length tried)^" ground instances tried; "^
               string_of_int(length fl)^" items in list");
  print_newline();
  match tuples with
    [] -> let newtups = groundtuples cntms funcs n (length fvs) in
          if newtups = [] then false else
          herbloop mfn tfn fl0 cntms funcs fvs (n + 1) fl tried newtups
  | tup::tups ->
          let fl' = mfn fl0 (formsubst(instantiate fvs tup)) fl in
          not(tfn fl') or
          herbloop mfn tfn fl0 cntms funcs fvs n fl' (tup::tried) tups;;

(* ------------------------------------------------------------------------- *)
(* Show how we need to do PNF transformation with care.                      *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let fm = <<(forall x. p(x)) \/ (exists y. p(y))>>;;

pnf fm;;

nnf(Not(pnf(nnf(simplify los))));;

pnf(nnf(simplify(Not los)));;

(* ------------------------------------------------------------------------- *)
(* Also the group theory problem.                                            *)
(* ------------------------------------------------------------------------- *)

aedecide
 <<(forall x. P(1,x,x)) /\
   (forall x. P(x,x,1)) /\
   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)>>;;

aedecide
 <<(forall x. P(x,x,1)) /\
   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)>>;;

(* ------------------------------------------------------------------------- *)
(* A bigger example.                                                         *)
(* ------------------------------------------------------------------------- *)

let p29 =
 <<(exists x. P(x)) /\ (exists x. G(x)) ==>
   ((forall x. P(x) ==> H(x)) /\ (forall x. G(x) ==> J(x)) <=>
    (forall x y. P(x) /\ G(y) ==> H(x) /\ J(y)))>>;;

aedecide p29;;

davisputnam p29;;

(* ------------------------------------------------------------------------- *)
(* The following, however, doesn't work with aedecide.                       *)
(* ------------------------------------------------------------------------- *)

let p18 = <<exists y. forall x. P(y) ==> P(x)>>;;

(*** aedecide p18;; ***)

davisputnam p18;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Simple-minded miniscoping procedure.                                      *)
(* ------------------------------------------------------------------------- *)

let separate x cjs =
  let yes,no = partition (mem x ** fv) cjs in
  if yes = [] then list_conj no
  else if no = [] then Exists(x,list_conj yes)
  else And(Exists(x,list_conj yes),list_conj no);;

let rec pushquant x p =
  if not (mem x (fv p)) then p else
  let djs = purednf(nnf p) in
  list_disj (map (separate x) djs);;

let rec miniscope fm =
  match fm with
    Not p -> Not(miniscope p)
  | And(p,q) -> And(miniscope p,miniscope q)
  | Or(p,q) -> Or(miniscope p,miniscope q)
  | Forall(x,p) -> Not(pushquant x (Not(miniscope p)))
  | Exists(x,p) -> pushquant x (miniscope p)
  | _ -> fm;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
miniscope(nnf <<exists y. forall x. P(y) ==> P(x)>>);;

let fm = miniscope(nnf
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>);;

pnf(nnf fm);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Stronger version of "aedecide" similar to Wang's classic procedure.       *)
(* ------------------------------------------------------------------------- *)

let wang fm =
  let fm' = miniscope(nnf(simplify fm)) in aedecide fm';;

(* ------------------------------------------------------------------------- *)
(* It works well on simple monadic formulas.                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let p18 = wang
 <<exists y. forall x. P(y) ==> P(x)>>;;

let p19 = wang
 <<exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)>>;;

let p20 = wang
 <<(forall x y. exists z. forall w. P(x) /\ Q(y) ==> R(z) /\ U(w))
   ==> (exists x y. P(x) /\ Q(y)) ==> (exists z. R(z))>>;;

let p21 = wang
 <<(exists x. P ==> Q(x)) /\ (exists x. Q(x) ==> P)
   ==> (exists x. P <=> Q(x))>>;;

let p22 = wang
 <<(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))>>;;

(* ------------------------------------------------------------------------- *)
(* But not on this one!                                                      *)
(* ------------------------------------------------------------------------- *)

let p34 =
 <<((exists x. forall y. P(x) <=> P(y)) <=>
    ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>
   ((exists x. forall y. Q(x) <=> Q(y)) <=>
    ((exists x. P(x)) <=> (forall y. P(y))))>>;;

pnf(nnf(miniscope(nnf p34)));;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Checking classic Aristotelean syllogisms.                                 *)
(* ------------------------------------------------------------------------- *)

type sylltype =
   Syll_A     (* All S are P      *)
 | Syll_E     (* No S are P       *)
 | Syll_I     (* Some S are P     *)
 | Syll_O;;   (* Some S are not P *)

let syllprem ty (s,p) =
  let sx = Atom(R(s,[Var "x"])) and px = Atom(R(p,[Var "x"])) in
  match ty with
    Syll_A -> Forall("x",Imp(sx,px))
  | Syll_E -> Forall("x",Imp(sx,Not(px)))
  | Syll_I -> Exists("x",And(sx,px))
  | Syll_O -> Exists("x",And(sx,Not(px)));;

let anglicize_prem fm =
  match fm with
    Forall(_,Imp(Atom(R(s,[Var _])),Atom(R(p,[Var _])))) ->
        "all "^s^" are "^p
  | Forall(_,Imp(Atom(R(s,[Var _])),Not(Atom(R(p,[Var _]))))) ->
        "no "^s^" are "^p
  | Exists(_,And(Atom(R(s,[Var _])),Atom(R(p,[Var _])))) ->
        "some "^s^" are "^p
  | Exists(_,And(Atom(R(s,[Var _])),Not(Atom(R(p,[Var _]))))) ->
        "some "^s^" are not "^p;;

let anglicize_syllogism (Imp(And(t1,t2),t3)) =
      "If " ^ anglicize_prem t1 ^
    " and " ^ anglicize_prem t2 ^
  ", then " ^ anglicize_prem t3;;

let all_possible_syllogisms =
  let sylltypes = [Syll_A; Syll_E; Syll_I; Syll_O] in
  let prems1 = allpairs syllprem sylltypes ["M","P"; "P","M"]
  and prems2 = allpairs syllprem sylltypes ["S","M"; "M","S"]
  and prems3 = allpairs syllprem sylltypes ["S","P"] in
  allpairs (fun p12 p3 -> Imp(p12,p3))
           (allpairs (fun p1 p2 -> And(p1,p2)) prems1 prems2) prems3;;

let all_valid_syllogisms = filter aedecide all_possible_syllogisms;;

START_INTERACTIVE;;
length all_valid_syllogisms;;

map anglicize_syllogism all_valid_syllogisms;;
END_INTERACTIVE;;

let all_cond_valid_syllogisms p =
  let all_modified_syllogisms =
    map (fun q -> Imp(p,q)) all_possible_syllogisms in
  filter aedecide all_modified_syllogisms;;

START_INTERACTIVE;;
length(all_cond_valid_syllogisms <<exists x. S(x)>>);;

length(all_cond_valid_syllogisms
 <<(exists x. P(x)) /\ (exists x. M(x))>>);;

length(all_cond_valid_syllogisms
 <<(exists x. S(x)) /\ (exists x. M(x)) /\ (exists x. P(x))>>);;

length(all_cond_valid_syllogisms
 <<((forall x. P(x) ==> M(x)) ==> (exists x. P(x) /\ M(x))) /\
   ((forall x. P(x) ==> ~M(x)) ==> (exists x. P(x) /\ ~M(x))) /\
   ((forall x. M(x) ==> P(x)) ==> (exists x. M(x) /\ P(x))) /\
   ((forall x. M(x) ==> ~P(x)) ==> (exists x. M(x) /\ ~P(x))) /\
   ((forall x. S(x) ==> M(x)) ==> (exists x. S(x) /\ M(x))) /\
   ((forall x. S(x) ==> ~M(x)) ==> (exists x. S(x) /\ ~M(x))) /\
   ((forall x. M(x) ==> S(x)) ==> (exists x. M(x) /\ S(x))) /\
   ((forall x. M(x) ==> ~S(x)) ==> (exists x. M(x) /\ ~S(x)))>>);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Decide a formula on all models of size n.                                 *)
(* ------------------------------------------------------------------------- *)

let rec alltuples n l =
  if n = 0 then [[]] else
  let tups = alltuples (n - 1) l in
  allpairs (fun h t -> h::t) l tups;;

let allmappings dom ran =
  itlist (fun p -> allpairs (valmod p) ran) dom [undef];;

let alldepmappings dom ran =
  itlist (fun (p,n) -> allpairs (valmod p) (ran n)) dom [undef];;

let allfunctions dmn n = allmappings (alltuples n dmn) dmn;;

let allpredicates dmn n = allmappings (alltuples n dmn) [false;true];;

let decide_finite n fm =
  let funcs = functions fm
  and preds = predicates fm in
  let dmn = 1 -- n in
  let finterps = alldepmappings funcs (allfunctions dmn)
  and predinterps = alldepmappings preds (allpredicates dmn) in
  let interps = allpairs (fun fi pi -> Interp(dmn,fi,pi))
                         finterps predinterps in
  let fm' = generalize fm in
  forall (fun md -> holds md undefined fm') interps;;

(* ------------------------------------------------------------------------- *)
(* Decision procedure in principle for formulas with finite model property.  *)
(* ------------------------------------------------------------------------- *)

let limitedmeson n fm =
  let cls = clausal(specialize(pnf fm)) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  expand rules [] False (fun x -> x) (undefined,n,0);;

let limmeson n fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (limitedmeson n ** list_conj) (simpdnf fm1);;

let decide_fmp =
  let rec test n =
    try limmeson n fm; true with Failure _ ->
    if decide_finite n fm then test (n + 1) else false in
  test 1;;

(* ------------------------------------------------------------------------- *)
(* Semantic decision procedure for the monadic fragment.                     *)
(* ------------------------------------------------------------------------- *)

let decide_monadic fm =
  let funcs = functions fm
  and preds = predicates fm in
  let monadic,other = partition (fun (_,ar) -> ar = 1) preds in
  if funcs <> [] or exists (fun (_,ar) -> ar > 1) other
  then failwith "Not in the monadic subset" else
  let n = funpow (length monadic) (( * ) 2) 1 in
  decide_finite n fm;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
decide_monadic p34;;
END_INTERACTIVE;;
