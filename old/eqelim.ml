(* ========================================================================= *)
(* Equality elimination including Brand transformation and relatives.        *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

START_INTERACTIVE;;
(meson ** equalitize)
 <<(forall x y z. (x * y) * z = x * (y * z)) <=>
   (forall u v w x y z.
         (x * y = u) /\ (y * z = w) ==> ((x * w = v) <=> (u * z = v)))>>;;

(* ------------------------------------------------------------------------- *)
(* Example of using 3-place predicate for group theory.                      *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x. P(1,x,x)) /\
   (forall x. P(i(x),x,1)) /\
   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall x. P(x,1,x)>>;;

meson
 <<(forall x. P(1,x,x)) /\
   (forall x. P(i(x),x,1)) /\
   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall x. P(x,i(x),1)>>;;

(* ------------------------------------------------------------------------- *)
(* The x^2 = 1 implies Abelian problem.                                      *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x. P(1,x,x)) /\
   (forall x. P(x,x,1)) /\
   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)>>;;

(* ------------------------------------------------------------------------- *)
(* See how efficiency drops when we assert completeness.                     *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x. P(1,x,x)) /\
   (forall x. P(x,x,1)) /\
   (forall x y. exists z. P(x,y,z)) /\
   (forall u v w x y z. P(x,y,u) /\ P(y,z,w) ==> (P(x,w,v) <=> P(u,z,v)))
   ==> forall a b c. P(a,b,c) ==> P(b,a,c)>>;;

(* ------------------------------------------------------------------------- *)
(* Lemma for equivalence elimination.                                        *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x. R(x,x)) /\
   (forall x y. R(x,y) ==>  R(y,x)) /\
   (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z))
   <=> (forall x y. R(x,y) <=> (forall z. R(x,z) <=> R(y,z)))>>;;

(* ------------------------------------------------------------------------- *)
(* Same thing for reflexivity and transitivity without symmetry.             *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x. R(x,x)) /\
   (forall x y z. R(x,y) /\ R(y,z) ==> R(x,z))
   <=> (forall x y. R(x,y) <=> (forall z. R(y,z) ==> R(x,z)))>>;;

(* ------------------------------------------------------------------------- *)
(* And for just symmetry.                                                    *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x y. R(x,y) ==>  R(y,x)) <=>
   (forall x y. R(x,y) <=> R(x,y) /\ R(y,x))>>;;

(* ------------------------------------------------------------------------- *)
(* Show how Equiv' reduces to triviality.                                    *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x. (forall w. R'(x,w) <=> R'(x,w))) /\
   (forall x y. (forall w. R'(x,w) <=> R'(y,w))
                ==> (forall w. R'(y,w) <=> R'(x,w))) /\
   (forall x y z. (forall w. R'(x,w) <=> R'(y,w)) /\
                  (forall w. R'(y,w) <=> R'(z,w))
                  ==> (forall w. R'(x,w) <=> R'(z,w)))>>;;

(* ------------------------------------------------------------------------- *)
(* More auxiliary proofs for Brand's S and T modification.                   *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall x y. R(x,y) <=> (forall z. R'(x,z) <=> R'(y,z))) /\
   (forall x. R'(x,x))
   ==> forall x y. ~R'(x,y) ==> ~R(x,y)>>;;

meson
 <<(forall x y. R(x,y) <=> (forall z. R'(y,z) ==> R'(x,z))) /\
   (forall x. R'(x,x))
   ==> forall x y. ~R'(x,y) ==> ~R(x,y)>>;;

meson
 <<(forall x y. R(x,y) <=> R'(x,y) /\ R'(y,x))
   ==> forall x y. ~R'(x,y) ==> ~R(x,y)>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Brand's S and T modifications on clauses.                                 *)
(* ------------------------------------------------------------------------- *)

let rec modify_S cl =
  try let (s,t) = tryfind dest_eq cl in
      let eq1 = Atom(R("=",[s;t])) and eq2 = Atom(R("=",[t;s])) in
      let sub = modify_S (subtract cl [eq1]) in
      map (fun s -> eq1::s) sub @ map (fun s -> eq2::s) sub
  with Failure _ -> [cl];;

let rec modify_T cl =
  match cl with
    [] -> []
  | (Atom(R("=",[s;t])) as eq)::ps ->
        let ps' = modify_T ps in
        let w = Var(variant "w" (itlist (union ** fv) ps' (fv eq))) in
        (Not(Atom(R("=",[t;w]))))::Atom(R("=",[s;w]))::ps'
  | p::ps -> p::(modify_T ps);;

(* ------------------------------------------------------------------------- *)
(* Finding nested non-variable subterms.                                     *)
(* ------------------------------------------------------------------------- *)

let find_nonvar = find (function (Var x) -> false | _ -> true);;

let find_nestnonvar tm =
  match tm with
    Var x -> failwith "findnvsubt"
  | Fn(f,args) -> find_nonvar args;;

let rec find_nvsubterm fm =
  match fm with
    Atom(R("=",[s;t])) -> tryfind find_nestnonvar [s;t]
  | Atom(R(p,args)) -> find_nonvar args
  | Not p -> find_nvsubterm p;;

(* ------------------------------------------------------------------------- *)
(* Replacement (substitution for non-variable) in term and literal.          *)
(* ------------------------------------------------------------------------- *)

let rec replacet rfn tm =
  try apply rfn tm with Failure _ ->
  match tm with
    Fn(f,args) -> Fn(f,map (replacet rfn) args)
  | _ -> tm;;

let replace rfn fm =
  onatoms (fun (R(p,a)) -> Atom(R(p,map (replacet rfn) a))) fm;;

(* ------------------------------------------------------------------------- *)
(* E-modification of a clause.                                               *)
(* ------------------------------------------------------------------------- *)

let rec emodify fvs cls =
  match cls with
    [] -> []
  | cl::ocls ->
        try let t = find_nvsubterm cl in
            let w = variant "w" fvs in
            let cls' = map (replace (t := Var w)) cls in
            emodify (w::fvs) (Not(Atom(R("=",[t;Var w])))::cls')
        with Failure _ -> cl::(emodify fvs ocls);;

let modify_E cls = emodify (itlist (union ** fv) cls []) cls;;

(* ------------------------------------------------------------------------- *)
(* Overall Brand transformation.                                             *)
(* ------------------------------------------------------------------------- *)

let brand cls =
  let cls1 = map modify_E cls in
  let cls2 = itlist (union ** modify_S) cls1 [] in
  [Atom(R("=",[Var"x";Var "x"]))]::(map modify_T cls2);;

(* ------------------------------------------------------------------------- *)
(* Incorporation into MESON.                                                 *)
(* ------------------------------------------------------------------------- *)

let bpuremeson fm =
  let cls = brand(clausal(specialize(pnf fm))) in
  let rules = itlist ((@) ** contrapositives) cls [] in
  deepen (fun n -> expand rules [] False
                     (fun x -> x) (undefined,n,0); n) 0;;

let bmeson fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (bpuremeson ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let emeson fm = meson (equalitize fm);;

let ewd =
 <<(forall x. f(x) ==> g(x)) /\
   (exists x. f(x)) /\
   (forall x y. g(x) /\ g(y) ==> x = y)
   ==> forall y. g(y) ==> f(y)>>;;

time bmeson ewd;;
time emeson ewd;;

END_INTERACTIVE;;
