(* ========================================================================= *)
(* First order logic with equality.                                          *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

let mk_eq s t = Atom(R("=",[s;t]));;

let dest_eq =
  function (Atom(R("=",[s;t]))) -> s,t
         | _ -> failwith "dest_eq: not an equation";;

(* ------------------------------------------------------------------------- *)
(* The set of predicates in a formula.                                       *)
(* ------------------------------------------------------------------------- *)

let rec predicates fm = atom_union (fun (R(p,a)) -> [p,length a]) fm;;

(* ------------------------------------------------------------------------- *)
(* Code to generate equality axioms for functions.                           *)
(* ------------------------------------------------------------------------- *)

let function_congruence (f,n) =
  if n = 0 then [] else
  let argnames_x = map (fun n -> "x"^(string_of_int n)) (1 -- n)
  and argnames_y = map (fun n -> "y"^(string_of_int n)) (1 -- n) in
  let args_x = map (fun x -> Var x) argnames_x
  and args_y = map (fun x -> Var x) argnames_y in
  let hyps = map2 (fun x y -> Atom(R("=",[x;y]))) args_x args_y in
  let ant = end_itlist (fun p q -> And(p,q)) hyps
  and con = Atom(R("=",[Fn(f,args_x); Fn(f,args_y)])) in
  [itlist (fun x p -> Forall(x,p)) (argnames_x @ argnames_y)
          (Imp(ant,con))];;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
function_congruence ("f",3);;

function_congruence ("+",2);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* And for predicates.                                                       *)
(* ------------------------------------------------------------------------- *)

let predicate_congruence (p,n) =
  if n = 0 then [] else
  let argnames_x = map (fun n -> "x"^(string_of_int n)) (1 -- n)
  and argnames_y = map (fun n -> "y"^(string_of_int n)) (1 -- n) in
  let args_x = map (fun x -> Var x) argnames_x
  and args_y = map (fun x -> Var x) argnames_y in
  let hyps = map2 (fun x y -> Atom(R("=",[x;y]))) args_x args_y in
  let ant = end_itlist (fun p q -> And(p,q)) hyps
  and con = Imp(Atom(R(p,args_x)),Atom(R(p,args_y))) in
  [itlist (fun x p -> Forall(x,p)) (argnames_x @ argnames_y)
          (Imp(ant,con))];;

(* ------------------------------------------------------------------------- *)
(* Hence implement logic with equality just by adding equality "axioms".     *)
(* ------------------------------------------------------------------------- *)

let equivalence_axioms =
  setify [<<forall x. x = x>>;
          <<forall x y z. x = y /\ x = z ==> y = z>>];;

let equalitize fm =
  let allpreds = predicates fm in
  if not (mem ("=",2) allpreds) then fm else
  let preds = subtract allpreds ["=",2]
  and funcs = functions fm in
  let axioms =
    itlist (union ** function_congruence) funcs
           (itlist (union ** predicate_congruence) preds
                   equivalence_axioms) in
  Imp(end_itlist (fun p q -> And(p,q)) axioms,fm);;

(* ------------------------------------------------------------------------- *)
(* A simple example (see EWD1266a and the application to Morley's theorem).  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;

let ewd = equalitize
 <<(forall x. f(x) ==> g(x)) /\
   (exists x. f(x)) /\
   (forall x y. g(x) /\ g(y) ==> x = y)
   ==> forall y. g(y) ==> f(y)>>;;

meson ewd;;

resolution ewd;;

splittab ewd;;

(* ------------------------------------------------------------------------- *)
(* Wishnu Prasetya's example (even nicer with an "exists unique" primitive). *)
(* ------------------------------------------------------------------------- *)

let wishnu = equalitize
 <<(exists x. x = f(g(x)) /\ forall x'. x' = f(g(x')) ==> x = x') <=>
   (exists y. y = g(f(y)) /\ forall y'. y' = g(f(y')) ==> y = y')>>;;

time meson wishnu;;

(* ------------------------------------------------------------------------- *)
(* An incestuous example used to establish completeness characterization.    *)
(* ------------------------------------------------------------------------- *)

meson
 <<(forall M p. sentence(p) ==> holds(M,p) \/ holds(M,not(p))) /\
   (forall M p. ~(holds(M,p) /\ holds(M,not(p))))
   ==> ((forall p. sentence(p)
                   ==> (forall M. models(M,S) ==> holds(M,p)) \/
                       (forall M. models(M,S) ==> holds(M,not(p)))) <=>
        (forall M M'. models(M,S) /\ models(M',S)
                      ==> forall p. sentence(p)
                                    ==> (holds(M,p) <=> holds(M',p))))>>;;

(* ------------------------------------------------------------------------- *)
(* Showing congruence closure.                                               *)
(* ------------------------------------------------------------------------- *)

let fm = equalitize
 <<forall c. f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c ==> f(c) = c>>;;

time meson fm;;

END_INTERACTIVE;;
