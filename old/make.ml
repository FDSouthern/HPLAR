(* ========================================================================= *)
(* Load theorem proving example code into OCaml toplevel.                    *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

#load "nums.cma";;                                     (* For Ocaml 3.06     *)
#load "camlp4o.cma";;                                  (* For quotations     *)

(* ------------------------------------------------------------------------- *)
(* Various small tweaks to OCAML's default state.                            *)
(* ------------------------------------------------------------------------- *)

Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };; (* Up the stack size  *)
Format.set_margin 72;;                                 (* Reduce margins     *)
open Format;;                                          (* Open formatting    *)
open Num;;                                             (* Open bignums       *)
let imperative_assign = (:=);;                         (* Preserve this      *)

let print_num n = print_string(string_of_num n);;      (* Avoid range limit  *)
#install_printer print_num;;                           (* when printing nums *)

(* ------------------------------------------------------------------------- *)
(* Bind these special identifiers to something so we can just do "#use".     *)
(* ------------------------------------------------------------------------- *)

type dummy_interactive = START_INTERACTIVE | END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Set up default quotation parsers for <<...>> and <<|...|>>.               *)
(* ------------------------------------------------------------------------- *)

let quotexpander s =
  if String.sub s 0 1 = "|" & String.sub s (String.length s - 1) 1 = "|" then
    "secondary_parser \""^
    (String.escaped (String.sub s 1 (String.length s - 2)))^"\""
  else "default_parser \""^(String.escaped s)^"\"";;

Quotation.add "" (Quotation.ExStr (fun x -> quotexpander));;

(* ------------------------------------------------------------------------- *)
(* Basic background.                                                         *)
(* ------------------------------------------------------------------------- *)

#use "lib.ml";;              (* Utility functions                            *)
#use "intro.ml";;            (* Trivial example from the introduction        *)

(* ------------------------------------------------------------------------- *)
(* General type of formulas, parser and printer (used for prop and FOL).     *)
(* ------------------------------------------------------------------------- *)

#use "formulas.ml";;

(* ------------------------------------------------------------------------- *)
(* Propositional logic.                                                      *)
(* ------------------------------------------------------------------------- *)

#use "prop.ml";;             (* Basic propositional logic stuff              *)
#use "propexamples.ml";;     (* Generate tautologies                         *)
#use "defcnf.ml";;           (* Definitional CNF                             *)
#use "dp.ml";;               (* Davis-Putnam procedure                       *)
#use "stal.ml";;             (* Stalmarck's algorithm                        *)
#use "bdd.ml";;              (* Binary decision diagrams                     *)

(* ------------------------------------------------------------------------- *)
(* First order logic.                                                        *)
(* ------------------------------------------------------------------------- *)

#use "fol.ml";;              (* Basic first order logic stuff                *)
#use "skolem.ml";;           (* Prenex and Skolem normal forms               *)
#use "herbrand.ml";;         (* Herbrand theorem and mechanization           *)
#use "unif.ml";;             (* Unification algorithm                        *)
#use "tableaux.ml";;         (* Tableaux                                     *)
#use "resolution.ml";;       (* Resolution                                   *)
#use "prolog.ml";;           (* Horn clauses and Prolog                      *)
#use "meson.ml";;            (* MESON-type model elimination                 *)
#use "skolems.ml";;          (* Skolemizing a set of formulas (theoretical)  *)

(* ------------------------------------------------------------------------- *)
(* Equality handling.                                                        *)
(* ------------------------------------------------------------------------- *)

#use "equal.ml";;            (* Naive equality axiomatization                *)
#use "cong.ml";;             (* Congruence closure                           *)
#use "rewrite.ml";;          (* Rewriting                                    *)
#use "order.ml";;            (* Simple term orderings including LPO          *)
#use "completion.ml";;       (* Knuth-Bendix completion                      *)
#use "orewrite.ml";;         (* Ordered rewriting                            *)
#use "eqelim.ml";;           (* Equality elimination: Brand transform etc.   *)
#use "paramodulation.ml";;   (* Paramodulation.                              *)

(* ------------------------------------------------------------------------- *)
(* Decidable problems.                                                       *)
(* ------------------------------------------------------------------------- *)

#use "decidable.ml";;        (* Some decidable subsets of first-order logic  *)
#use "qelim.ml";;            (* Quantifier elimination basics                *)
#use "cooper.ml";;           (* Cooper's algorithm for Presburger arith.     *)
#use "complex.ml";;          (* Complex quantifier elimination               *)
#use "grobner.ml";;          (* Grobner bases                                *)
#use "real.ml";;             (* Real quantifier elimination                  *)
#use "geom.ml";;             (* Geometry theorem proving                     *)
#use "interpolation.ml";;    (* Constructive Craig/Robinson interpolation    *)
#use "combining.ml";;        (* Combined decision procedure                  *)

(* ------------------------------------------------------------------------- *)
(* Model checking.                                                           *)
(* ------------------------------------------------------------------------- *)

#use "transition.ml";;       (* Finite state transition systems              *)
#use "temporal.ml";;         (* Linear temporal logic                        *)
#use "model.ml";;            (* CTL model checking                           *)
#use "ltl.ml";;              (* LTL decision procedure                       *)
#use "ste.ml";;              (* Symbolic trajectory evaluation               *)

(* ------------------------------------------------------------------------- *)
(* Interactive theorem proving.                                              *)
(* ------------------------------------------------------------------------- *)

#use "lcf.ml";;              (* LCF-style system for equational logic        *)
#use "hilbert.ml";;          (* Hilbert-style system for first order logic   *)
#use "lcfprop.ml";;          (* Propositional logic by inference             *)
#use "lcffol.ml";;           (* First-order reasoning by inference           *)
#use "checking.ml";;         (* Checking automatic tableau proofs in LCF     *)
#use "tactics.ml";;          (* Tactics and Mizar-style proofs               *)

(* ------------------------------------------------------------------------- *)
(* Limitations.                                                              *)
(* ------------------------------------------------------------------------- *)

#use "sigma.ml";;            (* Prover for sigma-sentences etc.              *)
#use "turing.ml";;           (* Turing machines etc.                         *)
#use "undecidable.ml";;      (* Other code related to undecidability         *)

(* ------------------------------------------------------------------------- *)
(* Further glimpses.                                                         *)
(* ------------------------------------------------------------------------- *)

(*************
#use "bhk.ml";;              (* BHK interpretation and Curry-Howard          *)
#use "many.ml";;             (* Many-sorted logic                            *)
#use "hol.ml";;              (* Higher order logic                           *)
 *************)
