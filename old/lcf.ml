(* ========================================================================= *)
(* Simple example of LCF-style prover: equational logic via Birkhoff rules.  *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

let default_parser = parse;;

(* ------------------------------------------------------------------------- *)
(* LCF realization of Birkhoff-style rules for equational logic.             *)
(* ------------------------------------------------------------------------- *)

module type Birkhoff =
   sig type thm
       val axiom : fol formula -> thm
       val inst : (string, term) func -> thm -> thm
       val refl : term -> thm
       val sym : thm -> thm
       val trans : thm -> thm -> thm
       val cong : string -> thm list -> thm
       val dest_thm : thm -> fol formula list * fol formula
   end;;

module Proveneq : Birkhoff =
  struct
    type thm = fol formula list * fol formula
    let axiom p =
      match p with
        Atom(R("=",[s;t])) -> ([p],p)
      | _ -> failwith "axiom: not an equation"
    let inst i (asm,p) = (asm,formsubst i p)
    let refl t = ([],Atom(R("=",[t;t])))
    let sym (asm,Atom(R("=",[s;t]))) = (asm,Atom(R("=",[t;s])))
    let trans (asm1,Atom(R("=",[s;t]))) (asm2,Atom(R("=",[t';u]))) =
      if t' = t then (union asm1 asm2,Atom(R("=",[s;u])))
      else failwith "trans: theorems don't match up"
    let cong f ths =
      let asms,eqs =
        unzip(map (fun (asm,Atom(R("=",[s;t]))) -> asm,(s,t)) ths) in
      let ls,rs = unzip eqs in
      (unions asms,Atom(R("=",[Fn(f,ls);Fn(f,rs)])))
    let dest_thm th = th
  end;;

(* ------------------------------------------------------------------------- *)
(* Printer.                                                                  *)
(* ------------------------------------------------------------------------- *)

open Proveneq;;

let print_thm th =
  let asl,c = dest_thm th in
  open_box 0;
  if asl = [] then () else
  (print_formula print_atom 0 (hd asl);
   do_list (fun a -> print_string ","; print_space();
                     print_formula print_atom 0 a)
           (tl asl));
  print_space(); print_string "|- ";
  open_box 0; print_formula print_atom 0 c; close_box();
  close_box();;

START_INTERACTIVE;;
#install_printer print_thm;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Using it to do a group theory example "manually".                         *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let group_1 = axiom <<x * (y * z) = (x * y) * z>>;;
let group_2 = axiom <<1 * x = x>>;;
let group_3 = axiom <<i(x) * x = 1>>;;

let th1 = inst ("x" := <<|x * i(x)|>>) (sym group_2)
and th2 = cong "*" [inst ("x" := <<|i(x)|>>) (sym group_3);
                    refl <<|x * i(x)|>>]
and th3 = inst (instantiate ["x"; "y"; "z"]
                   [<<|i(i(x))|>>; <<|i(x)|>>; <<|x * i(x)|>>])
               (sym group_1)
and th4 =
  trans (inst (instantiate ["x"; "y"; "z"]
                   [<<|i(x)|>>; <<|x|>>; <<|i(x)|>>])
              group_1)
        (trans (cong "*" [group_3; refl <<|i(x)|>>])
               (inst ("x" := <<|i(x)|>>) group_2))
and th5 = inst ("x" := <<|i(x)|>>) group_3 in
end_itlist trans
 [th1; th2; th3; cong "*" [refl <<|i(i(x))|>>; th4]; th5];;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Trivial example of a derived rule.                                        *)
(* ------------------------------------------------------------------------- *)

let lcong t th = cong "*" [th; refl t];;

let rcong t th = cong "*" [refl t; th];;

(* ------------------------------------------------------------------------- *)
(* Rewriting derived rule.                                                   *)
(* ------------------------------------------------------------------------- *)

let conclusion th = snd(dest_thm th);;

let rewrite1_conv eq t =
  match conclusion eq with
    Atom(R("=",[l;r])) -> inst (term_match l t) eq
  | _ -> failwith "rewrite1_conv";;

let thenc conv1 conv2 t =
  let th1 = conv1 t in
  let th2 = conv2 (rhs(conclusion th1)) in
  trans th1 th2;;

let rec depth fn tm =
  try (thenc fn (depth fn)) tm with Failure _ ->
  match tm with
    Var x -> refl tm
  | Fn(f,args) -> let th = cong f (map (depth fn) args) in
                  if rhs(conclusion th) = tm then th
                  else trans th (depth fn (rhs(conclusion th)));;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
depth (rewrite1_conv group_1) <<|(a * b * c) * (d * e) * f|>>;;
END_INTERACTIVE;;
