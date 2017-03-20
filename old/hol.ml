(* ========================================================================= *)
(* LCF-like formulation of higher order logic not unlike HOL Light.          *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

type hol_type = Bool
              | Ind
              | Fun of hol_type * hol_type;;

let dest_funtype ty =
  match ty with
    Fun(dom,ran) -> (dom,ran)
  | _ -> failwith "rangetype: not a function type";;

let domaintype ty = fst(dest_funtype ty)
and rangetype ty = snd(dest_funtype ty);;

(* ------------------------------------------------------------------------- *)
(* Abstract type of HOL terms, preserving well-typedness.                    *)
(* ------------------------------------------------------------------------- *)

module type Hol_term =
   sig type term
       val mk_const : string * hol_type -> term
       val mk_var : string * hol_type -> term
       val mk_comb : term * term -> term
       val mk_abs : term * term -> term
       val dest_const : term -> string * hol_type
       val dest_var : term -> string * hol_type
       val dest_comb : term -> term * term
       val dest_abs : term -> term * term
       val type_of : term -> hol_type
       val frees : term -> term list
       val instantiate : (term,term)func -> term -> term
   end;;

module Hol : Hol_term = struct
  type term = Const of string * hol_type
                | Var of string * hol_type
                | Comb of term * term
                | Abs of term * term
  let rec type_of tm =
    match tm with
      Const(s,ty) -> ty
    | Var(s,ty) -> ty
    | Comb(s,t) -> rangetype (type_of s)
    | Abs(s,t) -> Fun(type_of s,type_of t)
  let mk_const(s,ty) = Const(s,ty)
  let mk_var(s,ty) = Var(s,ty)
  let mk_comb(s,t) =
    if domaintype(type_of s) = type_of t then Comb(s,t)
    else failwith "mk_comb: types do not agree"
  let mk_abs(s,t) =
    match s with
      Var(_,_) -> Abs(s,t)
    | _ -> failwith "mk_abs: first argument not a variable"
  let dest_const =
    function (Const(s,ty)) -> (s,ty) | _ -> failwith "dest_const"
  let dest_var =
    function (Var(s,ty)) -> (s,ty) | _ -> failwith "dest_var"
  let dest_comb =
    function (Comb(s,t)) -> (s,t) | _ -> failwith "dest_comb"
  let dest_abs =
    function (Abs(s,t)) -> (s,t) | _ -> failwith "dest_abs"
  let rec frees tm =
    match tm with
      Const(_,_) -> []
    | Var(_,_) -> [tm]
    | Comb(s,t) -> union (frees s) (frees t)
    | Abs(x,t) -> subtract (frees t) [x]
  let prime x =
    match x with
      Var(n,ty) -> Var(n^"'",ty)
    | _ -> failwith "prime: not a variable"
  let rec variant x avoid =
    if mem x avoid then variant (prime x) avoid else x
  let rec inst sfn tm =
    match tm with
      Const(_,_) -> tm
    | Var(_,_) -> tryapplyd sfn tm tm
    | Comb(s,t) -> Comb(inst sfn s,inst sfn t)
    | Abs(x,t) ->
        let sfn' = undefine x sfn in
        let x' = if exists (fun y -> mem x (frees (tryapplyd sfn' y y)))
                           (frees tm)
                 then variant x (frees(inst sfn' t)) else x in
        Abs(x',inst ((x |-> x') sfn) t)
  let instantiate sfn tm =
    if forall (fun (x,y) -> type_of x = type_of y) (funset sfn)
    then inst sfn tm else failwith "instantiate: type mismatch"
end;;

open Hol;;

(* ------------------------------------------------------------------------- *)
(* Some extra syntax                                                         *)
(* ------------------------------------------------------------------------- *)

let mk_eq(s,t) =
  let eq = mk_const("=",
     itlist (fun a b -> Fun(a,b)) [type_of s; type_of t] Bool) in
  mk_comb(mk_comb(eq,s),t);;

let dest_eq tm =
  let eql,r = dest_comb tm in
  let eq,l = dest_comb eql in
  let n,_ = dest_const eq in
  if n = "=" then (l,r) else failwith "dest_eq: not an equation";;

(* ------------------------------------------------------------------------- *)
(* Inference system.                                                         *)
(* ------------------------------------------------------------------------- *)

module type Hol_thm =
  sig type thm
      val refl: Hol.term -> thm
      val trans: thm -> thm -> thm
      val cong : thm -> thm -> thm
      val abs : Hol.term -> thm -> thm
      val beta: Hol.term -> thm
      val ext : Hol.term -> Hol.term -> thm
      val axiom: Hol.term -> thm
      val eq_mp: thm -> thm -> thm
      val deduct_antisym: thm -> thm -> thm
      val inst: (term,term)func -> thm -> thm
      val dest_thm: thm -> Hol.term list * Hol.term
  end;;

module Proven : Hol_thm = struct
  type thm = Hol.term list * Hol.term
  let refl tm = [],mk_eq(tm,tm)
  let trans (asl1,c1) (asl2,c2) =
     let s,t = dest_eq c1 and t',u = dest_eq c2 in
     if t = t' then (union asl1 asl2,mk_eq(s,u))
     else failwith "trans: theorems don't match up"
  let cong (asl1,c1) (asl2,c2) =
     let f,g = dest_eq c1 and x,y = dest_eq c2 in
     try union asl1 asl2,mk_eq(mk_comb(f,x),mk_comb(g,y))
     with Failure _ -> failwith "cong: types do not agree"
  let abs x (asl,eq) =
    if exists (mem x ** frees) asl then failwith "abs: free variable"
    else let s,t = dest_eq eq in (asl,mk_eq(mk_abs(x,s),mk_abs(x,t)))
  let beta tm =
    let f,x = dest_comb tm in
    let x',t = dest_abs f in
    if x = x' then ([],mk_eq(tm,t))
    else failwith "beta: variable mismatch"
  let ext x t =
    if mem x (frees t) then failwith "ext: free variable"
    else [],mk_eq(mk_abs(x,mk_comb(t,x)),t)
  let axiom tm = if type_of tm = Bool then [tm],tm
                 else failwith "axiom: non-Boolean term"
  let eq_mp (asl1,c1) (asl2,s') =
     let s,t = dest_eq c1 in
     if s = s' then (union asl1 asl2,t)
     else failwith "eq_mp: theorems don't match up"
  let deduct_antisym (asl1,c1) (asl2,c2) =
      (union (subtract asl1 [c2]) (subtract asl2 [c1]),mk_eq(c1,c2))
  let inst sfn (asl,c) = map (instantiate sfn) asl,instantiate sfn c
  let dest_thm th = th
end;;

open Proven;;

(* ------------------------------------------------------------------------- *)
(* Some trivial inferencing.                                                 *)
(* ------------------------------------------------------------------------- *)

let beta_conv tm =
  let f,t = dest_comb tm in
  let x,s = dest_abs f in
  inst (x := t) (beta(mk_comb(f,x)));;

let sym th =
  let leq,r = dest_comb(snd(dest_thm th)) in
  let eq,l = dest_comb leq in
  eq_mp (cong(refl leq) th) (refl l);;

(* ------------------------------------------------------------------------- *)
(* Combinator reduction.                                                     *)
(* ------------------------------------------------------------------------- *)

let rec combinator tm =
  if can dest_comb tm then
    let s,t = dest_comb tm in mk_comb(combinator s,combinator t)
  else if can dest_abs tm then
    let x,t = dest_abs tm in
    let t' = combinator t in
    if x = t' then
      mk_const("I",type_of tm)
    else if can dest_var t' or can dest_const t' then
      let k = mk_const("K",Fun(type_of t',type_of tm)) in
      mk_comb(k,t')
    else
      let l0,r0 = dest_comb t' in
      let l = combinator(mk_abs(x,l0))
      and r = combinator(mk_abs(x,r0)) in
      let s = mk_const("S",Fun(type_of l,Fun(type_of r,type_of tm))) in
      mk_comb(mk_comb(s,l),r)
  else tm;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let x = mk_var("x",Ind) and f = mk_var("f",Fun(Ind,Ind));;

let t = mk_abs(x,mk_comb(f,x));;

combinator t;;

(* ------------------------------------------------------------------------- *)
(* Formulation of Cantor's theorem.                                          *)
(* ------------------------------------------------------------------------- *)

(meson ** equalitize)
 <<(forall f g x. ((S * f) * g) * x = (f * x) * (g * x)) /\
   (forall x y. (K * x) * y = x) /\
   (forall f x. (W * f) * x = (f * x) * x) /\
   (forall x. ~(n * x = x))
   ==> ~(exists f. forall y. exists x. f * x = y)>>;;

(* ------------------------------------------------------------------------- *)
(* However, it's just the Russell paradox.                                   *)
(* ------------------------------------------------------------------------- *)

(meson ** equalitize)
 <<(forall f g x. ((S * f) * g) * x = (f * x) * (g * x)) /\
   (forall x y. (K * x) * y = x) /\
   (forall f x. (W * f) * x = (f * x) * x) /\
   (forall x. ~(n * x = x))
   ==> false>>;;
END_INTERACTIVE;;
