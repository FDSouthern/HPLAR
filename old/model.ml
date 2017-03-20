(* ========================================================================= *)
(* CTL model checking.                                                       *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

let default_parser = parsep;;

(* ------------------------------------------------------------------------- *)
(* Define CTL syntax (with the path and temporal operators combined).        *)
(* ------------------------------------------------------------------------- *)

type sform = Falsec
           | Truec
           | Propvarc of string
           | Notc of sform
           | Andc of sform * sform
           | Orc of sform * sform
           | Impc of sform * sform
           | Iffc of sform * sform
           | AF of sform
           | AG of sform
           | AX of sform
           | AU of sform * sform
           | EF of sform
           | EG of sform
           | EX of sform
           | EU of sform * sform;;

(* ------------------------------------------------------------------------- *)
(* Model-check EX(p) by simply mapping a |-> Pre(a).                         *)
(* ------------------------------------------------------------------------- *)

let check_EX evs r bst p = bdd_Pre evs bst (r,p);;

(* ------------------------------------------------------------------------- *)
(* Model-check E(p U q) by iterating a |-> q \/ p /\ Pre(a) from "false".    *)
(* ------------------------------------------------------------------------- *)

let step_EU evs r p q bst a =
  let bst1,a' = bdd_Pre evs bst (r,a) in
  let bst2,pa' = bdd_And bst1 (p,a') in
  bdd_Or bst2 (q,pa');;

let check_EU evs r bst (p,q) =
  iterate_to_fixpoint (step_EU evs r p q) bst (-1);;

(* ------------------------------------------------------------------------- *)
(* Model-check EG p by iterating a |-> p /\ Pre(a) from "true".              *)
(* ------------------------------------------------------------------------- *)

let step_EG evs r p bst a =
  let bst',a' = bdd_Pre evs bst (r,a) in bdd_And bst' (p,a');;

let check_EG evs r bst p =
  iterate_to_fixpoint (step_EG evs r p) bst 1;;

(* ------------------------------------------------------------------------- *)
(* Main symbolic model checking function.                                    *)
(* ------------------------------------------------------------------------- *)

let rec modelcheck vars r bst fm =
  match fm with
    Falsec -> bst,-1
  | Truec -> bst,1
  | Propvarc(s) -> bdd_Node (P s) bst (1,-1)
  | Notc(p) -> single (modelcheck vars r) bst p bdd_Not
  | Andc(p,q) -> double (modelcheck vars r) bst p q bdd_And
  | Orc(p,q) -> double (modelcheck vars r) bst p q bdd_Or
  | Impc(p,q) -> double (modelcheck vars r) bst p q bdd_Imp
  | Iffc(p,q) -> double (modelcheck vars r) bst p q bdd_Iff
  | AF(p) -> modelcheck vars r bst (Notc(EG(Notc p)))
  | AG(p) -> modelcheck vars r bst (Notc(EF(Notc p)))
  | AX(p) -> modelcheck vars r bst (Notc(EX(Notc p)))
  | AU(p,q) -> modelcheck vars r bst
               (Andc(Notc(EU(Notc(q),Andc(Notc(p),Notc(q)))),
                     Notc(EG(Notc(q)))))
  | EF(p) -> modelcheck vars r bst (EU(Truec,p))
  | EG(p) -> single (modelcheck vars r) bst p (check_EG vars r)
  | EX(p) -> single (modelcheck vars r) bst p (check_EX vars r)
  | EU(p,q) -> double (modelcheck vars r) bst p q (check_EU vars r);;

(* ------------------------------------------------------------------------- *)
(* Overall model-checking function.                                          *)
(* ------------------------------------------------------------------------- *)

let model_check vars s r p =
  let vars' = map (fun s -> P(s^"'")) vars in
  let bst0 = mk_bdd (fun s1 s2 -> s1 < s2),undefined,undefined in
  let bst1,[n_s;n_r] = bdd_Makes bst0 [s;r] in
  let bst2,n_f = modelcheck vars' n_r bst1 p in
  snd(bdd_Imp bst2 (n_s,n_f)) = 1;;

(* ------------------------------------------------------------------------- *)
(* Some simple examples.                                                     *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let [v0; v1; v2; p0; p1; p2] = map (fun s -> Propvarc(s))
    ["v0"; "v1"; "v2"; "p0"; "p1"; "p2"];;

model_check ["v2"; "v1"; "v0"] <<true>> counter_trans
  (AF(Andc(v1,AX(Notc(v1)))));;

let s = <<~p2 /\ ~p1 /\ ~p0 /\ ~q2 /\ ~q1 /\ ~q0 /\ ~v1 /\ ~v0>>
and fm = AG(Impc(Andc(Notc(p0),Andc(Notc(p1),Notc(p2))),
                EF(Andc(p0,Andc(Notc(p1),Notc(p2))))))
and vars = ["p2"; "p1"; "p0"; "q2"; "q1"; "q0"; "v1"; "v0"] in
model_check vars s mutex_trans fm;;

(* ------------------------------------------------------------------------- *)
(* Failure of fairness even for correct algorithm.                           *)
(* ------------------------------------------------------------------------- *)

let s =
  <<~p2 /\ ~p1 /\ ~p0 /\ ~q2 /\ ~q1 /\ ~q0 /\ ~f1 /\ ~f0 /\ ~t>>
and fm = AG(Impc(Andc(Notc(p0),Andc(Notc(p1),Notc(p2))),
                AF(Andc(p0,Andc(Notc(p1),Notc(p2))))))
and vars = ["p2"; "p1"; "p0"; "q2"; "q1"; "q0"; "f2"; "f1"; "t"] in
model_check vars s peter_trans fm;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Model checking with fairness.                                             *)
(* ------------------------------------------------------------------------- *)

let rec stepfair_EG evs r fcs p bst a =
  match fcs with
    [] -> bdd_And bst (p,a)
  | f::ofcs ->
        let bst1,af = bdd_And bst (a,f) in
        let bst2,puaf = check_EU evs r bst1 (p,af) in
        let bst3,pru = bdd_Pre evs bst2 (r,puaf) in
        let bst4,a' = bdd_And bst3 (a,pru) in
        stepfair_EG evs r ofcs p bst4 a';;

let checkfair_EG evs r fcs bst p =
  if fcs = [] then iterate_to_fixpoint (step_EG evs r p) bst 1
  else iterate_to_fixpoint (stepfair_EG evs r fcs p) bst 1;;

let checkfair_EX evs r fcs bst p =
  let bst1,fairs = checkfair_EG evs r fcs bst 1 in
  let bst2,pfairs = bdd_And bst1 (p,fairs) in
  check_EX evs r bst2 pfairs;;

let checkfair_EU evs r fcs bst (p,q) =
  let bst1,fairs = checkfair_EG evs r fcs bst 1 in
  let bst2,qfairs = bdd_And bst1 (q,fairs) in
  check_EU evs r bst2 (p,qfairs);;

let rec fmodelcheck vars r fcs bst fm =
  match fm with
    Falsec -> bst,-1
  | Truec -> bst,1
  | Propvarc(s) -> bdd_Node (P s) bst (1,-1)
  | Notc(p) -> single (fmodelcheck vars r fcs) bst p bdd_Not
  | Andc(p,q) -> double (fmodelcheck vars r fcs) bst p q bdd_And
  | Orc(p,q) -> double (fmodelcheck vars r fcs) bst p q bdd_Or
  | Impc(p,q) -> double (fmodelcheck vars r fcs) bst p q bdd_Imp
  | Iffc(p,q) -> double (fmodelcheck vars r fcs) bst p q bdd_Iff
  | AF(p) -> fmodelcheck vars r fcs bst (Notc(EG(Notc p)))
  | AG(p) -> fmodelcheck vars r fcs bst (Notc(EF(Notc p)))
  | AX(p) -> fmodelcheck vars r fcs bst (Notc(EX(Notc p)))
  | AU(p,q) -> fmodelcheck vars r fcs bst
               (Andc(Notc(EU(Notc(q),Andc(Notc(p),Notc(q)))),
                     Notc(EG(Notc(q)))))
  | EF(p) -> fmodelcheck vars r fcs bst (EU(Truec,p))
  | EG(p) ->
      single (fmodelcheck vars r fcs) bst p (checkfair_EG vars r fcs)
  | EX(p) ->
      single (fmodelcheck vars r fcs) bst p (checkfair_EX vars r fcs)
  | EU(p,q) ->
      double (fmodelcheck vars r fcs) bst p q (checkfair_EU vars r fcs);;

(* ------------------------------------------------------------------------- *)
(* Overall packaging.                                                        *)
(* ------------------------------------------------------------------------- *)

let fair_model_check vars s r p fcs =
  let vars' = map (fun s -> P(s^"'")) vars in
  let bst0 = mk_bdd (fun s1 s2 -> s1 < s2),undefined,undefined in
  let bst1,n_s::n_r::n_fcs = bdd_Makes bst0 (s::r::fcs) in
  let bst2,n_f = fmodelcheck vars' n_r n_fcs bst1 p in
  snd(bdd_Imp bst2 (n_s,n_f)) = 1;;
