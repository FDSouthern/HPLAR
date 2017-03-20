(* ========================================================================= *)
(* Other code related to undecidability.                                     *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

START_INTERACTIVE;;
let euler_identity = complex_qelim
 <<(w1^2 + x1^2 + y1^2 + z1^2) *
   (w2^2 + x2^2 + y2^2 + z2^2) =
   (w1 * w2 - x1 * x2 - y1 * y2 - z1 * z2)^2 +
   (w1 * x2 + x1 * w2 + y1 * z2 - z1 * y2)^2 +
   (w1 * y2 - x1 * z2 + y1 * w2 + z1 * x2)^2 +
   (w1 * z2 + x1 * y2 - y1 * x2 + z1 * w2)^2>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* |- x <= n \/ n <= x (for the strong representability & Rosser proof)      *)
(* ------------------------------------------------------------------------- *)

let rec le_total n x =
  if n =/ Int 0 then gen_right x (spec_right (Var x) le_cases_0) else
  let m = n -/ Int 1 in
  right_mp (spec_right (numeral m) le_cases_suc) (le_total m x);;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
le_total (Int 5) "x";;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Goedel's first theorem from Lob 1, modus ponens and diagonal property.    *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let godel_1 = meson
 <<(forall p. |--(p) ==> |--(Pr(p))) /\
   (forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\
   (|--(imp(Pr(G),F)) ==> |--(G))
   ==> |--(imp(Pr(G),F)) ==> |--(F)>>;;

(* ------------------------------------------------------------------------- *)
(* Stronger form with 1-consistency.                                         *)
(* ------------------------------------------------------------------------- *)

let godel_1' = meson
 <<(forall p. |--(p) <=> |--(Pr(p))) /\
   (forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\
   (|--(G) ==> |--(imp(Pr(G),F))) /\ (|--(imp(G,F)) ==> |--(Pr(G)))
   ==> |--(G) \/ |--(imp(G,F)) ==> |--(F)>>;;

(* ------------------------------------------------------------------------- *)
(* Variant with `<=>' form of diagonal lemma.                                *)
(* ------------------------------------------------------------------------- *)

let godel_1'' = meson
 <<(forall p. |--(p) <=> |--(Pr(p))) /\
   (forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\
   (forall p q. |--(iff(p,q)) <=> |--(imp(p,q)) /\ |--(imp(q,p))) /\
   |--(iff(imp(G,F),Pr(G)))
   ==> |--(G) \/ |--(imp(G,F)) ==> |--(F)>>;;

(* ------------------------------------------------------------------------- *)
(* Goedel's second theorem.                                                  *)
(* ------------------------------------------------------------------------- *)

let godel_2 = prove
 <<(forall p. |--(p) ==> |--(Pr(p))) /\
   (forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))) /\
   (forall p. |--(imp(Pr(p),Pr(Pr(p)))))
   ==> (forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\
       (forall p q. |--(imp(q,imp(p,q)))) /\
       (forall p q r. |--(imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r)))))
       ==> |--(imp(G,imp(Pr(G),F))) /\ |--(imp(imp(Pr(G),F),G))
           ==> |--(imp(Pr(F),F)) ==> |--(F)>>
 [assume
   "    lob1: forall p. |--(p) ==> |--(Pr(p))
    and lob2: forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))
    and lob3: forall p. |--(imp(Pr(p),Pr(Pr(p))))";
  assume "logic: antecedent";
  assume "    diag1: |--(imp(G,imp(Pr(G),F)))
          and diag2: |--(imp(imp(Pr(G),F),G))";
  assume "reflection: |--(imp(Pr(F),F))";
  have "|--(Pr(imp(G,imp(Pr(G),F))))" by ["lob1"; "diag1"];
  so have "|--(imp(Pr(G),Pr(imp(Pr(G),F))))" by ["lob2"; "logic"];
  so have "|--(imp(Pr(G),imp(Pr(Pr(G)),Pr(F))))" by ["lob2"; "logic"];
  so have "|--(imp(Pr(G),Pr(F)))" by ["lob3"; "logic"];
  so have "L: |--(imp(Pr(G),F))" by ["reflection"; "logic"];
  so have "|--(G)" by ["diag2"; "logic"];
  so have "|--(Pr(G))" by ["lob1"; "logic"];
  hence "|--(F)" by ["L"; "logic"];
  qed];;

(* ------------------------------------------------------------------------- *)
(* Loeb's theorem --- just replace "F" by "S" in the G2 proof.               *)
(* ------------------------------------------------------------------------- *)

let lob = prove
 <<(forall p. |--(p) ==> |--(Pr(p))) /\
   (forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))) /\
   (forall p. |--(imp(Pr(p),Pr(Pr(p)))))
   ==> (forall p q. |--(imp(p,q)) /\ |--(p) ==> |--(q)) /\
       (forall p q. |--(imp(q,imp(p,q)))) /\
       (forall p q r. |--(imp(imp(p,imp(q,r)),imp(imp(p,q),imp(p,r)))))
       ==> |--(imp(G,imp(Pr(G),S))) /\ |--(imp(imp(Pr(G),S),G))
           ==> |--(imp(Pr(S),S)) ==> |--(S)>>
 [assume
   "    lob1: forall p. |--(p) ==> |--(Pr(p))
    and lob2: forall p q. |--(imp(Pr(imp(p,q)),imp(Pr(p),Pr(q))))
    and lob3: forall p. |--(imp(Pr(p),Pr(Pr(p))))";
  assume "logic: antecedent";
  assume "    diag1: |--(imp(G,imp(Pr(G),S)))
          and diag2: |--(imp(imp(Pr(G),S),G))";
  assume "reflection: |--(imp(Pr(S),S))";
  have "|--(Pr(imp(G,imp(Pr(G),S))))" by ["lob1"; "diag1"];
  so have "|--(imp(Pr(G),Pr(imp(Pr(G),S))))" by ["lob2"; "logic"];
  so have "|--(imp(Pr(G),imp(Pr(Pr(G)),Pr(S))))" by ["lob2"; "logic"];
  so have "|--(imp(Pr(G),Pr(S)))" by ["lob3"; "logic"];
  so have "L: |--(imp(Pr(G),S))" by ["reflection"; "logic"];
  so have "|--(G)" by ["diag2"; "logic"];
  so have "|--(Pr(G))" by ["lob1"; "logic"];
  hence "|--(S)" by ["L"; "logic"];
  qed];;
END_INTERACTIVE;;
