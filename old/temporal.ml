(* ========================================================================= *)
(* Temporal logic.                                                           *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

type tform = Falset
           | Truet
           | Propvart of string
           | Nott of tform
           | Andt of tform * tform
           | Ort of tform * tform
           | Impt of tform * tform
           | Ifft of tform * tform
           | Next of tform
           | Box of tform
           | Diamond of tform;;

(* ------------------------------------------------------------------------- *)
(* Basic semantics for arbitrary valuation-sequence.                         *)
(* ------------------------------------------------------------------------- *)

let rec teval fm v =
  match fm with
    Falset -> false
  | Truet -> true
  | Propvart(x) -> v 0 x
  | Nott(p) -> not(teval p v)
  | Andt(p,q) -> (teval p v) & (teval q v)
  | Ort(p,q) -> (teval p v) or (teval q v)
  | Impt(p,q) -> not(teval p v) or (teval q v)
  | Ifft(p,q) -> (teval p v) = (teval q v)
  | Next p -> teval p (fun i -> v(i + 1))
  | Box p -> teval p v & teval p (fun i -> v(i + 1))
  | Diamond p -> teval p v or teval p (fun i -> v(i + 1));;

(* ------------------------------------------------------------------------- *)
(* Proof via first order reduction.                                          *)
(* ------------------------------------------------------------------------- *)

let default_parser = parse;;

START_INTERACTIVE;;
meson
 <<~(forall t'. t <= t' ==> p(t)) <=> exists t'. t <= t' /\ ~p(t)>>;;

meson
 <<(forall t. t <= t)
  ==> (forall t'. t <= t' ==> forall t''. t' <= t'' ==> p(t''))
      ==> forall t'. t <= t' ==> p(t')>>;;

meson
 <<(forall s t u. s <= t /\ t <= u ==> s <= u)
  ==> (forall t'. t <= t' ==> p(t'))
      ==>  (forall t'. t <= t' ==> forall t''. t' <= t'' ==> p(t''))>>;;
END_INTERACTIVE;;
