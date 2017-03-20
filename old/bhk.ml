(* ========================================================================= *)
(* Some trivial ML code illustrating the BHK interpretation.                 *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

type ('a,'b)sum = Left of 'a | Right of 'b;;

(* ------------------------------------------------------------------------- *)
(* Some canonical proofs.                                                    *)
(* ------------------------------------------------------------------------- *)

let i = fun x -> x;;

let k = fun x y -> x;;

let s = fun f g x -> (f x) (g x);;

START_INTERACTIVE;;
s k k;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* However CAML can create programs of other types.                          *)
(* ------------------------------------------------------------------------- *)

let rec f x = f x;;
