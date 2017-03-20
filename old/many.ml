(* ========================================================================= *)
(* A motivating example for many-sorted logic.                               *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

START_INTERACTIVE;;
(real_qelim ** generalize)
 <<(a = 0 <=> true) /\ (b = 0 <=> false) /\
   (c = 0 <=> false) /\  (d = 0 <=> true) /\
   0 <= a /\ 0 <= b /\ 0 <= c /\ 0 <= d /\
   a + a <= a /\  a + b <= b /\ b + c <= a /\ b + d <= b /\
   c + a <= c /\  c + b <= d /\ d + c <= c /\ d + d <= d
   ==> false>>;;
END_INTERACTIVE;;
