(* ========================================================================= *)
(* Turing machine interpreter.                                               *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

type symbol = Blank | One;;

type direction = Left | Right | Stay;;

(* ------------------------------------------------------------------------- *)
(* Type of the tape.                                                         *)
(* ------------------------------------------------------------------------- *)

type tape = Tape of int * (int,symbol)func;;

(* ------------------------------------------------------------------------- *)
(* Look at current character.                                                *)
(* ------------------------------------------------------------------------- *)

let look (Tape(r,f)) = tryapplyd f r Blank;;

(* ------------------------------------------------------------------------- *)
(* Write a symbol on the tape.                                               *)
(* ------------------------------------------------------------------------- *)

let write s (Tape(r,f)) = Tape (r,(r |-> s) f);;

(* ------------------------------------------------------------------------- *)
(* Move machine left or right.                                               *)
(* ------------------------------------------------------------------------- *)

let move dir (Tape(r,f)) =
  let d = if dir = Left then -1 else if dir = Right then 1 else 0 in
  Tape(r+d,f);;

(* ------------------------------------------------------------------------- *)
(* Printer.                                                                  *)
(* ------------------------------------------------------------------------- *)

let print_tape (Tape(r,f)) =
  let d = insert 0 (filter (fun n -> apply f n = One) (dom f)) in
  let l = itlist min d r -- itlist max d r in
  let s = map
    (fun n -> if tryapplyd f n Blank = One then "1" else " ") l
  and p = String.make (length (filter (fun n -> n < r) l)) ' ' in
  print_newline();
  print_string (implode s); print_newline();
  print_string p; print_string "^"; print_newline();
  print_string p; print_string "H"; print_newline();;

START_INTERACTIVE;;
#install_printer print_tape;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Configurations, i.e. state and tape together.                             *)
(* ------------------------------------------------------------------------- *)

type config = Config of int * tape;;

(* ------------------------------------------------------------------------- *)
(* Keep running till we get to an undefined state.                           *)
(* ------------------------------------------------------------------------- *)

let rec run prog (Config(state,tape) as config) =
  let stt = (state,look tape) in
  if defined prog stt then
    let char,dir,state' = apply prog (state,look tape) in
    run prog (Config(state',move dir (write char tape)))
  else config;;

(* ------------------------------------------------------------------------- *)
(* Tape with set of canonical input arguments.                               *)
(* ------------------------------------------------------------------------- *)

let input_tape =
  let writen n =
    funpow n (move Left ** write One) ** move Left ** write Blank in
  fun args -> itlist writen args (Tape(0,undefined));;

(* ------------------------------------------------------------------------- *)
(* Read the result of the tape.                                              *)
(* ------------------------------------------------------------------------- *)

let rec output_tape tape =
  let tape' = move Right tape in
  if look tape' = Blank then 0
  else 1 + output_tape tape';;

(* ------------------------------------------------------------------------- *)
(* Overall program execution.                                                *)
(* ------------------------------------------------------------------------- *)

let exec prog args =
  let c = Config(1,input_tape args) in
  let Config(_,t) = run prog c in
  output_tape t;;

(* ------------------------------------------------------------------------- *)
(* Example program (successor).                                              *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let prog_suc = itlist (fun m -> m)
 [(1,Blank) |-> (Blank,Right,2);
  (2,One) |-> (One,Right,2);
  (2,Blank) |-> (One,Right,3);
  (3,Blank) |-> (Blank,Left,4);
  (3,One) |-> (Blank,Left,4);
  (4,One) |-> (One,Left,4);
  (4,Blank) |-> (Blank,Stay,0)]
 undefined;;

exec prog_suc [0];;

exec prog_suc [1];;

exec prog_suc [19];;
END_INTERACTIVE;;
