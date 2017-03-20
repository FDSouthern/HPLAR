(* ========================================================================= *)
(* Symbolic trajectory evaluation (STE).                                     *)
(*                                                                           *)
(* Based on Melham-Darbari presentation and John O'Leary's tutorial code.    *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

let default_parser = parsep;;

(* ------------------------------------------------------------------------- *)
(* Quaternary lattice.                                                       *)
(* ------------------------------------------------------------------------- *)

type quat = X | ZERO | ONE | T;;

(* ------------------------------------------------------------------------- *)
(* Basic lattice operations.                                                 *)
(* ------------------------------------------------------------------------- *)

let (<==) x y = x = X or y = T or x = y;;

let (&&) x y = if x <== y then y else if y <== x then x else T;;

(* ------------------------------------------------------------------------- *)
(* Boolean extensions.                                                       *)
(* ------------------------------------------------------------------------- *)

let bools q =
  match q with
    X -> [false; true]
  | ZERO -> [false]
  | ONE -> [true]
  | T -> [];;

(* ------------------------------------------------------------------------- *)
(* Converse.                                                                 *)
(* ------------------------------------------------------------------------- *)

let rec quat s =
  match s with
    [false; true] -> X
  | [false]       -> ZERO
  | [true]        -> ONE
  | []            -> T
  | _ -> quat(setify s);;

(* ------------------------------------------------------------------------- *)
(* Deduce the ternary or quaternary extensions of operations.                *)
(* ------------------------------------------------------------------------- *)

let print_quattable quaf fm =
  let pvs = atoms fm in
  let width = itlist (max ** String.length ** pname) pvs 5 + 1 in
  let fixw s = s^String.make(width - String.length s) ' ' in
  let truthstring =
    function X -> "X" | ZERO -> "0" | ONE -> "1" | T -> "T" in
  let testqs assig =
    let assigs = itlist (allpairs (fun h t -> h::t)) assig [[]] in
    quat(map (eval fm ** apply ** instantiate pvs) assigs) in
  let mk_row v =
     let ufn = instantiate pvs v in
     let lis = map (fixw ** truthstring ** apply ufn) pvs
     and ans = fixw(truthstring(testqs(map bools v))) in
     print_string(itlist (^) lis ("| "^ans)); print_newline() in
  let separator = String.make (width * length pvs + 9) '-' in
  print_string(itlist (fun s t -> fixw(pname s) ^ t) pvs "| formula");
  print_newline(); print_string separator; print_newline();
  let lis = if quaf then [X; ZERO; ONE; T] else [X; ZERO; ONE] in
  do_list mk_row (alltuples (length pvs) lis);;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
print_quattable true <<~p>>;;

print_quattable false <<p /\ q>>;;

print_quattable false <<p \/ q>>;;

print_quattable false <<p ==> q>>;;

print_quattable false <<p <=> q>>;;

print_quattable false <<~(p <=> q)>>;;

(* ------------------------------------------------------------------------- *)
(* Example of pessimism from composing truth tables.                         *)
(* ------------------------------------------------------------------------- *)

print_quattable false <<p /\ ~p>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Choice operator for Boolean parametrization.                              *)
(* ------------------------------------------------------------------------- *)

let (>->) b x = if b then x else X;;

(* ------------------------------------------------------------------------- *)
(* Spurious abstraction, but it might be useful later.                       *)
(* ------------------------------------------------------------------------- *)

type node = Node of string;;

(* ------------------------------------------------------------------------- *)
(* Type of trajectory formulas.                                              *)
(* ------------------------------------------------------------------------- *)

type trajform = Is_0 of node
              | Is_1 of node
              | Andj of trajform * trajform
              | When of trajform * prop formula
              | Next of trajform;;

(* ------------------------------------------------------------------------- *)
(* Abstract formula semantics with propositional valuation as last argument. *)
(* ------------------------------------------------------------------------- *)

let rec tholds tf seq v =
  match tf with
    Is_0 nd -> ZERO <== seq 0 nd v
  | Is_1 nd -> ONE <== seq 0 nd v
  | Andj(tf1,tf2) -> tholds tf1 seq v & tholds tf2 seq v
  | When(tf1,p) -> eval p v --> tholds tf1 seq v
  | Next(tf1) -> tholds tf1 (fun t -> seq(t + 1)) v;;

let rec defseq tf t nd v =
  match tf with
    Is_0 n -> (n = nd & t = 0) >-> ZERO
  | Is_1 n -> (n = nd & t = 0) >-> ONE
  | Andj(tf1,tf2) -> defseq tf1 t nd v && defseq tf2 t nd v
  | When(tf1,p) -> eval p v >-> defseq tf1 t nd v
  | Next(tf1) -> (t <> 0) >-> defseq tf1 (t - 1) nd v;;

let rec deftraj step tf t nd v =
  if t = 0 then defseq tf t nd v
  else defseq tf t nd v && step(deftraj step tf (t - 1)) nd v;;

(* ------------------------------------------------------------------------- *)
(* Depth of a trajectory formula.                                            *)
(* ------------------------------------------------------------------------- *)

let rec timedepth tf =
  match tf with
    Is_0 _ | Is_1 _ -> 0
  | Andj(tf1,tf2) -> max (timedepth tf1) (timedepth tf2)
  | When(tf1,p) -> timedepth tf1
  | Next(tf1) -> timedepth tf1 + 1;;

(* ------------------------------------------------------------------------- *)
(* Reformulation that will work better when we use finite partial functions. *)
(* ------------------------------------------------------------------------- *)

let constrain a1 a2 y f x1 x2 =
   if x1 = a1 & x2 = a2 then y && f x1 x2 else f x1 x2;;

let defseq =
  let rec defseq t0 g tf v seq =
    match tf with
      Is_0 n -> constrain t0 n (g >-> ZERO) seq
    | Is_1 n -> constrain t0 n (g >-> ONE) seq
    | Andj(tf1,tf2) -> defseq t0 g tf2 v (defseq t0 g tf1 v seq)
    | When(tf1,p) -> defseq t0 (eval p v & g) tf1 v seq
    | Next(tf1) -> defseq (t0 + 1) g tf1 v seq in
  fun tf t nd v -> defseq 0 true tf v (fun t n -> X) t nd;;

(* ------------------------------------------------------------------------- *)
(* The dual-rail encoding.                                                   *)
(* ------------------------------------------------------------------------- *)

let top = (-1,-1)
and one = (1,-1)
and zero = (-1,1)
and bot = (1,1);;

(* ------------------------------------------------------------------------- *)
(* Lattice ordering as a BDD operation.                                      *)
(* ------------------------------------------------------------------------- *)

let leq bst (h1,l1) (h2,l2) =
  let bst1,h = bdd_Imp bst (h2,h1) in
  let bst2,l = bdd_Imp bst1 (l2,l1) in
  bdd_And bst2 (h,l);;

(* ------------------------------------------------------------------------- *)
(* The lattice join as a BDD operation.                                      *)
(* ------------------------------------------------------------------------- *)

let join bst (h1,l1) (h2,l2) =
  let bst1,h = bdd_And bst (h1,h2) in
  let bst2,l = bdd_And bst1 (l1,l2) in
  bst2,(h,l);;

(* ------------------------------------------------------------------------- *)
(* Choice as a BDD operation.                                                *)
(* ------------------------------------------------------------------------- *)

let bchoice bst b (h,l) =
  let bst1,h' = bdd_Imp bst (b,h) in
  let bst2,l' = bdd_Imp bst1 (b,l) in
  bst2,(h',l');;

(* ------------------------------------------------------------------------- *)
(* Form the defining sequence.                                               *)
(* ------------------------------------------------------------------------- *)

let constrain bst t n y seq =
  let st = tryapplyd seq t undefined in
  let x = tryapplyd st n bot in
  let bst1,z = join bst x y in
  bst1,(t |-> (n |-> z) st) seq;;

let defseq =
  let rec defseq bst t0 g tf seq =
    match tf with
      Is_0 n -> let bst1,z = bchoice bst g zero in
                constrain bst1 t0 n z seq
    | Is_1 n -> let bst1,z = bchoice bst g one in
                constrain bst1 t0 n z seq
    | Andj(tf1,tf2) ->
        let bst1,seq1 = defseq bst t0 g tf1 seq in
        defseq bst1 t0 g tf2 seq1
    | When(tf1,p) ->
        let bst1,n = bdd_Make bst p in
        let bst2,g' = bdd_And bst1 (n,g) in
        defseq bst2 t0 g' tf1 seq
    | Next(tf1) -> defseq bst (t0 + 1) g tf1 seq in
  fun bst tf -> defseq bst 0 1 tf undefined;;

(* ------------------------------------------------------------------------- *)
(* Now the defining trajectory.                                              *)
(* ------------------------------------------------------------------------- *)

let rec deftraj bst step tf t =
  if t = 0 then defseq bst tf else
  let bst1,seq1 = deftraj bst step tf (t - 1) in
  let st = tryapplyd seq1 (t - 1) undefined in
  let bst2,st' = step bst1 st in
  itlist (fun (n,v) (bst,seq) -> constrain bst t n v seq) (funset st')
         (bst2,seq1);;

(* ------------------------------------------------------------------------- *)
(* Check containment of sequences.                                           *)
(* ------------------------------------------------------------------------- *)

let contained bst seq1 seq2 =
  itlist (fun t ->
    let st1 = apply seq1 t and st2 = tryapplyd seq2 t undefined in
    itlist (fun n (bst,x) ->
              let v1 = apply st1 n and v2 = tryapplyd st2 n bot in
              let bst1,y = leq bst v1 v2 in bdd_And bst1 (x,y))
           (dom st1))
    (dom seq1) (bst,1);;

(* ------------------------------------------------------------------------- *)
(* STE model checking algorithm.                                             *)
(* ------------------------------------------------------------------------- *)

let ste bst ckt (a,c) =
  let bst1,a_trj = deftraj bst ckt a (timedepth c) in
  let bst2,c_seq = defseq bst1 c in
  contained bst2 c_seq a_trj;;

(* ------------------------------------------------------------------------- *)
(* Basic gates. Note that they don't work for overconstrained value T.       *)
(* ------------------------------------------------------------------------- *)

let not_gate bst (h,l) = bst,(l,h);;

let and_gate bst (h1,l1) (h2,l2) =
  let bst1,h = bdd_And bst (h1,h2) in
  let bst2,l = bdd_Or bst1 (l1,l2) in
  bst2,(h,l);;

let or_gate bst (h1,l1) (h2,l2) =
  let bst1,h = bdd_Or bst (h1,h2) in
  let bst2,l = bdd_And bst1 (l1,l2) in
  bst2,(h,l);;

(* ------------------------------------------------------------------------- *)
(* The next-state function.                                                  *)
(* ------------------------------------------------------------------------- *)

let step bst st =
  let value nd = tryapplyd st (Node nd) bot in
  itlist (fun ((x1,x2),y) (bst,st) ->
            let bst',z = and_gate bst (value x1) (value x2) in
            if z = bot then (bst,st) else (bst',(Node y |-> z) st))
         [("a1","b0"),"b1";
          ("a2","b1"),"b2";
          ("a3","b2"),"b3";
          ("a4","b3"),"b4";
          ("a5","b4"),"b5";
          ("a6","b5"),"b6"]
         (bst,(Node"b0" |-> value "a0") undefined);;

(* ------------------------------------------------------------------------- *)
(* Shorthands (really, it would be better to write a proper parser).         *)
(* ------------------------------------------------------------------------- *)

let (&&&) x y = Andj(x,y);;

let (<--) f p = When(f,p);;

let is0 s = Is_0(Node s) and is1 s = Is_1(Node s);;

let next n p = funpow n (fun p -> Next p) p;;

(* ------------------------------------------------------------------------- *)
(* An example.                                                               *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let a =
  (next 0 (is0 "a0") <-- <<~p /\ ~q /\ ~r>>) &&&
  (next 1 (is0 "a1") <-- <<~p /\ ~q /\  r>>) &&&
  (next 2 (is0 "a2") <-- <<~p /\  q /\ ~r>>) &&&
  (next 3 (is0 "a3") <-- <<~p /\  q /\  r>>) &&&
  (next 4 (is0 "a4") <-- << p /\ ~q /\ ~r>>) &&&
  (next 5 (is0 "a5") <-- << p /\ ~q /\  r>>) &&&
  (next 6 (is0 "a6") <-- << p /\  q /\ ~r>>) &&&
  (next 0 (is1 "a0") <-- << p /\  q /\  r>>) &&&
  (next 1 (is1 "a1") <-- << p /\  q /\  r>>) &&&
  (next 2 (is1 "a2") <-- << p /\  q /\  r>>) &&&
  (next 3 (is1 "a3") <-- << p /\  q /\  r>>) &&&
  (next 4 (is1 "a4") <-- << p /\  q /\  r>>) &&&
  (next 5 (is1 "a5") <-- << p /\  q /\  r>>) &&&
  (next 6 (is1 "a6") <-- << p /\  q /\  r>>);;

let c = (next 7 (is1 "b6") <-- <<p /\ q /\ r>>) &&&
        (next 7 (is0 "b6") <-- <<~p \/ ~q \/ ~r>>);;

let bst = mk_bdd (fun s1 s2 -> s1 < s2),undefined,undefined in
ste bst step (a,c);;
END_INTERACTIVE;;
