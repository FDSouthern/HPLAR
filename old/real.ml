(* ========================================================================= *)
(* Real quantifier elimination (using Hormander's algorithm).                *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Evaluate a quantifier-free formula given a sign matrix row for its polys. *)
(* ------------------------------------------------------------------------- *)

let rec testform pmat fm =
  match fm with
    Atom(R(a,[p;Fn("0",[])])) ->
        let s = assoc p pmat in
        if a = "=" then s = Zero
        else if a = "<=" then s = Zero or s = Negative
        else if a = ">=" then s = Zero or s = Positive
        else if a = "<" then s = Negative
        else if a = ">" then s = Positive
        else failwith "testform: unknown literal"
  | False -> false
  | True -> true
  | Not(p) -> not(testform pmat p)
  | And(p,q) -> testform pmat p & testform pmat q
  | Or(p,q) -> testform pmat p or testform pmat q
  | Imp(p,q) -> not(testform pmat p) or testform pmat q
  | Iff(p,q) -> (testform pmat p = testform pmat q)
  | _ -> failwith "testform: non-propositional formula";;

(* ------------------------------------------------------------------------- *)
(* Infer sign of p(x) at points from corresponding qi(x) with pi(x) = 0      *)
(* ------------------------------------------------------------------------- *)

let inferpsign pd qd =
  try let i = index Zero pd in el i qd :: pd
  with Failure _ -> Nonzero :: pd;;

(* ------------------------------------------------------------------------- *)
(* Condense subdivision by removing points with no relevant zeros.           *)
(* ------------------------------------------------------------------------- *)

let rec condense ps =
  match ps with
    int::pt::other -> let rest = condense other in
                      if mem Zero pt then int::pt::rest else rest
  | _ -> ps;;

(* ------------------------------------------------------------------------- *)
(* Infer sign on intervals (use with infinities at end) and split if needed  *)
(* ------------------------------------------------------------------------- *)

let rec inferisign ps =
  match ps with
    pt1::int::pt2::other ->
      let res = inferisign(pt2::other)
      and tint = tl int and s1 = hd pt1 and s2 = hd pt2 in
      if s1 = Positive & s2 = Negative then
        pt1::(Positive::tint)::(Zero::tint)::(Negative::tint)::res
      else if s1 = Negative & s2 = Positive then
        pt1::(Negative::tint)::(Zero::tint)::(Positive::tint)::res
      else if (s1 = Positive or s2 = Negative) & s1 = s2 then
        pt1::(s1::tint)::res
      else if s1 = Zero & s2 = Zero then
        failwith "inferisign: inconsistent"
      else if s1 = Zero then
        pt1::(s2 :: tint)::res
      else if s2 = Zero then
        pt1::(s1 :: tint)::res
      else failwith "inferisign: can't infer sign on interval"
  | _ -> ps;;

(* ------------------------------------------------------------------------- *)
(* Deduce matrix for p,p1,...,pn from matrix for p',p1,...,pn,q0,...,qn      *)
(* where qi = rem(p,pi) with p0 = p'                                         *)
(* ------------------------------------------------------------------------- *)

let dedmatrix cont mat =
  let n = length (hd mat) / 2 in
  let mat1,mat2 = unzip (map (chop_list n) mat) in
  let mat3 = map2 inferpsign mat1 mat2 in
  let mat4 = condense mat3 in
  let k = length(hd mat4) in
  let mats = (replicate k (swap true (el 1 (hd mat3))))::mat4@
             [replicate k (el 1 (last mat3))] in
  let mat5 = butlast(tl(inferisign mats)) in
  let mat6 = map (fun l -> hd l :: tl(tl l)) mat5 in
  cont(condense mat6);;

(* ------------------------------------------------------------------------- *)
(* Pseudo-division making sure the remainder has the same sign.              *)
(* ------------------------------------------------------------------------- *)

let pdivides vars sgns q p =
  let s = findsign vars sgns (head vars p) in
  if s = Zero then failwith "pdivides: head coefficient is zero" else
  let (k,r) = pdivide vars q p in
  if s = Negative & k mod 2 = 1 then poly_neg r
  else if s = Positive or k mod 2 = 0 then r
  else poly_mul (tl vars) (head vars p) r;;

(* ------------------------------------------------------------------------- *)
(* Case splitting for positive/negative (assumed nonzero).                   *)
(* ------------------------------------------------------------------------- *)

let split_sign vars sgns pol cont_p cont_n =
  let s = findsign vars sgns pol in
  if s = Positive then cont_p sgns
  else if s = Negative then cont_n sgns
  else if s = Zero then failwith "split_sign: zero polynomial" else
  let ineq = Atom(R(">",[pol; Fn("0",[])])) in
  Or(And(ineq,cont_p (assertsign vars sgns (pol,Positive))),
     And(Not ineq,cont_n (assertsign vars sgns (pol,Negative))));;

(* ------------------------------------------------------------------------- *)
(* Formal derivative of polynomial.                                          *)
(* ------------------------------------------------------------------------- *)

let rec poly_diff_aux vars n p =
  let np = mk_numeral(Int n) in
  match p with
    Fn("+",[c; Fn("*",[Var x; q])]) when x = hd vars ->
        Fn("+",[poly_mul (tl vars) np c;
                Fn("*",[Var x; poly_diff_aux vars (n+1) q])])
  | _ -> poly_mul vars np p;;

let poly_diff vars p =
  match p with
    Fn("+",[c; Fn("*",[Var x; q])]) when x = hd vars ->
        poly_diff_aux vars 1 q
  | _ -> Fn("0",[]);;

(* ------------------------------------------------------------------------- *)
(* Modifiy cont to insert constant sign into a sign matrix at position i.    *)
(* ------------------------------------------------------------------------- *)

let matinsert i s cont mat = cont (map (insertat i s) mat);;

(* ------------------------------------------------------------------------- *)
(* Continuation will just return false if assignments are inconsistent.      *)
(* ------------------------------------------------------------------------- *)

let trapout cont m =
  try cont m with Failure "inferisign: inconsistent" -> False;;

(* ------------------------------------------------------------------------- *)
(* Find matrix and apply continuation; split over coefficient zero and signs *)
(* ------------------------------------------------------------------------- *)

let rec matrix vars pols cont sgns =
  if pols = [] then trapout cont [[]] else
  if exists (is_constant vars) pols then
    let p = find (is_constant vars) pols in
    let i = index p pols in
    let pols1,pols2 = chop_list i pols in
    let pols' = pols1 @ tl pols2 in
    matrix vars pols' (matinsert i (findsign vars sgns p) cont) sgns
  else
    let d = itlist (max ** degree vars) pols (-1) in
    let p = find (fun p -> degree vars p = d) pols in
    let p' = poly_diff vars p and i = index p pols in
    let qs = let p1,p2 = chop_list i pols in p'::p1 @ tl p2 in
    let gs = map (pdivides vars sgns p) qs in
    let cont' m = cont(map (fun l -> insertat i (hd l) (tl l)) m) in
    splitzero vars qs gs (dedmatrix cont') sgns

and splitzero vars dun pols cont sgns =
  match pols with
    [] -> splitsigns vars [] dun cont sgns
  | p::ops -> if p = Fn("0",[]) then
                let cont' = matinsert (length dun) Zero cont in
                splitzero vars dun ops cont' sgns
              else split_zero (tl vars) sgns (head vars p)
                    (splitzero vars dun (behead vars p :: ops) cont)
                    (splitzero vars (dun@[p]) ops cont)

and splitsigns vars dun pols cont sgns =
  match pols with
    [] -> monicize vars dun cont sgns
  | p::ops -> let cont' = splitsigns vars (dun@[p]) ops cont in
              split_sign (tl vars) sgns (head vars p) cont' cont'

and monicize vars pols cont sgns =
  let mols,swaps = unzip(map (monic vars) pols) in
  let sols = setify mols in
  let indices = map (fun p -> index p sols) mols in
  let transform m =
    map2 (fun sw i -> swap sw (el i m)) swaps indices in
  let cont' mat = cont(map transform mat) in
  matrix vars sols cont' sgns;;

(* ------------------------------------------------------------------------- *)
(* Overall quelim for exists x. literal_1(x) /\ ... /\ literal_n(x)          *)
(* ------------------------------------------------------------------------- *)

let rec polynomials fm =
  atom_union (function (R(a,[p;Fn("0",[])])) -> [p] | _ -> []) fm;;

let basic_real_qelim vars fm =
  let Exists(x,bod) = fm in
  let pols = polynomials bod in
  let cont mat =
    if exists (fun m -> testform (zip pols m) bod) mat
    then True else False in
  splitzero (x::vars) [] pols cont [Fn("1",[]),Positive];;

let real_qelim =
  simplify ** evalc **
  lift_qelim polyatom (simplify ** evalc) basic_real_qelim;;

(* ------------------------------------------------------------------------- *)
(* Sometimes it may pay to use DNF but we don't have to.                     *)
(* ------------------------------------------------------------------------- *)

let real_qelim' =
  simplify ** evalc **
  lift_qelim polyatom (dnf ** cnnf (fun x -> x) ** evalc)
                      basic_real_qelim;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
real_qelim <<exists x. x^4 + x^2 + 1 = 0>>;;

real_qelim <<exists x. x^3 - x^2 + x - 1 = 0>>;;

real_qelim
 <<exists x y. x^3 - x^2 + x - 1 = 0 /\
              y^3 - y^2 + y - 1 = 0 /\ ~(x = y)>>;;

real_qelim
 <<forall a f k. (forall e. k < e ==> f < a * e) ==> f <= a * k>>;;

real_qelim
 <<exists x. a * x^2 + b * x + c = 0>>;;

real_qelim
 <<forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                 b^2 >= 4 * a * c>>;;

real_qelim
 <<forall a b c. (exists x. a * x^2 + b * x + c = 0) <=>
                 a = 0 /\ (~(b = 0) \/ c = 0) \/
                 ~(a = 0) /\ b^2 >= 4 * a * c>>;;

(* ------------------------------------------------------------------------- *)
(* Termination ordering for group theory completion.                         *)
(* ------------------------------------------------------------------------- *)

real_qelim
 <<1 < 2 /\
   (forall x. 1 < x ==> 1 < x^2) /\
   (forall x y. 1 < x /\ 1 < y ==> 1 < x * (1 + 2 * y))>>;;
END_INTERACTIVE;;

let rec trans tm =
  match tm with
    Fn("*",[s;t]) -> Fn("*",[trans s;
                             Fn("+",[Fn("1",[]);
                                     Fn("*",[Fn("2",[]); trans t])])])
  | Fn("i",[t]) -> Fn("^",[trans t; Fn("2",[])])
  | Fn("1",[]) -> Fn("2",[])
  | Var x -> tm;;

let transeq (Atom(R("=",[s;t]))) = Atom(R(">",[trans s; trans t]));;

let supergen fm =
  itlist (fun x p -> Forall(x,Imp(Atom(R(">",[Var x; Fn("1",[])])),p)))
         (fv fm) fm;;

START_INTERACTIVE;;
let eqs = complete_and_simplify ["1"; "*"; "i"]
  [<<1 * x = x>>; <<i(x) * x = 1>>; <<(x * y) * z = x * y * z>>];;

let fm = list_conj (map (supergen ** transeq) eqs);;

real_qelim fm;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* This one works better using DNF.                                          *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;                                                            

real_qelim'
 <<forall d.
     (exists c. forall a b. (a = d /\ b = c) \/ (a = c /\ b = 1)
                            ==> a^2 = b)
     <=> d^4 = 1>>;;

(* ------------------------------------------------------------------------- *)
(* Linear examples.                                                          *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists x. x - 1 > 0>>;;

time real_qelim <<exists x. 3 - x > 0 /\ x - 1 > 0>>;;

(* ------------------------------------------------------------------------- *)
(* Quadratics.                                                               *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists x. x^2 = 0>>;;

time real_qelim <<exists x. x^2 + 1 = 0>>;;

time real_qelim <<exists x. x^2 - 1 = 0>>;;

time real_qelim <<exists x. x^2 - 2 * x + 1 = 0>>;;

time real_qelim <<exists x. x^2 - 3 * x + 1 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Cubics.                                                                   *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists x. x^3 - 1 > 0>>;;

time real_qelim <<exists x. x^3 - 3 * x^2 + 3 * x - 1 > 0>>;;

time real_qelim <<exists x. x^3 - 4 * x^2 + 5 * x - 2 > 0>>;;

time real_qelim <<exists x. x^3 - 6 * x^2 + 11 * x - 6 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Quartics.                                                                 *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists x. x^4 - 1 > 0>>;;

time real_qelim <<exists x. x^4 + 1 > 0>>;;

time real_qelim <<exists x. x^4 = 0>>;;

time real_qelim <<exists x. x^4 - x^3 = 0>>;;

time real_qelim <<exists x. x^4 - x^2 = 0>>;;

time real_qelim <<exists x. x^4 - 2 * x^2 + 2 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Quintics.                                                                 *)
(* ------------------------------------------------------------------------- *)

time real_qelim
  <<exists x. x^5 - 15 * x^4 + 85 * x^3 - 225 * x^2 + 274 * x - 120 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Sextics(?)                                                                *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists x.
 x^6 - 21 * x^5 + 175 * x^4 - 735 * x^3 + 1624 * x^2 - 1764 * x + 720 = 0>>;;

time real_qelim <<exists x.
 x^6 - 12 * x^5 + 56 * x^4 - 130 * x^3 + 159 * x^2 - 98 * x + 24 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Multiple polynomials.                                                     *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists x. x^2 + 2 > 0 /\ x^3 - 11 = 0 /\ x + 131 >= 0>>;;

(* ------------------------------------------------------------------------- *)
(* With more variables.                                                      *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists x. a * x^2 + b * x + c = 0>>;;

time real_qelim <<exists x. a * x^3 + b * x^2 + c * x + d = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Constraint solving.                                                       *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists x1 x2. x1^2 + x2^2 - u1 <= 0 /\ x1^2 - u2 > 0>>;;

(* ------------------------------------------------------------------------- *)
(* Huet & Oppen (interpretation of group theory).                            *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<forall x y. x > 0 /\ y > 0 ==> x * (1 + 2 * y) > 0>>;;

(* ------------------------------------------------------------------------- *)
(* Other examples.                                                           *)
(* ------------------------------------------------------------------------- *)

time real_qelim
  <<forall a f k. (forall e. k < e ==> f < a * e) ==> f <= a * k>>;;

time real_qelim <<exists x. x^2 - x + 1 = 0>>;;

time real_qelim <<exists x. x^2 - 3 * x + 1 = 0>>;;

time real_qelim <<exists x. x > 6 /\ (x^2 - 3 * x + 1 = 0)>>;;

time real_qelim <<exists x. 7 * x^2 - 5 * x + 3 > 0 /\
                            x^2 - 3 * x + 1 = 0>>;;

time real_qelim <<exists x. 11 * x^3 - 7 * x^2 - 2 * x + 1 = 0 /\
                            7 * x^2 - 5 * x + 3 > 0 /\
                            x^2 - 8 * x + 1 = 0>>;;

time real_qelim <<exists x. a * x^2 + b * x + c = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Quadratic inequality from Liska and Steinberg                             *)
(* ------------------------------------------------------------------------- *)

time real_qelim
 <<forall x. -(1) <= x /\ x <= 1 ==>
      C * (x - 1) * (4 * x * a * C - x * C - 4 * a * C + C - 2) >= 0>>;;


(* ------------------------------------------------------------------------- *)
(* Metal-milling example from Loos and Weispfenning                          *)
(* ------------------------------------------------------------------------- *)

time real_qelim
  <<exists x y. 0 < x /\
                y < 0 /\
                x * r - x * t + t = q * x - s * x + s /\
                x * b - x * d + d = a * y - c * y + c>>;;


(* ------------------------------------------------------------------------- *)
(* Linear example from Collins and Johnson                                   *)
(* ------------------------------------------------------------------------- *)

time real_qelim
 <<exists r. 0 < r /\
      r < 1 /\
      0 < (1 - 3 * r) * (a^2 + b^2) + 2 * a * r /\
      (2 - 3 * r) * (a^2 + b^2) + 4 * a * r - 2 * a - r < 0>>;;


(* ------------------------------------------------------------------------- *)
(* Dave Griffioen #4                                                         *)
(* ------------------------------------------------------------------------- *)

time real_qelim
 <<forall x y. (1 - t) * x <= (1 + t) * y /\ (1 - t) * y <= (1 + t) * x
         ==> 0 <= y>>;;

(* ------------------------------------------------------------------------- *)
(* Some examples from "Real Quantifier Elimination in practice".             *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists x2. x1^2 + x2^2 <= u1 /\ x1^2 > u2>>;;

time real_qelim <<exists x1 x2. x1^2 + x2^2 <= u1 /\ x1^2 > u2>>;;

time real_qelim
 <<forall x1 x2. x1 + x2 <= 2 /\ x1 <= 1 /\ x1 >= 0 /\ x2 >= 0
           ==> 3 * (x1 + 3 * x2^2 + 2) <= 8 * (2 * x1 + x2 + 1)>>;;

(* ------------------------------------------------------------------------- *)
(* From Collins & Johnson's "Sign variation..." article.                     *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists r. 0 < r /\ r < 1 /\
                (1 - 3 * r) * (a^2 + b^2) + 2 * a * r > 0 /\
                (2 - 3 * r) * (a^2 + b^2) + 4 * a * r - 2 * a - r < 0>>;;

(* ------------------------------------------------------------------------- *)
(* From "Parallel implementation of CAD" article.                            *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists x. forall y. x^2 + y^2 > 1 /\ x * y >= 1>>;;

(* ------------------------------------------------------------------------- *)
(* Other misc examples.                                                      *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<forall x y. x^2 + y^2 = 1 ==> 2 * x * y <= 1>>;;

time real_qelim <<forall x y. x^2 + y^2 = 1 ==> 2 * x * y < 1>>;;

time real_qelim <<forall x y. x * y > 0 <=> x > 0 /\ y > 0 \/ x < 0 /\ y < 0>>;;

time real_qelim <<exists x y. x > y /\ x^2 < y^2>>;;

time real_qelim <<forall x y. x < y ==> exists z. x < z /\ z < y>>;;

time real_qelim <<forall x. 0 < x <=> exists y. x * y^2 = 1>>;;

time real_qelim <<forall x. 0 <= x <=> exists y. x * y^2 = 1>>;;

time real_qelim <<forall x. 0 <= x <=> exists y. x = y^2>>;;

time real_qelim <<forall x y. 0 < x /\ x < y ==> exists z. x < z^2 /\ z^2 < y>>;;

time real_qelim <<forall x y. x < y ==> exists z. x < z^2 /\ z^2 < y>>;;

time real_qelim <<forall x y. x^2 + y^2 = 0 ==> x = 0 /\ y = 0>>;;

time real_qelim <<forall x y z. x^2 + y^2 + z^2 = 0 ==> x = 0 /\ y = 0 /\ z = 0>>;;

time real_qelim <<forall w x y z. w^2 + x^2 + y^2 + z^2 = 0
                      ==> w = 0 /\ x = 0 /\ y = 0 /\ z = 0>>;;

time real_qelim <<forall a. a^2 = 2 ==> forall x. ~(x^2 + a*x + 1 = 0)>>;;

time real_qelim <<forall a. a^2 = 2 ==> forall x. ~(x^2 - a*x + 1 = 0)>>;;

time real_qelim <<forall x y. x^2 = 2 /\ y^2 = 3 ==> (x * y)^2 = 6>>;;

time real_qelim <<forall x. exists y. x^2 = y^3>>;;

time real_qelim <<forall x. exists y. x^3 = y^2>>;;

time real_qelim
 <<forall a b c.
        (a * x^2 + b * x + c = 0) /\
        (a * y^2 + b * y + c = 0) /\
        ~(x = y)
        ==> (a * (x + y) + b = 0)>>;;

time real_qelim
 <<forall y_1 y_2 y_3 y_4.
     (y_1 = 2 * y_3) /\
     (y_2 = 2 * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1^2 = y_2^2)>>;;

time real_qelim <<forall x. x^2 < 1 <=> x^4 < 1>>;;

(* ------------------------------------------------------------------------- *)
(* Counting roots.                                                           *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<exists x. x^3 - x^2 + x - 1 = 0>>;;

time real_qelim
  <<exists x y. x^3 - x^2 + x - 1 = 0 /\ y^3 - y^2 + y - 1 = 0 /\ ~(x = y)>>;;

time real_qelim <<exists x. x^4 + x^2 - 2 = 0>>;;

time real_qelim
  <<exists x y. x^4 + x^2 - 2 = 0 /\ y^4 + y^2 - 2 = 0 /\ ~(x = y)>>;;

time real_qelim
  <<exists x y. x^3 + x^2 - x - 1 = 0 /\ y^3 + y^2 - y - 1 = 0 /\ ~(x = y)>>;;

time real_qelim <<exists x y z. x^3 + x^2 - x - 1 = 0 /\
                    y^3 + y^2 - y - 1 = 0 /\
                    z^3 + z^2 - z - 1 = 0 /\ ~(x = y) /\ ~(x = z)>>;;

(* ------------------------------------------------------------------------- *)
(* Existence of tangents, so to speak.                                       *)
(* ------------------------------------------------------------------------- *)

time real_qelim
  <<forall x y. exists s c. s^2 + c^2 = 1 /\ s * x + c * y = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Another useful thing (componentwise ==> normwise accuracy etc.)           *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<forall x y. (x + y)^2 <= 2 * (x^2 + y^2)>>;;

(* ------------------------------------------------------------------------- *)
(* Some related quantifier elimination problems.                             *)
(* ------------------------------------------------------------------------- *)

time real_qelim <<forall x y. (x + y)^2 <= c * (x^2 + y^2)>>;;

time real_qelim
  <<forall c. (forall x y. (x + y)^2 <= c * (x^2 + y^2)) <=> 2 <= c>>;;

time real_qelim <<forall a b. a * b * c <= a^2 + b^2>>;;

time real_qelim
  <<forall c. (forall a b. a * b * c <= a^2 + b^2) <=> c^2 <= 4>>;;

(* ------------------------------------------------------------------------- *)
(* Tedious lemmas I once proved manually in HOL.                             *)
(* ------------------------------------------------------------------------- *)

time real_qelim
 <<forall a b c. 0 < a /\ 0 < b /\ 0 < c
                 ==> 0 < a * b /\ 0 < a * c /\ 0 < b * c>>;;

time real_qelim
  <<forall a b c. a * b > 0 ==> (c * a < 0 <=> c * b < 0)>>;;

time real_qelim
  <<forall a b c. a * b > 0 ==> (a * c < 0 <=> b * c < 0)>>;;

time real_qelim
  <<forall a b. a < 0 ==> (a * b > 0 <=> b < 0)>>;;

time real_qelim
  <<forall a b c. a * b < 0 /\ ~(c = 0) ==> (c * a < 0 <=> ~(c * b < 0))>>;;

time real_qelim
  <<forall a b. a * b < 0 <=> a > 0 /\ b < 0 \/ a < 0 /\ b > 0>>;;

time real_qelim
  <<forall a b. a * b <= 0 <=> a >= 0 /\ b <= 0 \/ a <= 0 /\ b >= 0>>;;

(* ------------------------------------------------------------------------- *)
(* Vaguely connected with reductions for Robinson arithmetic.                *)
(* ------------------------------------------------------------------------- *)

time real_qelim
  <<forall a b. ~(a <= b) <=> forall d. d <= b ==> d < a>>;;

time real_qelim
  <<forall a b. ~(a <= b) <=> forall d. d <= b ==> ~(d = a)>>;;

time real_qelim
  <<forall a b. ~(a < b) <=> forall d. d < b ==> d < a>>;;

(* ------------------------------------------------------------------------- *)
(* Another nice problem.                                                     *)
(* ------------------------------------------------------------------------- *)

time real_qelim
 <<forall x y. x^2 + y^2 = 1 ==> (x + y)^2 <= 2>>;;

(* ------------------------------------------------------------------------- *)
(* Some variants / intermediate steps in Cauchy-Schwartz inequality.         *)
(* ------------------------------------------------------------------------- *)

time real_qelim
 <<forall x y. 2 * x * y <= x^2 + y^2>>;;

time real_qelim
 <<forall a b c d. 2 * a * b * c * d <= a^2 * b^2 + c^2 * d^2>>;;

time real_qelim
 <<forall x1 x2 y1 y2.
      (x1 * y1 + x2 * y2)^2 <= (x1^2 + x2^2) * (y1^2 + y2^2)>>;;

(* ------------------------------------------------------------------------- *)
(* The determinant example works OK here too.                                *)
(* ------------------------------------------------------------------------- *)

time real_qelim
 <<exists w x y z. (a * w + b * y = 1) /\
                   (a * x + b * z = 0) /\
                   (c * w + d * y = 0) /\
                   (c * x + d * z = 1)>>;;

time real_qelim
 <<forall a b c d.
        (exists w x y z. (a * w + b * y = 1) /\
                         (a * x + b * z = 0) /\
                         (c * w + d * y = 0) /\
                         (c * x + d * z = 1))
        <=> ~(a * d = b * c)>>;;

END_INTERACTIVE;;
