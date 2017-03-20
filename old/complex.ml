(* ========================================================================= *)
(* Complex quantifier elimination (by simple divisibility a la Tarski).      *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Basic arithmetic operations on canonical polynomials.                     *)
(* ------------------------------------------------------------------------- *)

let rec poly_add vars pol1 pol2 =
  match (pol1,pol2) with
   (Fn("+",[c; Fn("*",[Var x; p])]),Fn("+",[d; Fn("*",[Var y; q])])) ->
        if earlier vars x y then poly_cadd vars pol2 pol1
        else if earlier vars y x then poly_cadd vars pol1 pol2 else
        let cd = poly_add vars c d and pq = poly_add vars p q in
        if pq = Fn("0",[]) then cd
        else Fn("+",[cd; Fn("*",[Var x; pq])])
    | (_,Fn("+",_)) -> poly_cadd vars pol1 pol2
    | (Fn("+",_),pol2) -> poly_cadd vars pol2 pol1
    | _ -> numeral2 (+/) pol1 pol2
and poly_cadd vars =
  fun pol1 (Fn("+",[d; Fn("*",[Var y; q])])) ->
        Fn("+",[poly_add vars pol1 d; Fn("*",[Var y; q])]);;

let rec poly_neg =
  function (Fn("+",[c; Fn("*",[Var x; p])])) ->
                Fn("+",[poly_neg c; Fn("*",[Var x; poly_neg p])])
         | n -> numeral1 minus_num n;;

let poly_sub vars p q = poly_add vars p (poly_neg q);;

let rec poly_mul vars pol1 pol2 =
  match (pol1,pol2) with
   (Fn("+",[c; Fn("*",[Var x; p])]),Fn("+",[d; Fn("*",[Var y; q])])) ->
        if earlier vars x y then poly_cmul vars pol2 pol1
        else poly_cmul vars pol1 pol2
  | (Fn("0",[]),_) -> Fn("0",[])
  | (_,Fn("0",[])) -> Fn("0",[])
  | (_,Fn("+",_)) -> poly_cmul vars pol1 pol2
  | (Fn("+",_),_) -> poly_cmul vars pol2 pol1
  | _ -> numeral2 ( */ ) pol1 pol2
and poly_cmul vars =
  fun pol1 (Fn("+",[d; Fn("*",[Var y; q])])) ->
        poly_add vars (poly_mul vars pol1 d)
                     (Fn("+",[Fn("0",[]);
                              Fn("*",[Var y; poly_mul vars pol1 q])]));;

let poly_pow vars p n = funpow n (poly_mul vars p) (Fn("1",[]));;

(* ------------------------------------------------------------------------- *)
(* Convert term into canonical polynomial representative.                    *)
(* ------------------------------------------------------------------------- *)

let rec polynate vars tm =
  match tm with
    Var x -> Fn("+",[Fn("0",[]); Fn("*",[Var x; Fn("1",[])])])
  | Fn(ns,[]) -> if can num_of_string ns then tm
                 else failwith "Unexpected constant"
  | Fn("^",[p;Fn(n,[])]) ->
       poly_pow vars (polynate vars p) (int_of_string n)
  | Fn("*",[s;t]) -> poly_mul vars (polynate vars s) (polynate vars t)
  | Fn("+",[s;t]) -> poly_add vars (polynate vars s) (polynate vars t)
  | Fn("-",[s;t]) -> poly_sub vars (polynate vars s) (polynate vars t)
  | Fn("-",[t]) -> poly_neg (polynate vars t)
  | Fn(s,_) -> failwith ("Unexpected function symbol: "^s);;

(* ------------------------------------------------------------------------- *)
(* Do likewise for atom so the RHS is zero.                                  *)
(* ------------------------------------------------------------------------- *)

let polyatom vars fm =
  match fm with
    Atom(R(a,[s;t])) ->
        Atom(R(a,[polynate vars (Fn("-",[s;t])); Fn("0",[])]))
  | _ -> failwith "polyatom: not an atom";;

(* ------------------------------------------------------------------------- *)
(* Sanity check.                                                             *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let liouville = polyatom ["w"; "x"; "y"; "z"]
 <<6 * (w^2 + x^2 + y^2 + z^2)^2 =
   (((w + x)^4 + (w + y)^4 + (w + z)^4 +
     (x + y)^4 + (x + z)^4 + (y + z)^4) +
    ((w - x)^4 + (w - y)^4 + (w - z)^4 +
     (x - y)^4 + (x - z)^4 + (y - z)^4))>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Useful utility functions for polynomial terms.                            *)
(* ------------------------------------------------------------------------- *)

let rec degree vars =
  function (Fn("+",[c; Fn("*",[Var x; p])])) when x = hd vars ->
                1 + degree vars p
         | _ -> 0;;

let rec coefficients vars =
  function (Fn("+",[c; Fn("*",[Var x; q])]) as p) when x = hd vars ->
                c::(coefficients vars q)
         | p -> [p];;

let head vars p = last(coefficients vars p);;

let is_constant vars p =
  match p with
    Fn("+",[c; Fn("*",[Var x; q])]) when x = hd vars -> false
  | _ -> true;;

let rec behead vars =
  function Fn("+",[c; Fn("*",[Var x; p])]) when x = hd vars ->
                let p' = behead vars p in
                if p' = Fn("0",[]) then c
                else Fn("+",[c; Fn("*",[Var x; p'])])
         | _ -> Fn("0",[]);;

(* ------------------------------------------------------------------------- *)
(* Get the constant multiple of the "maximal" monomial (implicit lex order)  *)
(* ------------------------------------------------------------------------- *)

let rec headconst p =
  match p with
    Fn("+",[c; Fn("*",[Var x; q])]) -> headconst q
  | Fn(n,[]) -> dest_numeral p;;

(* ------------------------------------------------------------------------- *)
(* Make a polynomial monic and return negativity flag for head constant      *)
(* ------------------------------------------------------------------------- *)

let monic vars p =
  let h = headconst p in
  if h = Int 0 then p,false else
  poly_mul vars (mk_numeral(Int 1 // h)) p,h </ Int 0;;

(* ------------------------------------------------------------------------- *)
(* Pseudo-division of s by p; head coefficient of p assumed nonzero.         *)
(* Returns (k,r) so that a^k s = p q + r for some q, deg(r) < deg(p).        *)
(* Optimized only for the trivial case of equal head coefficients; no GCDs.  *)
(* ------------------------------------------------------------------------- *)

let pdivide =
  let shift1 x p = Fn("+",[Fn("0",[]); Fn("*",[Var x; p])]) in
  let rec pdivide_aux vars a n p k s =
    if s = Fn("0",[]) then (k,s) else
    let b = head vars s and m = degree vars s in
    if m < n then (k,s) else
    let p' = funpow (m - n) (shift1 (hd vars)) p in
    if a = b then
      pdivide_aux vars a n p k (poly_sub vars s p')
    else
      pdivide_aux vars a n p (k+1)
        (poly_sub vars (poly_mul vars a s) (poly_mul vars b p')) in
  fun vars s p -> pdivide_aux vars (head vars p) (degree vars p) p 0 s;;

(* ------------------------------------------------------------------------- *)
(* Datatype of signs.                                                        *)
(* ------------------------------------------------------------------------- *)

type sign = Zero | Nonzero | Positive | Negative;;

let swap swf s =
  if not swf then s else
  match s with
    Positive -> Negative
  | Negative -> Positive
  | _ -> s;;

(* ------------------------------------------------------------------------- *)
(* Lookup and asserting of polynomial sign, modulo constant multiples.       *)
(* Note that we are building in a characteristic-zero assumption here.       *)
(* ------------------------------------------------------------------------- *)

let findsign vars sgns p =
  try let p',swf = monic vars p in
      swap swf (assoc p' sgns)
  with Failure _ -> failwith "findsign";;

let assertsign vars sgns (p,s) =
  if p = Fn("0",[]) then
    if s = Zero then sgns else failwith "assertsign"
  else
    let p',swf = monic vars p in
    let s' = swap swf s in
    let s0 = try assoc p' sgns with Failure _ -> s' in
    if s' = s0 or s0 = Nonzero & (s' = Positive or s' = Negative)
    then (p',s')::(subtract sgns [p',s0]) else failwith "assertsign";;

(* ------------------------------------------------------------------------- *)
(* Deduce or case-split over zero status of polynomial.                      *)
(* ------------------------------------------------------------------------- *)

let split_zero vars sgns pol cont_z cont_n =
  try let z = findsign vars sgns pol in
      (if z = Zero then cont_z else cont_n) sgns
  with Failure "findsign" ->
      let eq = Atom(R("=",[pol; Fn("0",[])])) in
      Or(And(eq,cont_z (assertsign vars sgns (pol,Zero))),
         And(Not eq,cont_n (assertsign vars sgns (pol,Nonzero))));;

(* ------------------------------------------------------------------------- *)
(* Whether a polynomial is nonzero in a context.                             *)
(* ------------------------------------------------------------------------- *)

let poly_nonzero vars sgns pol =
  let cs = coefficients vars pol in
  let dcs,ucs = partition (can (findsign vars sgns)) cs in
  if exists (fun p -> not(findsign vars sgns p = Zero)) dcs then True
  else if ucs = [] then False else
  end_itlist (fun p q -> Or(p,q))
             (map (fun p -> Not(Atom(R("=",[p; Fn("0",[])])))) ucs);;

(* ------------------------------------------------------------------------- *)
(* Divisibility and hence variety inclusion.                                 *)
(* ------------------------------------------------------------------------- *)

let rec poly_not_divides vars sgns p q =
  if degree vars q < degree vars p then poly_nonzero vars sgns q else
  let _,q' = pdivide vars q p in
  poly_not_divides vars sgns p q';;

let poly_variety vars sgns p q =
  poly_not_divides vars sgns p (poly_pow vars q (degree vars p));;

(* ------------------------------------------------------------------------- *)
(* Main reduction for ?x. all ceqs == 0 and all cneqs =/= 0, in context.     *)
(* ------------------------------------------------------------------------- *)

let rec reduce vars (eqs,neqs) sgns =
  try let c = find (is_constant vars) eqs in
      try if findsign vars sgns c = Zero
          then reduce vars (subtract eqs [c],neqs) sgns else False
      with Failure _ ->
          And(Atom(R("=",[c;Fn("0",[])])),
              reduce vars (subtract eqs [c],neqs)
                          (assertsign vars sgns (c,Zero)))
  with Failure _ -> match (eqs,neqs) with
    ([],neqs) -> list_conj (map (poly_nonzero vars sgns) neqs)
  | ([p],neqs) ->
        split_zero vars sgns (head vars p)
          (reduce vars ([behead vars p],neqs))
          (fun sgns ->
             if neqs = [] then True else
             poly_variety vars sgns p
              (snd(pdivide vars (end_itlist (poly_mul vars) neqs) p)))
  | (_,_) ->
        let n = end_itlist min (map (degree vars) eqs) in
        let p = find (fun p -> degree vars p = n) eqs in
        let oeqs = subtract eqs [p] in
        let cfn q = snd(pdivide vars q p) in
        split_zero vars sgns (head vars p)
          (reduce vars (behead vars p::oeqs,neqs))
          (reduce vars (p::(map cfn oeqs),neqs));;

(* ------------------------------------------------------------------------- *)
(* Basic complex quantifier elimination on actual existential formula.       *)
(* ------------------------------------------------------------------------- *)

let lhz (Atom(R("=",[s; Fn("0",[])]))) = s;;

let lhnz (Not fm) = lhz fm;;

let basic_complex_qelim vars fm =
  match fm with
    Exists(x,p) ->
        let eqs,neqs = partition (non negative) (conjuncts p) in
        reduce (x::vars) (map lhz eqs,map lhnz neqs)
               [Fn("1",[]),Positive]
  | _ -> failwith "basic_complex_qelim: not an existential formula";;

(* ------------------------------------------------------------------------- *)
(* Full quantifier elimination.                                              *)
(* ------------------------------------------------------------------------- *)

let complex_qelim =
  simplify ** evalc **
  lift_qelim polyatom (dnf ** cnnf (fun x -> x) ** evalc)
             basic_complex_qelim;;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
complex_qelim
 <<forall a x. a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0>>;;

complex_qelim
 <<forall a x. a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + c = 0>>;;

complex_qelim
 <<forall x y. x^2 = 2 /\ y^2 = 3 ==> (x * y)^2 = 6>>;;

complex_qelim
 <<forall a b c x y. (a * x^2 + b * x + c = 0) /\
                     (a * y^2 + b * y + c = 0) /\
                     ~(x = y)
                     ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

complex_qelim
 <<forall x y.
    (forall a b c. (a * x^2 + b * x + c = 0) /\
                   (a * y^2 + b * y + c = 0)
                   ==> (a * x * y = c) /\ (a * (x + y) + b = 0))
    <=> ~(x = y)>>;;

(* ------------------------------------------------------------------------- *)
(* More serious test for pure normalization code.                            *)
(* ------------------------------------------------------------------------- *)

let polytest tm = time (polynate (fvt tm)) tm;;

let lagrange_4 = polytest
 <<|(((x1^2) + (x2^2) + (x3^2) + (x4^2)) *
     ((y1^2) + (y2^2) + (y3^2) + (y4^2))) -
    ((((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4))^2)  +
     (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3))^2)  +
     (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2))^2)  +
     (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1))^2))|>>;;

let lagrange_8 = polytest
 <<|((p1^2 + q1^2 + r1^2 + s1^2 + t1^2 + u1^2 + v1^2 + w1^2) *
     (p2^2 + q2^2 + r2^2 + s2^2 + t2^2 + u2^2 + v2^2 + w2^2)) -
     ((p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1* w2)^2 +
      (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1* v2)^2 +
      (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1* u2)^2 +
      (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1* t2)^2 +
      (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1* s2)^2 +
      (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1* r2)^2 +
      (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1* q2)^2 +
      (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1* p2)^2)|>>;;

let liouville = polytest
 <<|6 * (x1^2 + x2^2 + x3^2 + x4^2)^2 -
    (((x1 + x2)^4 + (x1 + x3)^4 + (x1 + x4)^4 +
      (x2 + x3)^4 + (x2 + x4)^4 + (x3 + x4)^4) +
     ((x1 - x2)^4 + (x1 - x3)^4 + (x1 - x4)^4 +
      (x2 - x3)^4 + (x2 - x4)^4 + (x3 - x4)^4))|>>;;

let fleck = polytest
 <<|60 * (x1^2 + x2^2 + x3^2 + x4^2)^3 -
    (((x1 + x2 + x3)^6 + (x1 + x2 - x3)^6 +
      (x1 - x2 + x3)^6 + (x1 - x2 - x3)^6 +
      (x1 + x2 + x4)^6 + (x1 + x2 - x4)^6 +
      (x1 - x2 + x4)^6 + (x1 - x2 - x4)^6 +
      (x1 + x3 + x4)^6 + (x1 + x3 - x4)^6 +
      (x1 - x3 + x4)^6 + (x1 - x3 - x4)^6 +
      (x2 + x3 + x4)^6 + (x2 + x3 - x4)^6 +
      (x2 - x3 + x4)^6 + (x2 - x3 - x4)^6) +
     2 * ((x1 + x2)^6 + (x1 - x2)^6 +
          (x1 + x3)^6 + (x1 - x3)^6 +
          (x1 + x4)^6 + (x1 - x4)^6 +
          (x2 + x3)^6 + (x2 - x3)^6 +
          (x2 + x4)^6 + (x2 - x4)^6 +
          (x3 + x4)^6 + (x3 - x4)^6) +
     36 * (x1^6 + x2^6 + x3^6 + x4^6))|>>;;

let hurwitz = polytest
 <<|5040 * (x1^2 + x2^2 + x3^2 + x4^2)^4 -
    (6 * ((x1 + x2 + x3 + x4)^8 +
          (x1 + x2 + x3 - x4)^8 +
          (x1 + x2 - x3 + x4)^8 +
          (x1 + x2 - x3 - x4)^8 +
          (x1 - x2 + x3 + x4)^8 +
          (x1 - x2 + x3 - x4)^8 +
          (x1 - x2 - x3 + x4)^8 +
          (x1 - x2 - x3 - x4)^8) +
     ((2 * x1 + x2 + x3)^8 +
      (2 * x1 + x2 - x3)^8 +
      (2 * x1 - x2 + x3)^8 +
      (2 * x1 - x2 - x3)^8 +
      (2 * x1 + x2 + x4)^8 +
      (2 * x1 + x2 - x4)^8 +
      (2 * x1 - x2 + x4)^8 +
      (2 * x1 - x2 - x4)^8 +
      (2 * x1 + x3 + x4)^8 +
      (2 * x1 + x3 - x4)^8 +
      (2 * x1 - x3 + x4)^8 +
      (2 * x1 - x3 - x4)^8 +
      (2 * x2 + x3 + x4)^8 +
      (2 * x2 + x3 - x4)^8 +
      (2 * x2 - x3 + x4)^8 +
      (2 * x2 - x3 - x4)^8 +
      (x1 + 2 * x2 + x3)^8 +
      (x1 + 2 * x2 - x3)^8 +
      (x1 - 2 * x2 + x3)^8 +
      (x1 - 2 * x2 - x3)^8 +
      (x1 + 2 * x2 + x4)^8 +
      (x1 + 2 * x2 - x4)^8 +
      (x1 - 2 * x2 + x4)^8 +
      (x1 - 2 * x2 - x4)^8 +
      (x1 + 2 * x3 + x4)^8 +
      (x1 + 2 * x3 - x4)^8 +
      (x1 - 2 * x3 + x4)^8 +
      (x1 - 2 * x3 - x4)^8 +
      (x2 + 2 * x3 + x4)^8 +
      (x2 + 2 * x3 - x4)^8 +
      (x2 - 2 * x3 + x4)^8 +
      (x2 - 2 * x3 - x4)^8 +
      (x1 + x2 + 2 * x3)^8 +
      (x1 + x2 - 2 * x3)^8 +
      (x1 - x2 + 2 * x3)^8 +
      (x1 - x2 - 2 * x3)^8 +
      (x1 + x2 + 2 * x4)^8 +
      (x1 + x2 - 2 * x4)^8 +
      (x1 - x2 + 2 * x4)^8 +
      (x1 - x2 - 2 * x4)^8 +
      (x1 + x3 + 2 * x4)^8 +
      (x1 + x3 - 2 * x4)^8 +
      (x1 - x3 + 2 * x4)^8 +
      (x1 - x3 - 2 * x4)^8 +
      (x2 + x3 + 2 * x4)^8 +
      (x2 + x3 - 2 * x4)^8 +
      (x2 - x3 + 2 * x4)^8 +
      (x2 - x3 - 2 * x4)^8) +
     60 * ((x1 + x2)^8 + (x1 - x2)^8 +
           (x1 + x3)^8 + (x1 - x3)^8 +
           (x1 + x4)^8 + (x1 - x4)^8 +
           (x2 + x3)^8 + (x2 - x3)^8 +
           (x2 + x4)^8 + (x2 - x4)^8 +
           (x3 + x4)^8 + (x3 - x4)^8) +
     6 * ((2 * x1)^8 + (2 * x2)^8 + (2 * x3)^8 + (2 * x4)^8))|>>;;

let schur = polytest
 <<|22680 * (x1^2 + x2^2 + x3^2 + x4^2)^5 -
    (9 * ((2 * x1)^10 +
          (2 * x2)^10 +
          (2 * x3)^10 +
          (2 * x4)^10) +
     180 * ((x1 + x2)^10 + (x1 - x2)^10 +
            (x1 + x3)^10 + (x1 - x3)^10 +
            (x1 + x4)^10 + (x1 - x4)^10 +
            (x2 + x3)^10 + (x2 - x3)^10 +
            (x2 + x4)^10 + (x2 - x4)^10 +
            (x3 + x4)^10 + (x3 - x4)^10) +
     ((2 * x1 + x2 + x3)^10 +
      (2 * x1 + x2 - x3)^10 +
      (2 * x1 - x2 + x3)^10 +
      (2 * x1 - x2 - x3)^10 +
      (2 * x1 + x2 + x4)^10 +
      (2 * x1 + x2 - x4)^10 +
      (2 * x1 - x2 + x4)^10 +
      (2 * x1 - x2 - x4)^10 +
      (2 * x1 + x3 + x4)^10 +
      (2 * x1 + x3 - x4)^10 +
      (2 * x1 - x3 + x4)^10 +
      (2 * x1 - x3 - x4)^10 +
      (2 * x2 + x3 + x4)^10 +
      (2 * x2 + x3 - x4)^10 +
      (2 * x2 - x3 + x4)^10 +
      (2 * x2 - x3 - x4)^10 +
      (x1 + 2 * x2 + x3)^10 +
      (x1 + 2 * x2 - x3)^10 +
      (x1 - 2 * x2 + x3)^10 +
      (x1 - 2 * x2 - x3)^10 +
      (x1 + 2 * x2 + x4)^10 +
      (x1 + 2 * x2 - x4)^10 +
      (x1 - 2 * x2 + x4)^10 +
      (x1 - 2 * x2 - x4)^10 +
      (x1 + 2 * x3 + x4)^10 +
      (x1 + 2 * x3 - x4)^10 +
      (x1 - 2 * x3 + x4)^10 +
      (x1 - 2 * x3 - x4)^10 +
      (x2 + 2 * x3 + x4)^10 +
      (x2 + 2 * x3 - x4)^10 +
      (x2 - 2 * x3 + x4)^10 +
      (x2 - 2 * x3 - x4)^10 +
      (x1 + x2 + 2 * x3)^10 +
      (x1 + x2 - 2 * x3)^10 +
      (x1 - x2 + 2 * x3)^10 +
      (x1 - x2 - 2 * x3)^10 +
      (x1 + x2 + 2 * x4)^10 +
      (x1 + x2 - 2 * x4)^10 +
      (x1 - x2 + 2 * x4)^10 +
      (x1 - x2 - 2 * x4)^10 +
      (x1 + x3 + 2 * x4)^10 +
      (x1 + x3 - 2 * x4)^10 +
      (x1 - x3 + 2 * x4)^10 +
      (x1 - x3 - 2 * x4)^10 +
      (x2 + x3 + 2 * x4)^10 +
      (x2 + x3 - 2 * x4)^10 +
      (x2 - x3 + 2 * x4)^10 +
      (x2 - x3 - 2 * x4)^10) +
     9 * ((x1 + x2 + x3 + x4)^10 +
          (x1 + x2 + x3 - x4)^10 +
          (x1 + x2 - x3 + x4)^10 +
          (x1 + x2 - x3 - x4)^10 +
          (x1 - x2 + x3 + x4)^10 +
          (x1 - x2 + x3 - x4)^10 +
          (x1 - x2 - x3 + x4)^10 +
          (x1 - x2 - x3 - x4)^10))|>>;;

(* ------------------------------------------------------------------------- *)
(* More non-trivial complex quantifier elimination.                          *)
(* ------------------------------------------------------------------------- *)

let complex_qelim_all = time complex_qelim ** generalize;;

time complex_qelim <<exists x. x + 2 = 3>>;;

time complex_qelim <<exists x. x^2 + a = 3>>;;

time complex_qelim <<exists x. x^2 + x + 1 = 0>>;;

time complex_qelim <<exists x. x^2 + x + 1 = 0 /\ x^3 + x^2 + 1 = 0>>;;

time complex_qelim <<exists x. x^2 + 1 = 0 /\ x^4 + x^3 + x^2 + x = 0>>;;

time complex_qelim 
  <<forall a x. a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 1 = 0>>;;

time complex_qelim 
  <<forall a x. a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0>>;;

time complex_qelim 
  <<exists a x. a^2 = 2 /\ x^2 + a*x + 1 = 0 /\ ~(x^4 + 2 = 0)>>;;

time complex_qelim 
  <<exists x. a^2 = 2 /\ x^2 + a*x + 1 = 0 /\ ~(x^4 + 2 = 0)>>;;

time complex_qelim <<forall x. x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0>>;;

time complex_qelim <<forall a. a^2 = 2 /\ x^2 + a*x + 1 = 0 ==> x^4 + 2 = 0>>;;

time complex_qelim <<exists a b c x y.
        a * x^2 + b * x + c = 0 /\
        a * y^2 + b * y + c = 0 /\
        ~(x = y) /\
        ~(a * x * y = c)>>;;

time complex_qelim
 <<forall y_1 y_2 y_3 y_4.
     (y_1 = 2 * y_3) /\
     (y_2 = 2 * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1^2 = y_2^2)>>;;

time complex_qelim
 <<forall x y. x^2 = 2 /\ y^2 = 3
         ==> (x * y)^2 = 6>>;;

time complex_qelim
 <<forall x a. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
         ==> (x^4 + 1 = 0)>>;;

time complex_qelim
 <<forall a x. (a^2 = 2) /\ (x^2 + a * x + 1 = 0)
         ==> (x^4 + 1 = 0)>>;;

time complex_qelim
 <<~(exists a x y. (a^2 = 2) /\
             (x^2 + a * x + 1 = 0) /\
             (y * (x^4 + 1) + 1 = 0))>>;;

time complex_qelim <<forall x. exists y. x^2 = y^3>>;;

time complex_qelim
 <<forall x y z a b. (a + b) * (x - y + z) - (a - b) * (x + y + z) =
               2 * (b * x + b * z - a * y)>>;;

time complex_qelim
 <<forall a b. ~(a = b) ==> exists x y. (y * x^2 = a) /\ (y * x^2 + x = b)>>;;

time complex_qelim
 <<forall a b c x y. (a * x^2 + b * x + c = 0) /\
               (a * y^2 + b * y + c = 0) /\
               ~(x = y)
               ==> (a * x * y = c) /\ (a * (x + y) + b = 0)>>;;

time complex_qelim
 <<~(forall a b c x y. (a * x^2 + b * x + c = 0) /\
                 (a * y^2 + b * y + c = 0)
                 ==> (a * x * y = c) /\ (a * (x + y) + b = 0))>>;;

time complex_qelim
 <<forall y_1 y_2 y_3 y_4.
     (y_1 = 2 * y_3) /\
     (y_2 = 2 * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1^2 = y_2^2)>>;;

time complex_qelim
 <<forall a1 b1 c1 a2 b2 c2.
        ~(a1 * b2 = a2 * b1)
        ==> exists x y. (a1 * x + b1 * y = c1) /\ (a2 * x + b2 * y = c2)>>;;

time complex_qelim
 <<~(forall x1 y1 x2 y2 x3 y3.
      exists x0 y0. (x1 - x0)^2 + (y1 - y0)^2 = (x2 - x0)^2 + (y2 - y0)^2 /\
                    (x2 - x0)^2 + (y2 - y0)^2 = (x3 - x0)^2 + (y3 - y0)^2)>>;;

time complex_qelim
 <<forall a b c.
      (exists x y. (a * x^2 + b * x + c = 0) /\
             (a * y^2 + b * y + c = 0) /\
             ~(x = y)) <=>
      (a = 0) /\ (b = 0) /\ (c = 0) \/
      ~(a = 0) /\ ~(b^2 = 4 * a * c)>>;;

time complex_qelim
 <<~(forall x1 y1 x2 y2 x3 y3 x0 y0 x0' y0'.
        (x1 - x0)^2 + (y1 - y0)^2 =
        (x2 - x0)^2 + (y2 - y0)^2 /\
        (x2 - x0)^2 + (y2 - y0)^2 =
        (x3 - x0)^2 + (y3 - y0)^2 /\
        (x1 - x0')^2 + (y1 - y0')^2 =
        (x2 - x0')^2 + (y2 - y0')^2 /\
        (x2 - x0')^2 + (y2 - y0')^2 =
        (x3 - x0')^2 + (y3 - y0')^2
        ==> x0 = x0' /\ y0 = y0')>>;;

time complex_qelim
 <<forall a b c.
        a * x^2 + b * x + c = 0 /\
        a * y^2 + b * y + c = 0 /\
        ~(x = y)
        ==> a * (x + y) + b = 0>>;;

time complex_qelim
 <<forall a b c.
        (a * x^2 + b * x + c = 0) /\
        (2 * a * y^2 + 2 * b * y + 2 * c = 0) /\
        ~(x = y)
        ==> (a * (x + y) + b = 0)>>;;

complex_qelim_all
 <<~(y_1 = 2 * y_3 /\
    y_2 = 2 * y_4 /\
    y_1 * y_3 = y_2 * y_4 /\
    (y_1^2 - y_2^2) * z = 1)>>;;

time complex_qelim <<forall y_1 y_2 y_3 y_4.
       (y_1 = 2 * y_3) /\
       (y_2 = 2 * y_4) /\
       (y_1 * y_3 = y_2 * y_4)
       ==> (y_1^2 = y_2^2)>>;;

complex_qelim_all
 <<(x1 = u3) /\
  (x1 * (u2 - u1) = x2 * u3) /\
  (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
  (x3 * u3 = x4 * u2) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (x3^2 + x4^2 = (u2 - x3)^2 + (u3 - x4)^2)>>;;

complex_qelim_all
 <<(u1 * x1 - u1 * u3 = 0) /\
  (u3 * x2 - (u2 - u1) * x1 = 0) /\
  (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = 0) /\
  (u3 * x4 - u2 * x3 = 0) /\
  ~(u1 = 0) /\
  ~(u3 = 0)
  ==> (2 * u2 * x4 + 2 * u3 * x3 - u3^2 - u2^2 = 0)>>;;

complex_qelim_all
 <<(y1 * y3 + x1 * x3 = 0) /\
  (y3 * (y2 - y3) + (x2 - x3) * x3 = 0) /\
  ~(x3 = 0) /\
  ~(y3 = 0)
  ==> (y1 * (x2 - x3) = x1 * (y2 - y3))>>;;

time complex_qelim 
  <<forall y.
         a * x^2 + b * x + c = 0 /\
         a * y^2 + b * y + c = 0 /\
         ~(x = y)
         ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

complex_qelim_all
 <<a * x^2 + b * x + c = 0 /\
    a * y^2 + b * y + c = 0 /\
    ~(x = y)
    ==> a * x * y = c /\ a * (x + y) + b = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Checking resultants from Maple.                                           *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
<<forall a b c.
   (exists x. a * x^2 + b * x + c = 0 /\ 2 * a * x + b = 0) \/ (a = 0) <=>
   (4*a^2*c-b^2*a = 0)>>;;

time complex_qelim
<<forall a b c d e.
  (exists x. a * x^2 + b * x + c = 0 /\ d * x + e = 0) \/
   a = 0 /\ d = 0 <=> d^2*c-e*d*b+a*e^2 = 0>>;;

time complex_qelim
<<forall a b c d e f.
   (exists x. a * x^2 + b * x + c = 0 /\ d * x^2 + e * x + f = 0) \/
   (a = 0) /\ (d = 0) <=>
   d^2*c^2-2*d*c*a*f+a^2*f^2-e*d*b*c-e*b*a*f+a*e^2*c+f*d*b^2 = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Some trigonometric addition formulas (checking stuff from Maple).         *)
(* ------------------------------------------------------------------------- *)

time complex_qelim
  <<forall x y. x^2 + y^2 = 1 ==> (2 * y^2 - 1)^2 + (2 * x * y)^2 = 1>>;;

(* ------------------------------------------------------------------------- *)
(* The examples from my thesis.                                              *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<forall s c. s^2 + c^2 = 1
      ==> 2 * s - (2 * s * c * c - s^3) = 3 * s^3>>;;

time complex_qelim <<forall u v.
  -((((9 * u^8) * v) * v - (u * u^9)) * 128) -
     (((7 * u^6) * v) * v - (u * u^7)) * 144 -
     (((5 * u^4) * v) * v - (u * u^5)) * 168 -
     (((3 * u^2) * v) * v - (u * u^3)) * 210 -
     (v * v - (u * u)) * 315 + 315 - 1280 * u^10 =
   (-(1152) * u^8 - 1008 * u^6 - 840 * u^4 - 630 * u^2 - 315) *
   (u^2 + v^2 - 1)>>;;

time complex_qelim <<forall u v.
        u^2 + v^2 = 1
        ==> (((9 * u^8) * v) * v - (u * u^9)) * 128 +
            (((7 * u^6) * v) * v - (u * u^7)) * 144 +
            (((5 * u^4) * v) * v - (u * u^5)) * 168 +
            (((3 * u^2) * v) * v - (u * u^3)) * 210 +
            (v * v - (u * u)) * 315 + 1280 * u^10 = 315>>;;

(* ------------------------------------------------------------------------- *)
(* Deliberately silly examples from Poizat's model theory book (6.6).        *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<exists z. x * z^87 + y * z^44 + 1 = 0>>;;

time complex_qelim <<forall u. exists v. x * (u + v^2)^2 + y * (u + v^2) + z = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Actually prove simple equivalences.                                       *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<forall x y. (exists z. x * z^87 + y * z^44 + 1 = 0)
                  <=> ~(x = 0) \/ ~(y = 0)>>;;

time complex_qelim <<forall x y z. (forall u. exists v.
                         x * (u + v^2)^2 + y * (u + v^2) + z = 0)
                    <=> ~(x = 0) \/ ~(y = 0) \/ z = 0>>;;

(* ------------------------------------------------------------------------- *)
(* Invertibility of 2x2 matrix in terms of nonzero determinant.              *)
(* ------------------------------------------------------------------------- *)

time complex_qelim <<exists w x y z. (a * w + b * y = 1) /\
                      (a * x + b * z = 0) /\
                      (c * w + d * y = 0) /\
                      (c * x + d * z = 1)>>;;

time complex_qelim <<forall a b c d.
        (exists w x y z. (a * w + b * y = 1) /\
                         (a * x + b * z = 0) /\
                         (c * w + d * y = 0) /\
                         (c * x + d * z = 1))
        <=> ~(a * d = b * c)>>;;

END_INTERACTIVE;;
