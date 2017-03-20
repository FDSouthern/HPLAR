(* ========================================================================= *)
(* Geometry theorem proving.                                                 *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* List of geometric properties with their coordinate translations.          *)
(* ------------------------------------------------------------------------- *)

let coordinations =
  ["collinear",
   <<(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x)>>;
   "parallel",
    <<(1_x - 2_x) * (3_y - 4_y) = (1_y - 2_y) * (3_x - 4_x)>>;
   "perpendicular",
   <<(1_x - 2_x) * (3_x - 4_x) + (1_y - 2_y) * (3_y - 4_y) = 0>>;
   "lengths_eq",
   <<(1_x - 2_x)^2 + (1_y - 2_y)^2 = (3_x - 4_x)^2 + (3_y - 4_y)^2>>;
   "is_midpoint",
   <<2 * 1_x = 2_x + 3_x /\ 2 * 1_y = 2_y + 3_y>>;
   "is_intersection",
   <<(1_x - 2_x) * (2_y - 3_y) = (1_y - 2_y) * (2_x - 3_x) /\
     (1_x - 4_x) * (4_y - 5_y) = (1_y - 4_y) * (4_x - 5_x)>>;
   "=",<<(1_x = 2_x) /\ (1_y = 2_y)>>;
   "angles_eq",
   <<((2_y - 1_y) * (2_x - 3_x) - (2_y - 3_y) * (2_x - 1_x)) *
     ((5_x - 4_x) * (5_x - 6_x) + (5_y - 4_y) * (5_y - 6_y)) =
     ((5_y - 4_y) * (5_x - 6_x) - (5_y - 6_y) * (5_x - 4_x)) *
     ((2_x - 1_x) * (2_x - 3_x) + (2_y - 1_y) * (2_y - 3_y))>>];;

(* ------------------------------------------------------------------------- *)
(* Convert formula into coordinate form.                                     *)
(* ------------------------------------------------------------------------- *)

let inst_coord fms pat =
  let xtms,ytms = unzip
    (map (fun (Var v) -> Var(v^"_x"),Var(v^"_y")) fms) in
  let xs = map (fun n -> string_of_int n^"_x") (1--length fms)
  and ys = map (fun n -> string_of_int n^"_y") (1--length fms) in
  formsubst (instantiate (xs @ ys) (xtms @ ytms)) pat;;

let coordinate fm = onatoms
  (fun (R(a,args)) -> inst_coord args (assoc a coordinations)) fm;;

(* ------------------------------------------------------------------------- *)
(* Trivial example.                                                          *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
coordinate <<collinear(a,b,c) ==> collinear(b,a,c)>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Verify equivalence under rotation.                                        *)
(* ------------------------------------------------------------------------- *)

let test_invariance(_,fm) =
  let modify s c x y =
    formsubst(instantiate [x;y]
              [Fn("-",[Fn("*",[c; Var x]); Fn("*",[s; Var y])]);
               Fn("+",[Fn("*",[c; Var y]); Fn("*",[s; Var x])])]) in
  let s = <<|s|>> and c = <<|c|>>
  and eq = <<s^2 + c^2 = 1>> in
  let fm' = itlist (fun n -> modify s c (n^"_x") (n^"_y"))
                   (map string_of_int (1--6)) fm in
  let equiv = Imp(eq,Iff(fm',fm)) in
  grobner_decide equiv;;

START_INTERACTIVE;;
forall test_invariance coordinations;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* And show we can always invent such a transformation to zero a y:          *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
real_qelim
 <<forall x y. exists s c. s^2 + c^2 = 1 /\ s * x + c * y = 0>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Choose one point to be the origin and rotate to zero another x coordinate *)
(* ------------------------------------------------------------------------- *)

let originate fm =
  let a::b::ovs as vars = fv fm in
  let rfn = itlist (fun v -> v |-> Fn("0",[]))
                   [a^"_x"; a^"_y"; b^"_y"] undefined in
  formsubst rfn (coordinate fm);;

(* ------------------------------------------------------------------------- *)
(* Invariance under shearing, hence any affine xform, for many properties.   *)
(* ------------------------------------------------------------------------- *)

let test_str_invariance(_,fm) =
  let a = <<|a|>> and b = <<|b|>>
  and c = <<|c|>> and d = <<|d|>> in
  let modify x y =
    formsubst
      (x := Fn("+",[Fn("*",[Fn("1",[]); Var x]); Fn("*",[b; Var y])])) in
  let fm' = itlist (fun n -> modify (n^"_x") (n^"_y"))
                   (map string_of_int (1--6)) fm in
  let equiv = Iff(fm',fm) in
  grobner_decide equiv;;

START_INTERACTIVE;;
map (fun a -> fst a,test_str_invariance a) (butlast coordinations);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Examples of inadequacy but fixability of complex coordinates.             *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
(grobner_decide ** originate)
 <<lengths_eq(A,X,B,X) /\ lengths_eq(B,X,C,X) /\
   lengths_eq(A,Y,B,Y) /\ lengths_eq(B,Y,C,Y) /\
   ~(A = B) /\ ~(A = C) /\ ~(B = C) ==> X = Y>>;;

(* ------------------------------------------------------------------------- *)
(* Centroid (Chou, example 142).                                             *)
(* ------------------------------------------------------------------------- *)

(grobner_decide ** originate)
 <<is_midpoint(d,b,c) /\
   is_midpoint(e,a,c) /\
   is_midpoint(f,a,b) /\
   is_intersection(m,b,e,a,d)
   ==> collinear(c,f,m)>>;;

(* ------------------------------------------------------------------------- *)
(* One from "Algorithms for Computer Algebra"                                *)
(* ------------------------------------------------------------------------- *)

(grobner_decide ** originate)
 <<is_midpoint(m,a,c) /\ perpendicular(a,c,m,b)
   ==> lengths_eq(a,b,b,c)>>;;

(* ------------------------------------------------------------------------- *)
(* Parallelogram theorem (Chou's expository example at the start).           *)
(* ------------------------------------------------------------------------- *)

(grobner_decide ** originate)
 <<parallel(a,b,d,c) /\ parallel(a,d,b,c) /\ is_intersection(e,a,c,b,d)
   ==> lengths_eq(a,e,e,c)>>;;

(grobner_decide ** originate)
 <<parallel(a,b,d,c) /\ parallel(a,d,b,c) /\
   is_intersection(e,a,c,b,d) /\ ~collinear(a,b,c)
   ==> lengths_eq(a,e,e,c)>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Reduce p using triangular set, collecting degenerate conditions.          *)
(* ------------------------------------------------------------------------- *)

let rec pprove vars triang p degens =
  if p = Fn("0",[]) then degens else
  match triang with
    [] -> Atom(R("=",[p;Fn("0",[])]))::degens
  | (Fn("+",[c;Fn("*",[Var x;_])]) as q)::qs ->
        if x <> hd vars then
          if mem (hd vars) (fvt p)
          then itlist (pprove vars triang) (coefficients vars p) degens
          else pprove (tl vars) triang p degens
        else
          let k,p' = pdivide vars p q in
          if k = 0 then pprove vars qs p' degens else
          let degens' =
            Not(Atom(R("=",[head vars q; Fn("0",[])])))::degens in
          if is_constant vars p' then pprove vars qs p' degens' else
          itlist (pprove vars qs) (coefficients vars p') degens'
  | (q::qs) -> Not(Or(False,Atom(R("=",[q; Fn("0",[])]))))::degens;;

(* ------------------------------------------------------------------------- *)
(* Triangulate a set of polynomials.                                         *)
(* ------------------------------------------------------------------------- *)

let rec triangulate vars consts pols =
  if vars = [] then pols
  else if pols = [] then triangulate (tl vars) [] consts else
  let cns,tpols = partition (is_constant vars) pols in
  if cns <> [] then triangulate vars (cns @ consts) tpols else
  if length pols = 1 then pols @ triangulate (tl vars) [] consts else
  let n = end_itlist min (map (degree vars) pols) in
  let p = find (fun p -> degree vars p = n) pols in
  let ps = subtract pols [p] in
  if n = 1 then
    p :: (triangulate (tl vars) []
            (consts @ map (fun q -> snd(pdivide vars q p)) ps))
  else
    let m = end_itlist min (map (degree vars) ps) in
    let q = find (fun q -> degree vars q = m) ps in
    let qs = subtract ps [q] in
    let rs = p::(snd(pdivide vars q p))::qs in
    triangulate vars consts rs;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary stuff.                                                          *)
(* ------------------------------------------------------------------------- *)

let dest_imp fm =
  match fm with
    Imp(p,q) -> p,q
  | _ -> failwith "dest_imp";;

let lhs eq = fst(dest_eq eq) and rhs eq = snd(dest_eq eq);;

(* ------------------------------------------------------------------------- *)
(* Trivial version of Wu's method based on repeated pseudo-division.         *)
(* ------------------------------------------------------------------------- *)

let wu fm vars zeros =
  let gfm0 = coordinate fm in
  let gfm = formsubst
    (itlist (fun v -> v |-> Fn("0",[])) zeros undefined) gfm0 in
  if not (set_eq vars (fv gfm))
  then failwith "wu: wrong variable set" else
  let ant,con = dest_imp gfm in
  let pols = map (lhs ** polyatom vars) (conjuncts ant)
  and ps = map (lhs ** polyatom vars) (conjuncts con) in
  let tri = triangulate vars [] pols in
  itlist (fun p -> union(pprove vars tri p [])) ps [];;

(* ------------------------------------------------------------------------- *)
(* Simson's theorem.                                                         *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let simson =
 <<lengths_eq(o,a,o,b) /\
   lengths_eq(o,a,o,c) /\
   lengths_eq(o,a,o,d) /\
   collinear(e,b,c) /\
   collinear(f,a,c) /\
   collinear(g,a,b) /\
   perpendicular(b,c,d,e) /\
   perpendicular(a,c,d,f) /\
   perpendicular(a,b,d,g)
   ==> collinear(e,f,g)>>;;

let vars =
 ["g_y"; "g_x"; "f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x"; "c_y"; "c_x";
  "b_y"; "b_x"; "o_x"]
and zeros = ["a_x"; "a_y"; "o_y"];;

wu simson vars zeros;;

(* ------------------------------------------------------------------------- *)
(* Try without special coordinates.                                          *)
(* ------------------------------------------------------------------------- *)

wu simson (vars @ zeros) [];;

(* ------------------------------------------------------------------------- *)
(* Pappus (Chou's figure 6).                                                 *)
(* ------------------------------------------------------------------------- *)

let pappus =
 <<collinear(a1,b2,d) /\
   collinear(a2,b1,d) /\
   collinear(a2,b3,e) /\
   collinear(a3,b2,e) /\
   collinear(a1,b3,f) /\
   collinear(a3,b1,f)
   ==> collinear(d,e,f)>>;;

let vars = ["f_y"; "f_x"; "e_y"; "e_x"; "d_y"; "d_x";
            "b3_y"; "b2_y"; "b1_y"; "a3_x"; "a2_x"; "a1_x"]
and zeros = ["a1_y"; "a2_y"; "a3_y"; "b1_x"; "b2_x"; "b3_x"];;

wu pappus vars zeros;;

(* ------------------------------------------------------------------------- *)
(* Without special coordinates.                                              *)
(* ------------------------------------------------------------------------- *)

let pappus =
 <<collinear(a1,a2,a3) /\
   collinear(b1,b2,b3) /\
   collinear(a1,b2,d) /\
   collinear(a2,b1,d) /\
   collinear(a2,b3,e) /\
   collinear(a3,b2,e) /\
   collinear(a1,b3,f) /\
   collinear(a3,b1,f)
   ==> collinear(d,e,f)>>;;

wu pappus (vars @ zeros) [];;

END_INTERACTIVE;;
