(* ========================================================================= *)
(* Knuth-Bendix completion.                                                  *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

let renamepair (fm1,fm2) =
  let fvs1 = fv fm1
  and fvs2 = fv fm2 in
  let nms1,nms2 =
     chop_list(length fvs1)
              (map (fun n -> Var("x"^string_of_int n))
                   (0 -- (length fvs1 + length fvs2 - 1))) in
  formsubst (itlist2 (fun x t -> x |-> t) fvs1 nms1 undefined) fm1,
  formsubst (itlist2 (fun x t -> x |-> t) fvs2 nms2 undefined) fm2;;

(* ------------------------------------------------------------------------- *)
(* Rewrite (using unification) with l = r inside tm to give a critical pair. *)
(* ------------------------------------------------------------------------- *)

let rec listcases fn rfn lis acc =
  match lis with
    [] -> acc
  | h::t -> fn h (fun i h' -> rfn i (h'::t)) @
            listcases fn (fun i t' -> rfn i (h::t')) t acc;;

let rec overlaps (l,r) tm rfn =
  match tm with
    Fn(f,args) ->
        listcases (overlaps (l,r)) (fun i a -> rfn i (Fn(f,a))) args
                  (try [rfn (fullunify [l,tm]) r] with Failure _ -> [])
  | Var x -> [];;

(* ------------------------------------------------------------------------- *)
(* Generate all critical pairs between two equations.                        *)
(* ------------------------------------------------------------------------- *)

let crit1 (Atom(R("=",[l1;r1]))) (Atom(R("=",[l2;r2]))) =
  overlaps (l1,r1) l2 (fun i t -> formsubst i (Atom(R("=",[t;r2]))));;

let critical_pairs fma fmb =
  let fm1,fm2 = renamepair (fma,fmb) in
  if fma = fmb then crit1 fm1 fm2
  else union (crit1 fm1 fm2) (crit1 fm2 fm1);;

(* ------------------------------------------------------------------------- *)
(* Simple example.                                                           *)
(* ------------------------------------------------------------------------- *)

let eq = <<f(f(x)) = g(x)>>;;
START_INTERACTIVE;;
critical_pairs eq eq;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Orienting an equation.                                                    *)
(* ------------------------------------------------------------------------- *)

let normalize_and_orient ord eqs =
  fun (Atom(R("=",[s;t]))) ->
    let s' = depth(rewrite eqs) s and t' = depth(rewrite eqs) t in
    if ord s' t' then (s',t') else if ord t' s' then (t',s')
    else failwith "Can't orient equation";;

(* ------------------------------------------------------------------------- *)
(* Status report so the user doesn't get too bored.                          *)
(* ------------------------------------------------------------------------- *)

let status(eqs,def,crs) eqs0 =
  if eqs = eqs0 & (length crs) mod 1000 <> 0 then () else
  (print_string(string_of_int(length eqs)^" equations and "^
                string_of_int(length crs)^" pending critical pairs + "^
                string_of_int(length def)^" deferred");
   print_newline());;

(* ------------------------------------------------------------------------- *)
(* Completion main loop (deferring non-orientable equations).                *)
(* ------------------------------------------------------------------------- *)

let rec complete ord (eqs,def,crits) =
  match crits with
    (eq::ocrits) ->
        let trip =
          try let (s',t') = normalize_and_orient ord eqs eq in
              if s' = t' then (eqs,def,ocrits) else
              let eq' = Atom(R("=",[s';t'])) in
              let eqs' = eq'::eqs in
              eqs',def,
              ocrits @ itlist ((@) ** critical_pairs eq') eqs' []
          with Failure _ -> (eqs,eq::def,ocrits) in
        status trip eqs; complete ord trip
  | _ -> if def = [] then eqs else
         let e = find (can (normalize_and_orient ord eqs)) def in
         complete ord (eqs,subtract def [e],[e]);;

(* ------------------------------------------------------------------------- *)
(* A simple "manual" example, before considering packaging and refinements.  *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<1 * x = x>>; <<i(x) * x = 1>>; <<(x * y) * z = x * y * z>>];;

let ord = lpo_ge (weight ["1"; "*"; "i"]);;

START_INTERACTIVE;;
let eqs' = complete ord
  (eqs,[],unions(allpairs critical_pairs eqs eqs));;

let tm = <<|i(x * i(x)) * (i(i((y * z) * u) * y) * i(u))|>>;;

depth(rewrite eqs') tm;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Show that we get a significant difference just from changing order.       *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let eqs =
 [<<(x * y) * z = x * y * z>>; <<1 * x = x>>; <<i(x) * x = 1>>];;

let eqs'' = complete ord
  (eqs,[],unions(allpairs critical_pairs eqs eqs));;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Interreduction.                                                           *)
(* ------------------------------------------------------------------------- *)

let rec interreduce ord dun eqs =
  match eqs with
    (Atom(R("=",[l;r])))::oeqs ->
        let rewr_fn = depth(rewrite (dun @ oeqs)) in
        if rewr_fn l <> l then interreduce ord dun oeqs
        else interreduce ord (Atom(R("=",[l;rewr_fn r]))::dun) oeqs
  | [] -> rev dun
  | _ -> failwith "non-equational input";;

(* ------------------------------------------------------------------------- *)
(* This does indeed help a lot.                                              *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
interreduce ord [] eqs';;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Overall function with post-simplification (but not dynamically).          *)
(* ------------------------------------------------------------------------- *)

let complete_and_simplify wts eqs =
  let ord = lpo_ge (weight wts) in
  if exists (fun (Atom(R("=",[l;r]))) -> ord r l) eqs
  then failwith "Initial equations not ordered by given ordering" else
    (interreduce ord [] ** complete ord)
    (eqs,[],unions(allpairs critical_pairs eqs eqs));;

(* ------------------------------------------------------------------------- *)
(* Central groupoids (K&B example 6).                                        *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let eqs =  [<<(a * b) * (b * c) = b>>];;

complete_and_simplify ["*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Inverse property (K&B example 4).                                         *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<i(a) * (a * b) = b>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary result used to justify extension for example 9.                 *)
(* ------------------------------------------------------------------------- *)

(meson ** equalitize)
 <<(forall x y z. x * y = x * z ==> y = z) <=>
   (forall x z. exists w. forall y. z = x * y ==> w = y)>>;;

skolemize <<forall x z. exists w. forall y. z = x * y ==> w = y>>;;

let eqs =
  [<<f(a,a*b) = b>>; <<g(a*b,b) = a>>; <<1 * a = a>>; <<a * 1 = a>>];;

complete_and_simplify ["1"; "*"; "f"; "g"] eqs;;

(* ------------------------------------------------------------------------- *)
(* K&B example 7, where we need to divide through.                           *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<f(a,f(b,c,a),d) = c>>; <<f(a,b,c) = g(a,b)>>;
                     <<g(a,b) = h(b)>>];;

complete_and_simplify ["h"; "g"; "f"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Group theory I (K & B example 1).                                         *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<1 * x = x>>; <<i(x) * x = 1>>; <<(x * y) * z = x * y * z>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Inverse property (K&B example 4).                                         *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<i(a) * (a * b) = b>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

let eqs =  [<<a * (i(a) * b) = b>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* The cancellation law (K&B example 9).                                     *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<f(a,a*b) = b>>; <<g(a*b,b) = a>>];;

complete_and_simplify ["*"; "f"; "g"] eqs;;

let eqs =
  [<<f(a,a*b) = b>>; <<g(a*b,b) = a>>; <<1 * a = a>>; <<a * 1 = a>>];;

complete_and_simplify ["1"; "*"; "f"; "g"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Loops (K&B example 10).                                                   *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<a * \(a,b) = b>>; <</(a,b) * b = a>>; <<1 * a = a>>; <<a * 1 = a>>];;

complete_and_simplify ["1"; "*"; "\\"; "/"] eqs;;

let eqs =
 [<<a * \(a,b) = b>>; <</(a,b) * b = a>>; <<1 * a = a>>; <<a * 1 = a>>;
  <<f(a,a*b) = b>>; <<g(a*b,b) = a>>];;

complete_and_simplify ["1"; "*"; "\\"; "/"; "f"; "g"] eqs;;

(* ------------------------------------------------------------------------- *)
(* (r,l)-systems (K&B example 13).                                           *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(x * y) * z = x * y * z>>; <<x * 1 = x>>; <<i(x) * x = 1>>];;

complete_and_simplify ["1"; "*"; "i"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Central groupoids II. (K&B example 16).                                   *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(a * a) * a = one(a)>>;
  <<a * (a * a) = two(a)>>;
  <<(a * b) * (b * c) = b>>;
  <<two(a) * b = a * b>>];;

complete_and_simplify ["one"; "two"; "*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Simply congruence closure.                                                *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<f(f(f(f(f(1))))) = 1>>; <<f(f(f(1))) = 1>>];;

complete_and_simplify ["1"; "f"] eqs;;

(* ------------------------------------------------------------------------- *)
(* A rather simple example from Baader & Nipkow, p. 141.                     *)
(* ------------------------------------------------------------------------- *)

let eqs =  [<<f(f(x)) = g(x)>>];;

complete_and_simplify ["g"; "f"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Some of the exercises (these are taken from Baader & Nipkow).             *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<f(f(x)) = f(x)>>;
  <<g(g(x)) = f(x)>>;
  <<f(g(x)) = g(x)>>;
  <<g(f(x)) = f(x)>>];;

complete_and_simplify ["f"; "g"] eqs;;

let eqs =  [<<f(g(f(x))) = g(x)>>];;

complete_and_simplify ["f"; "g"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Inductive theorem proving example.                                        *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<0 + y = y>>;
  <<SUC(x) + y = SUC(x + y)>>;
  <<append(nil,l) = l>>;
  <<append(h::t,l) = h::append(t,l)>>;
  <<length(nil) = 0>>;
  <<length(h::t) = SUC(length(t))>>;
  <<rev(nil) = nil>>;
  <<rev(h::t) = append(rev(t),h::nil)>>];;

complete_and_simplify
   ["0"; "nil"; "SUC"; "::"; "+"; "length"; "append"; "rev"] eqs;;

let iprove eqs' tm =
 complete_and_simplify
   ["0"; "nil"; "SUC"; "::"; "+"; "append"; "rev"; "length"]
   (tm :: eqs' @ eqs);;

iprove [] <<x + 0 = x>>;;

iprove [] <<x + SUC(y) = SUC(x + y)>>;;

iprove [] <<(x + y) + z = x + y + z>>;;

iprove [] <<length(append(x,y)) = length(x) + length(y)>>;;

iprove [] <<append(append(x,y),z) = append(x,append(y,z))>>;;

iprove [] <<append(x,nil) = x>>;;

iprove [<<append(append(x,y),z) = append(x,append(y,z))>>;
        <<append(x,nil) = x>>]
        <<rev(append(x,y)) = append(rev(y),rev(x))>>;;

iprove [<<rev(append(x,y)) = append(rev(y),rev(x))>>;
        <<append(x,nil) = x>>;
        <<append(append(x,y),z) = append(x,append(y,z))>>]
        <<rev(rev(x)) = x>>;;

(* ------------------------------------------------------------------------- *)
(* Here it's not immediately so obvious since we get extra equs.             *)
(* ------------------------------------------------------------------------- *)

iprove [] <<rev(rev(x)) = x>>;;

END_INTERACTIVE;;
