(* ========================================================================= *)
(* Ordered rewriting.                                                        *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Rewriting constrained by ordering.                                        *)
(* ------------------------------------------------------------------------- *)

let orewrite1 ord eq t =
  match eq with
    (Atom(R("=",[l;r]))) ->
        let t' = termsubst (term_match l t) r in
        if ord t t' then t' else failwith "orewrite1: not ordered"
  | _ -> failwith "orewrite1: not an equation";;

(* ------------------------------------------------------------------------- *)
(* Rewriting with set of ordered and unordered equations.                    *)
(* ------------------------------------------------------------------------- *)

let orewrite ord (oeqs,ueqs) tm =
  try tryfind (fun eq -> rewrite1 eq tm) oeqs
  with Failure _ -> tryfind (fun eq -> orewrite1 ord eq tm) ueqs;;

(* ------------------------------------------------------------------------- *)
(* Split equations into orientable and non-orientable; orient the former.    *)
(* ------------------------------------------------------------------------- *)

let tryorient ord (Atom(R("=",[l;r])) as eq) (oeqs,ueqs) =
  if ord l r then (eq::oeqs,ueqs)
  else if ord r l then (Atom(R("=",[r;l]))::oeqs,ueqs)
  else (oeqs,eq::ueqs);;

(* ------------------------------------------------------------------------- *)
(* Evaluate "hypothetical" LPO based on ordering of variables.               *)
(* ------------------------------------------------------------------------- *)

let rec lpoh_gt vord w s t =
  match (s,t) with
    (Var y,Var x) -> vord y > vord x
  | (_,Var x) -> exists (fun y -> vord y >= vord x) (fvt s)
  | (Fn(f,fargs),Fn(g,gargs)) ->
        exists (fun si -> lpoh_ge vord w si t) fargs or
        forall (lpoh_gt vord w s) gargs &
        (f = g & lexord (lpoh_gt vord w) fargs gargs or
         w (f,length fargs) (g,length gargs))
    | _ -> false

and lpoh_ge vord w s t = (s = t) or lpoh_gt vord w s t;;

(* ------------------------------------------------------------------------- *)
(* All ways to identify subsets of the variables in a formula.               *)
(* ------------------------------------------------------------------------- *)

let allpartitions =
  let allinsertions x l acc =
    itlist (fun p acc -> ((x::p)::(subtract l [p])) :: acc) l
           (([x]::l)::acc) in
  fun l -> itlist (fun h y -> itlist (allinsertions h) y []) l [[]];;

let identify vars fn =
  let x = Var(hd vars) in itlist (fun v -> v |-> x) vars fn;;

let allidentifications fm =
  let fvs = fv fm in
  map (fun p -> formsubst(itlist identify p undefined) fm)
      (allpartitions fvs);;

(* ------------------------------------------------------------------------- *)
(* Find all orderings of variables.                                          *)
(* ------------------------------------------------------------------------- *)

let rec allpermutations l =
  if l = [] then [[]] else
  itlist (fun h acc -> map (fun t -> h::t)
                (allpermutations (subtract l [h])) @ acc) l [];;

let allvarorders l =
  map (fun vlis x -> index x vlis) (allpermutations l);;

(* ------------------------------------------------------------------------- *)
(* Test critical triple for joinability under all variable orders.           *)
(* ------------------------------------------------------------------------- *)

let ojoinable ord oueqs (Atom(R("=",[s;t]))) =
  depth (orewrite ord oueqs) s = depth (orewrite ord oueqs) t;;

let allojoinable w oueqs eq =
  forall (fun eq' ->
            forall (fun vord -> ojoinable (lpoh_gt vord w) oueqs eq')
                   (allvarorders(fv eq')))
         (allidentifications eq);;

(* ------------------------------------------------------------------------- *)
(* Find the critical pairs not joinable by naive variable order splits.      *)
(* ------------------------------------------------------------------------- *)

let rec unjoined w ((oeqs,ueqs as oueqs),unj,critts) =
  match critts with
    (Atom(R("=",[s;t])) as eq)::ocritts ->
        let s' = depth (orewrite ord oueqs) s
        and t' = depth (orewrite ord oueqs) t in
        if s' = t' then unjoined w (oueqs,unj,ocritts)
        else if allojoinable w oueqs eq
        then unjoined w (oueqs,unj,ocritts)
        else unjoined w (oueqs,Atom(R("=",[s';t']))::unj,ocritts)
  | [] -> unj;;

(* ------------------------------------------------------------------------- *)
(* Overall function to return possibly-unjoinable critical pairs.            *)
(* ------------------------------------------------------------------------- *)

let unjoinables plis eqs =
  let w = weight plis in
  let ord = lpo_gt w in
  let oueqs = itlist (tryorient ord) eqs ([],[]) in
  let critts = unions (allpairs critical_pairs eqs eqs) in
  unjoined w (oueqs,[],critts);;

(* ------------------------------------------------------------------------- *)
(* Example: pure AC.                                                         *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let eqs = [<<x * y = y * x>>; <<(x * y) * z = x * y * z>>];;

unjoinables ["*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* 4.2: associativity and commutativity.                                     *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<x * y = y * x>>;
  <<(x * y) * z = x * y * z>>;
  <<x * y * z = y * x * z>>];;

unjoinables ["*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Example of normalizing expressions.                                       *)
(* ------------------------------------------------------------------------- *)

let ord = lpo_gt (fun (s,n) (s',n') -> s > s' or s = s' & n > n');;

let acnorm =
  depth(orewrite ord (itlist (tryorient ord) eqs ([],[])));;

acnorm <<|(4 * 3) * (1 * 5 * 1 * 2)|>>;;

(* ------------------------------------------------------------------------- *)
(* 4.4: associativity, commutativity and idempotence.                        *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(x * y) * z = x * y * z>>;
  <<x * y = y * x>>;
  <<x * (y * z) = y * (x * z)>>;
  <<x * x = x>>;
  <<x * (x * y) = x * y>>];;

unjoinables ["*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* 4.8: Boolean rings.                                                       *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<x + y = y + x>>;               <<x * y = y * x>>;
  <<x + y + z = y + x + z>>;       <<x * y * z = y * x * z>>;
  <<x + x = 0>>;                   <<x + 0 = x>>;
  <<0 + x = x>>;                   <<x * x = x>>;
  <<1 * x = x>>;                   <<x * 1 = x>>;
  <<x * 0 = 0>>;                   <<0 * x = 0>>;
  <<(x * y) * z = x * y * z>>;      <<(x + y) + z = x + y + z>>;
  <<x * (y + z) = x * y + x * z>>; <<(x + y) * z = x * z + y * z>>;
  <<x * (x * y) = x * y>>;         <<x + (x + y) = y>>];;

unjoinables ["0"; "1"; "+"; "*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* Translation to propositional logic.                                       *)
(* ------------------------------------------------------------------------- *)

let rec prop_of_boolterm tm =
  match tm with
    Fn("+",[p;q]) -> Not(Iff(prop_of_boolterm p,prop_of_boolterm q))
  | Fn("*",[p;q]) -> And(prop_of_boolterm p,prop_of_boolterm q)
  | Fn("0",[]) -> False
  | Fn("1",[]) -> True
  | Var x -> Atom(R(x,[]));;

let prop_of_bool (Atom(R("=",[s;t]))) =
  Iff(prop_of_boolterm s,prop_of_boolterm t);;

forall tautology (map prop_of_bool eqs);;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Translation back.                                                         *)
(* ------------------------------------------------------------------------- *)

let rec bool_of_prop fm =
  match fm with
    False -> Fn("0",[])
  | True -> Fn("1",[])
  | Atom(R(p,[])) -> Fn(p,[])
  | Not(p) -> Fn("+",[bool_of_prop p; Fn("1",[])])
  | And(p,q) -> Fn("*",[bool_of_prop p; bool_of_prop q])
  | Or(p,q) -> let p' = bool_of_prop p and q' = bool_of_prop q in
               Fn("+",[p'; Fn("+",[q'; Fn("*",[p';q'])])])
  | Imp(p,q) -> bool_of_prop(Or(Not p,q))
  | Iff(p,q) -> let p' = bool_of_prop p and q' = bool_of_prop q in
                Fn("+",[p'; Fn("+",[q'; Fn("1",[])])]);;

(* ------------------------------------------------------------------------- *)
(* Canonical simplifier for Boolean rings.                                   *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let ord =
  let w f g =
    match (f,g) with
      (("*",2),("+",2)) -> true
    | ((_,2),(_,0)) -> true
    | ((s,0),(s',0)) -> s > s'
    | _ -> false in
  lpo_gt w;;

let boolnorm =
  depth(orewrite ord (itlist (tryorient ord) eqs ([],[])));;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

boolnorm (bool_of_prop <<p /\ q \/ ~p \/ ~q>>);;

boolnorm (bool_of_prop <<(p ==> q) \/ (q ==> p)>>);;

boolnorm (bool_of_prop <<p \/ q ==> q \/ (p <=> q)>>);;

(* ------------------------------------------------------------------------- *)
(* 4.5: Groups of exponent two                                               *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(x * y) * z = x * y * z>>;
  <<x * y = y * x>>;
  <<x * (y * z) = y * (x * z)>>;
  <<x * x = 1>>;
  <<x * (x * y) = y>>;
  <<x * 1 = x>>;
  <<1 * x = x>>];;

unjoinables ["1"; "*"] eqs;;

(* ------------------------------------------------------------------------- *)
(* 4.7: Distributivity.                                                      *)
(* ------------------------------------------------------------------------- *)

let eqs =
 [<<(x * y) * z = x * y * z>>;
  <<x * y = y * x>>;
  <<x * y * z = y * x * z>>;
  <<x * (y + z) = x * y + x * z>>;
  <<(x + y) * z = x * z + y * z>>];;

unjoinables ["+"; "*"] eqs;;

END_INTERACTIVE;;
