(* ========================================================================= *)
(* Paramodulation.                                                           *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

let rec overlapv (l,r) tm rfn =
  match tm with
    Fn(f,args) ->
        listcases (overlapv (l,r)) (fun i a -> rfn i (Fn(f,a))) args
                  (try [rfn (fullunify [l,tm]) r] with Failure _ -> [])
  | Var x -> [rfn (fullunify [l,tm]) r];;

(* ------------------------------------------------------------------------- *)
(* Find paramodulations with l = r inside a literal fm.                      *)
(* ------------------------------------------------------------------------- *)

let rec overlapl (l,r) fm rfn =
  match fm with
    Atom(R(f,args)) -> listcases (overlapv (l,r))
                              (fun i a -> rfn i (Atom(R(f,a)))) args []
  | Not(p) -> overlapl (l,r) p (fun i p -> rfn i (Not(p)))
  | _ -> failwith "overlapl: not a literal";;

(* ------------------------------------------------------------------------- *)
(* Now find paramodulations within a clause.                                 *)
(* ------------------------------------------------------------------------- *)

let overlapc (l,r) cl rfn acc = listcases (overlapl (l,r)) rfn cl acc;;

(* ------------------------------------------------------------------------- *)
(* Overall paramodulation of ocl by equations in pcl.                        *)
(* ------------------------------------------------------------------------- *)

let paramodulate pcl ocl =
  itlist (fun eq ->
                let pcl' = subtract pcl [eq] in
                let (l,r) = dest_eq eq
                and rfn i ocl' = smap (formsubst i) (pcl' @ ocl') in
                overlapc (l,r) ocl rfn ** overlapc (r,l) ocl rfn)
         (filter (can dest_eq) pcl) [];;

let paramodulate_clauses cls1 cls2 =
  let cls1' = rename "x" cls1 and cls2' = rename "y" cls2 in
  paramodulate cls1' cls2' @ paramodulate cls2' cls1';;

(* ------------------------------------------------------------------------- *)
(* Incorporation into resolution loop.                                       *)
(* ------------------------------------------------------------------------- *)

let rec paraloop (used,unused) =
  match unused with
    [] -> failwith "No proof found"
  | cls::ros ->
        print_string(string_of_int(length used) ^ " used; "^
                     string_of_int(length unused) ^ " unused.");
        print_newline();
        let used' = insert cls used in
        let news =
          itlist (@) (mapfilter (resolve_clauses cls) used')
            (itlist (@) (mapfilter (paramodulate_clauses cls) used') []) in
        if mem [] news then true else
        paraloop(used',itlist (incorporate cls) news ros);;

let pure_paramodulation fm =
  paraloop([],[Atom(R("=",[Var "x"; Var "x"]))]::
              (filter (non tautologous)
                      (clausal(specialize(pnf fm)))));;

let paramodulation fm =
  let fm1 = askolemize(Not(generalize fm)) in
  map (pure_paramodulation ** list_conj) (simpdnf fm1);;

(* ------------------------------------------------------------------------- *)
(* Test.                                                                     *)
(* ------------------------------------------------------------------------- *)

let ewd =
 <<(forall x. f(x) ==> g(x)) /\
   (exists x. f(x)) /\
   (forall x y. g(x) /\ g(y) ==> x = y)
   ==> forall y. g(y) ==> f(y)>>;;

START_INTERACTIVE;;
paramodulation ewd;;
END_INTERACTIVE;;

let fm =
 <<forall c. f(f(f(f(f(c))))) = c /\ f(f(f(c))) = c ==> f(c) = c>>;;

START_INTERACTIVE;;
paramodulation fm;;
END_INTERACTIVE;;

let ewd' =
 <<(forall x. f(f(x)) = f(x)) /\ (forall x. exists y. f(y) = x)
   ==> forall x. f(x) = x>>;;

START_INTERACTIVE;;
paramodulation ewd';;
END_INTERACTIVE;;
