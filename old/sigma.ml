(* ========================================================================= *)
(* Evaluation of Sigma-sentences by proof, and other oddments.               *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Produce numeral in zero-successor form.                                   *)
(* ------------------------------------------------------------------------- *)

let rec numeral n =
  if n =/ Int 0 then Fn("0",[])
  else Fn("S",[numeral(n -/ Int 1)]);;

(* ------------------------------------------------------------------------- *)
(* Injective pairing function with "pair x y" always nonzero.                *)
(* ------------------------------------------------------------------------- *)

let pair x y = (x +/ y) */ (x +/ y) +/ x +/ Int 1;;

(* ------------------------------------------------------------------------- *)
(* Map names (i.e. strings) to numbers.                                      *)
(* ------------------------------------------------------------------------- *)

let charcode s n = Int(int_of_char(String.get s n));;

let number s =
  let n = String.length s in
  itlist (pair ** charcode s) (0--(n-1)) (Int n);;

(* ------------------------------------------------------------------------- *)
(* Goedel numbering of terms and formulas.                                   *)
(* ------------------------------------------------------------------------- *)

let rec gterm tm =
  match tm with
    Var x -> pair (Int 0) (number x)
  | Fn("0",[]) -> pair (Int 1) (Int 0)
  | Fn("S",[t]) -> pair (Int 2) (gterm t)
  | Fn("+",[s;t]) -> pair (Int 3) (pair (gterm s) (gterm t))
  | Fn("*",[s;t]) -> pair (Int 4) (pair (gterm s) (gterm t))
  | _ -> failwith "gterm: not in the language";;

let rec gform fm =
  match fm with
    False -> pair (Int 0) (Int 0)
  | True -> pair (Int 0) (Int 1)
  | Atom(R("=",[s;t])) -> pair (Int 1) (pair (gterm s) (gterm t))
  | Atom(R("<",[s;t])) -> pair (Int 2) (pair (gterm s) (gterm t))
  | Atom(R("<=",[s;t])) -> pair (Int 3) (pair (gterm s) (gterm t))
  | Atom(R(">",[s;t])) -> pair (Int 4) (pair (gterm s) (gterm t))
  | Atom(R(">=",[s;t])) -> pair (Int 5) (pair (gterm s) (gterm t))
  | Not(p) -> pair (Int 6) (gform p)
  | And(p,q) -> pair (Int 7) (pair (gform p) (gform q))
  | Or(p,q) -> pair (Int 8) (pair (gform p) (gform q))
  | Imp(p,q) -> pair (Int 9) (pair (gform p) (gform q))
  | Iff(p,q) -> pair (Int 10) (pair (gform p) (gform q))
  | Forall(x,p) -> pair (Int 11) (pair (number x) (gform p))
  | Exists(x,p) -> pair (Int 12) (pair (number x) (gform p))
  | _ -> failwith "gform: not in the language";;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
gform <<~(x = 0)>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Decider for delta-sentences.                                              *)
(* ------------------------------------------------------------------------- *)

let rec deval v tm =
  match tm with
    Var x -> apply v x
  | Fn("0",[]) -> Int 0
  | Fn("S",[t]) -> deval v t +/ Int 1
  | Fn("+",[s;t]) -> deval v s +/ deval v t
  | Fn("*",[s;t]) -> deval v s */ deval v t
  | _ -> failwith "deval: not a ground term of the language";;

let rec all_upto n p =
  if n </ Int 0 then true else p n & all_upto (n -/ Int 1) p;;

let some_upto n p = not(all_upto n (non p));;

let rel_atoms = ["=",(=); "<",(</); "<=",(<=/); ">",(>/); ">=",(>=/)];;

let rec delta v fm =
  match fm with
    False -> false
  | True -> true
  | Atom(R(a,[s;t])) -> (assoc a rel_atoms) (deval v s) (deval v t)
  | Not(p) -> not(delta v p)
  | And(p,q) -> delta v p & delta v q
  | Or(p,q) -> delta v p or delta v q
  | Imp(p,q) -> not(delta v p) or delta v q
  | Iff(p,q) -> (delta v p = delta v q)
  | Forall(x,Imp(Atom(R("<=",[Var y; t])),p)) when x = y
      -> all_upto (deval v t) (fun n -> delta ((x |-> n) v) p)
  | Forall(x,Imp(Atom(R("<",[Var y; t])),p)) when x = y
      -> all_upto (deval v t -/ Int 1) (fun n -> delta ((x |-> n) v) p)
  | Exists(x,And(Atom(R("<=",[Var y; t])),p)) when x = y
      -> some_upto (deval v t) (fun n -> delta ((x |-> n) v) p)
  | Exists(x,And(Atom(R("<",[Var y; t])),p)) when x = y
      -> some_upto (deval v t -/ Int 1) (fun n -> delta ((x |-> n) v) p)
  | _ -> failwith "delta: not a delta sentence";;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
delta undefined
 <<exists p. p <= S(S(S(S(0)))) /\ ~(p = 0) /\ ~(p = S(0)) /\
             forall n. n <= p
                       ==> (exists x. x <= p /\ p = n * x)
                           ==> n = S(0) \/ n = p>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Verify NNF sigma sentence with all existentials relativized to <= m.      *)
(* ------------------------------------------------------------------------- *)

let rec sigma m v fm =
  match fm with
    False -> false
  | True -> true
  | Atom(R(a,[s;t])) -> (assoc a rel_atoms) (deval v s) (deval v t)
  | Not(Atom(R(a,[s;t])) as p) -> not(sigma m v p)
  | And(p,q) -> sigma m v p & sigma m v q
  | Or(p,q) -> sigma m v p or sigma m v q
  | Forall(x,Or(Not(Atom(R("<=",[Var y; t]))),p)) when x = y
      -> all_upto (deval v t) (fun n -> sigma m ((x |-> n) v) p)
  | Forall(x,Or(Not(Atom(R("<",[Var y; t]))),p)) when x = y
      -> all_upto (deval v t -/ Int 1) (fun n -> sigma m ((x |-> n) v) p)
  | Exists(x,p) -> some_upto m (fun n -> sigma m ((x |-> n) v) p)
  | _ -> failwith "sigma: not a sigma NNF sentence";;

(* ------------------------------------------------------------------------- *)
(* Find adequate bound for all existentials to make sentence true.           *)
(* ------------------------------------------------------------------------- *)

let find_bound fm = first (Int 0) (fun n -> sigma n undefined fm);;

(* ------------------------------------------------------------------------- *)
(* Robinson axioms.                                                          *)
(* ------------------------------------------------------------------------- *)

let robinson =
 <<(forall m n. S(m) = S(n) ==> m = n) /\
   (forall n. ~(n = 0) <=> exists m. n = S(m)) /\
   (forall n. 0 + n = n) /\
   (forall m n. S(m) + n = S(m + n)) /\
   (forall n. 0 * n = 0) /\
   (forall m n. S(m) * n = n + m * n) /\
   (forall m n. m <= n <=> exists d. m + d = n) /\
   (forall m n. m < n <=> S(m) <= n) /\
   (forall m n. m > n <=> n < m) /\
   (forall m n. m >= n <=> n <= m)>>;;

(* ------------------------------------------------------------------------- *)
(* Consequences for Sigma-completeness and other related stuff.              *)
(* ------------------------------------------------------------------------- *)

let robinson_consequences =
 <<(forall n. ~(S(n) = 0)) /\
   (forall n. ~(0 = S(n))) /\
   (forall m n. ~(m = n) ==> ~(S(m) = S(n))) /\
   (forall n. n <= 0 ==> n = 0) /\
   (forall n. n <= S(0) ==> n = S(0) \/ n <= 0) /\
   (forall n. (forall x. x <= S(n) ==> x = S(n) \/ x <= n)
              ==> forall x. x <= S(S(n))
                            ==> x = S(S(n)) \/ x <= S(n)) /\
   (forall n. n < 0 ==> false) /\
   (forall m n. m < S(n) ==> m <= n) /\
   (forall m n. (exists d. m + d = n) ==> m <= n) /\
   (forall m n. (exists d. n + d = m) ==> m >= n) /\
   (forall m n. (exists d. S(m) + d = n) ==> m < n) /\
   (forall m n. (exists d. S(n) + d = m) ==> m > n) /\
   (forall m n. (forall d. ~(d <= n) \/ ~(d = m)) ==> ~(m <= n)) /\
   (forall m n. (forall d. ~(d <= m) \/ ~(d = n)) ==> ~(m >= n)) /\
   (forall m n. (forall d. ~(d < n) \/ ~(d = m)) ==> ~(m < n)) /\
   (forall m n. (forall d. ~(d < m) \/ ~(d = n)) ==> ~(m > n)) /\
   (forall x. x <= 0 \/ 0 <= x) /\
   (forall n. (forall x. x <= n \/ n <= x)
              ==> (forall x. x <= S(n) \/ S(n) <= x))>>;;

(* ------------------------------------------------------------------------- *)
(* Prove that they are indeed consequences.                                  *)
(* ------------------------------------------------------------------------- *)

let robinson_thm =
  prove (Imp(robinson,robinson_consequences))
  [have "eq_refl: forall x. x = x" using [axiom_eqrefl (Var "x")];
   have "eq_trans: forall x y z. x = y ==> y = z ==> x = z"
      using [eq_trans (Var "x") (Var "y") (Var "z")];
   have "eq_sym: forall x y. x = y ==> y = x"
      using [eq_sym (Var "x") (Var "y")];
   have "suc_cong: forall a b. a = b ==> S(a) = S(b)"
      using [axiom_funcong "S" [Var "a"] [Var "b"]];
   have "add_cong: forall a b c d. a = b /\ c = d ==> a + c = b + d"
      using [axiom_funcong "+" [Var "a"; Var "c"] [Var "b"; Var "d"]];
   have "le_cong: forall a b c d. a = b /\ c = d ==> a <= c ==> b <= d"
      using [axiom_predcong "<=" [Var "a"; Var "c"] [Var "b"; Var "d"]];

   assume "suc_inj: forall m n. S(m) = S(n) ==> m = n
       and num_nz: forall n. ~(n = 0) <=> exists m. n = S(m)
       and add_0: forall n. 0 + n = n
       and add_suc: forall m n. S(m) + n = S(m + n)
       and mul_0: forall n. 0 * n = 0
       and mul_suc: forall m n. S(m) * n = n + m * n
       and le_def: forall m n. m <= n <=> exists d. m + d = n
       and lt_def: forall m n. m < n <=> S(m) <= n
       and gt_def: forall m n. m > n <=> n < m
       and ge_def: forall m n. m >= n <=> n <= m";

   thus "not_suc_0: forall n. ~(S(n) = 0)" by ["num_nz"; "eq_refl"];
   hence "not_0_suc: forall n. ~(0 = S(n))" by ["eq_sym"];
   have "num_cases: forall n. (n = 0) \/ exists m. n = S(m)"
         by ["num_nz"];
   have "suc_inj_eq: forall m n. S(m) = S(n) <=> m = n"
     by ["suc_inj"; "suc_cong"];
   hence "forall m n. ~(m = n) ==> ~(S(m) = S(n))" at once;
   have "add_eq_0: forall m n. m + n = 0 ==> m = 0 /\ n = 0" proof
    [fix "m"; fix "n";
     assume "A: m + n = 0";
     case_split "B: m = 0 \/ exists p. m = S(p)" by ["num_cases"];
       thus "m = 0" by ["B"];
       have "m + n = 0 + n" by ["B"; "add_cong"; "eq_refl"];
       hence thesis by ["A"; "add_0"; "eq_sym"; "eq_trans"];
     qed;
       so consider ("p","m = S(p)") at once;
       so have "m + n = S(p) + n" by ["add_cong"; "eq_refl"];
       so have "m + n = S(p + n)" by ["eq_trans"; "add_suc"];
       so have "S(p + n) = 0" by ["A"; "eq_sym"; "eq_trans"];
       hence thesis by ["not_suc_0"];
     qed];
   hence "le_0: forall n. n <= 0 ==> n = 0" by ["le_def"];
   so have "le_suc_0: forall n. ~(S(n) <= 0)" by ["not_suc_0"];
   have "le_mono: forall m n. S(m) <= S(n) ==> m <= n" proof
    [fix "m"; fix "n";
     assume "S(m) <= S(n)";
     so consider ("d","S(m) + d = S(n)") by ["le_def"];
     so have "S(m + d) = S(n)" by ["add_suc"; "eq_trans"; "eq_sym"];
     so have "m + d = n" by ["suc_inj"];
     hence thesis by ["le_def"];
     qed];
   have "0_le: forall x. 0 <= x" by ["le_def"; "add_0"];
   have "le_mono': forall m n. m <= n ==> S(m) <= S(n)" proof
    [fix "m"; fix "n"; assume "m <= n";
     so consider ("d","m + d = n") by ["le_def"];
     so have "S(m + d) = S(n)" by ["suc_cong"];
     so have "S(m) + d = S(n)" by ["add_suc"; "eq_trans"];
     hence thesis by ["le_def"];
     qed];
   thus "forall n. n <= S(0) ==> n = S(0) \/ n <= 0" proof
     [fix "n";
      assume "A: n <= S(0)";
      case_split "n = 0 \/ exists p. n = S(p)" by ["num_cases"];
        hence thesis by ["0_le"; "le_cong"; "eq_refl"; "eq_sym"];
        qed;
        so consider ("p","NP: n = S(p)") at once;
        so have "S(p) <= S(0)" by ["A"; "le_cong"; "eq_refl"; "eq_sym"];
        so have "p <= 0" by ["le_mono"];
        so have "p = 0" by ["le_0"];
        hence thesis by ["suc_cong"; "NP"; "eq_trans"];
        qed
     ];
   thus "forall n. (forall x. x <= S(n) ==> x = S(n) \/ x <= n)
                    ==> (forall x. x <= S(S(n))
                                   ==> x = S(S(n)) \/ x <= S(n))" proof
    [fix "n";
     assume "ind: forall x. x <= S(n) ==> x = S(n) \/ x <= n";
     fix "x";
     case_split "x = 0 \/ exists y. x = S(y)" by ["num_cases"];
       hence thesis by ["0_le"; "le_cong"; "eq_refl"; "eq_sym"];
       qed;
       so consider ("y","XY: x = S(y)") at once;
       assume "x <= S(S(n))";
       so have "S(y) <= S(S(n))" by
            ["XY"; "le_cong"; "eq_refl"; "eq_sym"];
       so have "y <= S(n)" by ["le_mono"];
       so case_split "y = S(n) \/ y <= n" by ["ind"];
         so have "S(y) = S(S(n))" by ["suc_cong"];
         hence thesis by ["XY"; "eq_trans"];
         qed;
         so have "S(y) <= S(n)" by ["le_mono'"];
         hence thesis by ["XY"; "le_cong"; "eq_refl"; "eq_sym"];
         qed];
   thus "lt_0: forall n. n < 0 ==> false" by ["lt_def"; "le_suc_0"];
   thus "lt_suc: forall m n. m < S(n) ==> m <= n"
         by ["lt_def"; "le_mono"];
   thus "forall m n. (exists d. m + d = n) ==> m <= n" by ["le_def"];
   hence "forall m n. (exists d. n + d = m) ==> m >= n" by ["ge_def"];
   thus "forall m n. (exists d. S(m) + d = n) ==> m < n"
     by ["lt_def"; "le_def"];
   hence "forall m n. (exists d. S(n) + d = m) ==> m > n" by ["gt_def"];
   thus "forall m n. (forall d. ~(d <= n) \/ ~d = m) ==> ~m <= n"
      by ["eq_refl"];
   hence "forall m n. (forall d. ~(d <= m) \/ ~d = n) ==> ~m >= n"
      by ["ge_def"];
   thus "forall m n. (forall d. ~(d < n) \/ ~d = m) ==> ~m < n"
         by ["eq_refl"];
   hence "forall m n. (forall d. ~(d < m) \/ ~d = n) ==> ~m > n"
         by ["gt_def"];
   thus "forall x. x <= 0 \/ 0 <= x" by ["0_le"];
   fix "n";
   assume "ind: forall x. x <= n \/ n <= x";
   fix "x";
   case_split "Z: x = 0 \/ exists y. x = S(y)" by ["num_cases"];
     hence thesis by ["0_le"; "le_cong"; "eq_refl"; "eq_sym"];
     qed;
     so consider ("y","XY: x = S(y)") at once;
     have "y <= n \/ n <= y" by ["ind"];
     so have "S(y) <= S(n) \/ S(n) <= S(y)" by ["le_mono'"];
     hence thesis by ["le_cong"; "eq_refl"; "eq_sym"; "XY"];
     qed];;

(* ------------------------------------------------------------------------- *)
(* Assign names to axioms and consequences.                                  *)
(* ------------------------------------------------------------------------- *)

let [suc_inj; num_cases;
     add_0; add_suc; mul_0; mul_suc;
     le_def; lt_def; gt_def; ge_def] =
    conjths robinson;;

let [suc_0_l; suc_0_r; suc_inj_false;
     le_0; le_1; le_suc; lt_0; lt_suc;
     le_expand; ge_expand; lt_expand; gt_expand;
     nle_expand; nge_expand; nlt_expand; ngt_expand;
     le_cases_0; le_cases_suc] =
  map (imp_trans robinson_thm) (conjths robinson_consequences);;

(* ------------------------------------------------------------------------- *)
(* Particularly useful "right handed" inference rules.                       *)
(* ------------------------------------------------------------------------- *)

let spec_right t th = imp_trans th (ispec t (consequent(concl th)));;

let right_mp ith th =
  imp_unduplicate(imp_trans th (imp_swap ith));;

let right_imp_trans th1 th2 =
  imp_unduplicate(imp_front 2 (imp_trans th1 (imp_swap th2)));;

(* ------------------------------------------------------------------------- *)
(* Evalute constant expressions (allow non-constant on RHS in last clause).  *)
(* ------------------------------------------------------------------------- *)

let trans_right th1 th2 =
  let s,t = dest_eq(consequent(concl th1))
  and t',u = dest_eq(consequent(concl th2)) in
  imp_trans_chain [th1; th2] (eq_trans s t u);;

let rec robop tm =
  match tm with
    Fn(op,[Fn("0",[]);t]) ->
        if op = "*" then spec_right t mul_0
        else trans_right (spec_right t add_0) (robeval t)
  | Fn(op,[Fn("S",[u]);t]) ->
        let th1 = if op = "+" then add_suc else mul_suc in
        let th2 = itlist spec_right [t;u] th1 in
        trans_right th2 (robeval (rhs(consequent(concl th2))))

and robeval tm =
  match tm with
    Fn("S",[t]) ->
        let th = robeval t in
        let t' = rhs(consequent(concl th)) in
        imp_trans th (axiom_funcong "S" [t] [t'])
  | Fn(op,[s;t]) ->
        let th1 = robeval s in
        let s' = rhs(consequent(concl th1)) in
        let th2 = robop (Fn(op,[s';t])) in
        let th3 = axiom_funcong op [s;t] [s';t] in
        let th4 = modusponens (imp_swap th3) (axiom_eqrefl t) in
        trans_right (imp_trans th1 th4) th2
  | _ -> add_assum robinson (axiom_eqrefl tm);;

(* ------------------------------------------------------------------------- *)
(* Prove |- Q ==> x <= n ==> x = n \/ ... \/ x = 0.                          *)
(* ------------------------------------------------------------------------- *)

let right_disjl =
  let pfn = lcfptaut <<(p ==> q) ==> r \/ p ==> r \/ q>> in
  fun r th -> let p,q = dest_imp(consequent(concl th)) in
              let fm = Imp(Imp(p,q),Imp(Or(r,p),Or(r,q))) in
              imp_trans th (pfn fm);;

let rec le_casestep n =
  if n =/ Int 0 then
    let th = spec_right (Var "x") le_0 in th,gen_right "x" th
  else if n =/ Int 1 then
    let [th0;th1] = map (spec_right (Var "x")) [le_0; le_1] in
    let th2 = right_disjl (mk_eq (Var "x") (numeral(Int 1))) th0 in
    right_imp_trans th1 th2,gen_right "x" th1
  else
    let th1,th2 = le_casestep (n -/ Int 1) in
    let th3 = right_mp (spec_right (numeral(n -/ Int 2)) le_suc) th2 in
    let th4 = right_disjl (mk_eq (Var "x") (numeral n)) th1 in
    right_imp_trans (spec_right (Var "x") th3) th4,th3;;

let le_cases n x =
  spec_right (Var x) (gen_right "x" (fst(le_casestep n)));;

(* ------------------------------------------------------------------------- *)
(* From |- Q ==> s = s' and |- Q ==> t = t' to |- Q ==> a(s,t) ==> a(s',t')  *)
(* From |- Q ==> s = s' and |- Q ==> t = t' to |- Q ==> a(s',t') ==> a(s,t)  *)
(* From |- Q ==> s = s' and |- Q ==> t = t' to |- Q ==> ~(s,t) ==> ~a(s',t') *)
(* ------------------------------------------------------------------------- *)

let sym_right th =
  let s,t = dest_eq(consequent(concl th)) in imp_trans th (eq_sym s t);;

let right_contrapos =
  let pfn = lcfptaut <<(p ==> q) ==> ~q ==> ~p>> in
  fun th ->
    let p,q = dest_imp(consequent(concl th)) in
    imp_trans th (pfn(Imp(Imp(p,q),Imp(Not q,Not p))));;

let cong_atom a th_s th_t =
  let s,s' = dest_eq(consequent(concl th_s))
  and t,t' = dest_eq(consequent(concl th_t)) in
  imp_trans_chain [th_s; th_t] (axiom_predcong a [s; t] [s'; t']);;

let cong_batom a th_s th_t =
  cong_atom a (sym_right th_s) (sym_right th_t);;

let cong_natom a th_s th_t =
  right_contrapos(cong_atom a th_s th_t);;

(* ------------------------------------------------------------------------- *)
(* Prove true Sigma-sentence from the Robinson axioms Q.                     *)
(* ------------------------------------------------------------------------- *)

let right_disj1 =
  let pfn = lcfptaut <<p ==> p \/ q>> in
  fun th q -> let p = consequent(concl th) in
              imp_trans th (pfn(Imp(p,Or(p,q))));;

let right_disj2 =
  let pfn = lcfptaut <<q ==> p \/ q>> in
  fun p th -> let q = consequent(concl th) in
              imp_trans th (pfn(Imp(q,Or(p,q))));;

let right_impor =
  let pfn = lcfptaut <<(p ==> q) ==> ~p \/ q>> in
  fun th -> let p,q = dest_imp(consequent(concl th)) in
            imp_trans th (pfn(Imp(Imp(p,q),Or(Not p,q))));;

let expths =
  ["<",(lt_expand,nlt_expand); "<=",(le_expand,nle_expand);
   ">",(gt_expand,ngt_expand); ">=",(ge_expand,nge_expand)];;

let rec sigma_prove m fm =
  match fm with
    Exists(x,p) ->
        let n = first (Int 0)
          (fun n -> sigma m undefined (formsubst (x := numeral n) p)) in
        let nn = numeral n in
        let th = sigma_prove m (formsubst (x := nn) p) in
        imp_trans th (right_exists x nn p)
  | And(p,q) ->
        let thp = sigma_prove m p and thq = sigma_prove m q in
        imp_trans_chain [thp; thq] (and_pair p q)
  | Or(p,q) ->
        if sigma m undefined p then right_disj1 (sigma_prove m p) q
        else right_disj2 p (sigma_prove m q)
  | Atom(R(a,[s;t])) ->
        let th1 = cong_batom a (robeval s) (robeval t) in
        let fm' = antecedent(consequent(concl th1)) in
        right_mp th1 (sigma_trueatom m fm')
  | Not(Atom(R(a,[s;t]))) ->
        let th1 = cong_natom a (robeval s) (robeval t) in
        let fm' = antecedent(consequent(concl th1)) in
        right_mp th1 (sigma_falseatom m fm')
  | Forall(x,Or(Not(Atom(R(a,[y;t]))),p)) when Var x = y & fvt t = [] ->
        let th1 = add_assum robinson (axiom_eqrefl y) in
        let th2 = cong_atom a th1 (robeval t) in
        let fm' = Imp(funpow 2 consequent (concl th2),p) in
        let th3 = sigma_universal m fm' in
        gen_right x (right_impor(right_imp_trans th2 th3))

and sigma_trueatom m (Atom(R(a,[s;t]))) =
  if a = "=" & s = t then add_assum robinson (axiom_eqrefl s) else
  let th = itlist spec_right [t;s] (fst(assoc a expths)) in
  right_mp th (sigma_prove m (antecedent(consequent(concl th))))

and sigma_falseatom m (Not(Atom(R(a,[s;t])))) =
  if a = "=" then
    match (s,t) with
      (Fn("S",[s']),Fn("0",[])) -> spec_right s' suc_0_l
    | (Fn("0",[]),Fn("S",[t'])) -> spec_right t' suc_0_r
    | (Fn("S",[s']),Fn("S",[t'])) ->
        right_mp (itlist spec_right [t';s'] suc_inj_false)
                 (sigma_falseatom m (Not(Atom(R(a,[s';t'])))))
  else
    let th = itlist spec_right [t;s] (snd(assoc a expths)) in
    right_mp th (sigma_prove m (antecedent(consequent(concl th))))

and sigma_universal m fm =
  match fm with
    Imp(Atom(R("<",[(Var x as y);Fn("0",[])])),p) ->
        imp_trans (spec_right y lt_0) (ex_falso p)
  | Imp(Atom(R("<",[(Var x as y);Fn("S",[t])])),p) ->
        let th1 = itlist spec_right [t;y] lt_suc in
        let th2 = sigma_universal m (Imp(Atom(R("<=",[y;t])),p)) in
        right_imp_trans th1 th2
  | Imp(Atom(R("<=",[(Var x as y);t])),p) ->
        let th1 = le_cases (deval undefined t) x in
        let eqs = disjuncts(consequent(consequent(concl th1))) in
        let ths = map (fun e -> sigma_equal m (Imp(e,p))) eqs in
        let th2 = end_itlist ante_disj (map imp_swap ths) in
        imp_unduplicate (imp_front 2 (imp_trans th1 th2))

and sigma_equal m (Imp(Atom(R("=",[(Var x as y);t])),p)) =
  let th1 = isubst y t p in
  let p' = snd(dest_iff(consequent(concl th1))) in
  let th2 = sigma_prove m p' in
  imp_trans th2 (imp_swap(imp_trans th1 (axiom_iffimp2 p p')));;

(* ------------------------------------------------------------------------- *)
(* Overall function.                                                         *)
(* ------------------------------------------------------------------------- *)

let sigma_rule fm =
  let th = iff_imp2(nnf_conv fm) in
  let fm' = antecedent(concl th) in
  let m = find_bound fm' in
  imp_trans (sigma_prove m fm') th;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
sigma_rule
 <<exists p. ~(p = 0) /\ ~(p = S(0)) /\
             forall n. n <= p
                       ==> (exists x. x <= p /\ p = n * x)
                           ==> n = S(0) \/ n = p>>;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Delta-decider.                                                            *)
(* ------------------------------------------------------------------------- *)

let find_bibound fms =
  first (Int 0) (fun n -> exists (sigma n undefined) fms);;

let delta_rule fm =
  let [th_p; th_n] = map (iff_imp2 ** nnf_conv) [fm; Not fm] in
  let [fm_p; fm_n] = map (antecedent ** concl) [th_p; th_n] in
  let m = find_bibound [fm_p; fm_n] in
  if sigma m undefined fm_p then imp_trans (sigma_prove m fm_p) th_p
  else imp_trans (sigma_prove m fm_n) th_n;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
delta_rule
 <<exists p. p <= S(0) /\ ~(p = 0) /\ ~(p = S(0)) /\
             forall n. n <= p ==> (exists x. x <= p /\ p = n * x)
                                  ==> n = S(0) \/ n = p>>;;
END_INTERACTIVE;;
