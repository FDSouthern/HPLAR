(* ========================================================================= *)
(* LTL decision procedure based on reduction to fair CTL model checking.     *)
(*                                                                           *)
(* Basically follows Clarke et al's "Another look at LTL model checking"     *)
(* paper, though it's presented in a somewhat different style.               *)
(*                                                                           *)
(* Copyright (c) 2003, John Harrison. (See "LICENSE.txt" for details.)       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Prime all propositional variables in a term to perform "next" op.         *)
(* ------------------------------------------------------------------------- *)

let next fm =
  let ifn p = p |-> Atom(P(pname p^"'")) in
  propsubst (itlist ifn (atoms fm) undefined) fm;;

(* ------------------------------------------------------------------------- *)
(* Transform the formula to fair CTL model checking.                         *)
(* ------------------------------------------------------------------------- *)

let rec ltl (fm,defs,fcs,n as quad) =
  match fm with
    Nott(p) -> let p',defs',fcs',n' = ltl(p,defs,fcs,n) in
               Not(p'),defs',fcs',n'
  | Andt(p,q) -> ltl2 (fun (p,q) -> And(p,q)) (p,q) quad
  | Ort(p,q) -> ltl2 (fun (p,q) -> Or(p,q)) (p,q) quad
  | Impt(p,q) -> ltl2 (fun (p,q) -> Imp(p,q)) (p,q) quad
  | Ifft(p,q) -> ltl2 (fun (p,q) -> Iff(p,q)) (p,q) quad
  | Next(p) -> ltl1 p (fun p v -> next p) (fun p v -> []) quad
  | Box(p) ->
      ltl1 p (fun p v -> And(p,next v)) (fun p v -> [Imp(p,v)]) quad
  | Diamond(p) ->
      ltl1 p (fun p v -> Or(p,next v)) (fun p v -> [Imp(v,p)]) quad
  | Falset -> False,defs,fcs,n
  | Truet -> True,defs,fcs,n
  | Propvart(p) -> Atom(P p),defs,fcs,n

and ltl1 p cons1 cons2 (fm,defs,fcs,n) =
  let p',defs',fcs',n' = ltl(p,defs,fcs,n) in
  let v,n'' = mkprop n' in
  v,(Iff(v,cons1 p' v)::defs'),(cons2 p' v @ fcs'),(n' +/ Int 1)

and ltl2 cons (p,q) (fm,defs,fcs,n) =
  let fm1,defs1,fcs1,n1 = ltl (p,defs,fcs,n) in
  let fm2,defs2,fcs2,n2 = ltl (q,defs1,fcs1,n1) in
  cons(fm1,fm2),defs2,fcs2,n2;;

(* ------------------------------------------------------------------------- *)
(* Iterator analogous to "overatoms" for propositional logic.                *)
(* ------------------------------------------------------------------------- *)

let rec itpropt f fm a =
  match fm with
    Propvart(x) -> f x a
  | Nott(p) | Next(p) | Box(p) | Diamond(p) -> itpropt f p a
  | Andt(p,q) | Ort(p,q) | Impt(p,q) | Ifft(p,q) ->
        itpropt f p (itpropt f q a)
  | _ -> a;;

(* ------------------------------------------------------------------------- *)
(* Get propositional variables in a temporal formula.                        *)
(* ------------------------------------------------------------------------- *)

let propvarst fm = setify(itpropt (fun h t -> h::t) fm []);;

(* ------------------------------------------------------------------------- *)
(* We also need to avoid primed variables.                                   *)
(* ------------------------------------------------------------------------- *)

let max_varindex' pfx =
  let mkf = max_varindex pfx in
  fun s n ->
    if s = "" then n else
    let n' = mkf s n and l = String.length s - 1 in
    if String.sub s l 1 <> "'" then n' else mkf (String.sub s 0 l) n';;

(* ------------------------------------------------------------------------- *)
(* Make a variable name "p_n".                                               *)
(* ------------------------------------------------------------------------- *)

let mkname n = "p_"^(string_of_num n);;

(* ------------------------------------------------------------------------- *)
(* Overall LTL decision procedure (we add box to make sure top is variable). *)
(* ------------------------------------------------------------------------- *)

let ltldecide fm =
  let n = Int 1 +/ itpropt (max_varindex' "p_") fm (Int 0) in
  let Atom(P p),defs,fcs,m = ltl(Box fm,[],[],n) in
  let vars = propvarst fm @ map mkname (n---(m-/Int 1)) in
  fair_model_check vars True (list_conj defs) (AG(Propvarc(p))) fcs;;

(* ------------------------------------------------------------------------- *)
(* Example.                                                                  *)
(* ------------------------------------------------------------------------- *)

START_INTERACTIVE;;
let fm = let p = Propvart "p" in Impt(Next(Box p),Diamond(p));;

ltldecide fm;;
END_INTERACTIVE;;

(* ------------------------------------------------------------------------- *)
(* Alternative version moving p into the starting states.                    *)
(* ------------------------------------------------------------------------- *)

let ltldecide' fm =
  let n = Int 1 +/ itpropt (max_varindex' "p_") fm (Int 0) in
  let p,defs,fcs,m = ltl(fm,[],[],n) in
  let vars = propvarst fm @ map mkname (n---(m-/Int 1)) in
  fair_model_check vars (Not p) (list_conj defs) (Notc(EG(Truec))) fcs;;

(* ------------------------------------------------------------------------- *)
(* A parser, just to make testing nicer.                                     *)
(* ------------------------------------------------------------------------- *)

let rec parse_tformula inp =
   parse_right_infix "<=>" (fun (p,q) -> Ifft(p,q))
     (parse_right_infix "==>" (fun (p,q) -> Impt(p,q))
         (parse_right_infix "\\/" (fun (p,q) -> Ort(p,q))
             (parse_right_infix "/\\" (fun (p,q) -> Andt(p,q))
                 parse_tunary))) inp

and parse_tunary inp =
  match inp with
    "~"::onp -> papply (fun e -> Nott(e)) (parse_tunary onp)
  | "("::")"::onp -> papply (fun e -> Next(e)) (parse_tunary onp)
  | "["::"]"::onp -> papply (fun e -> Box(e)) (parse_tunary onp)
  | "<>"::onp -> papply (fun e -> Diamond(e)) (parse_tunary onp)
  | _ -> parse_tatom inp

and parse_tatom inp =
  match inp with
    [] -> failwith "Expected an expression at end of input"
  | "false"::toks -> Falset,toks
  | "true"::toks -> Truet,toks
  | "("::toks -> parse_bracketed parse_tformula ")" toks
  | p::toks -> Propvart(p),toks;;

let parsel s =
  let toks,rest = parse_tformula(lex(explode s)) in
  if rest = [] then toks else failwith "Unparsed input";;

(* ------------------------------------------------------------------------- *)
(* Examples.                                                                 *)
(* ------------------------------------------------------------------------- *)

let default_parser = parsel;;

START_INTERACTIVE;;
ltldecide << <>[]p ==> []<>()<>[]p >>;;

ltldecide' << [](p ==> ()p) ==> [](p ==> []p) >>;;

ltldecide' << []<>p ==> <>[]p >>;;

(* ------------------------------------------------------------------------- *)
(* Compare performances (and check results!) on test cases.                  *)
(* ------------------------------------------------------------------------- *)

let test fm =
  let a = time ltldecide fm in
  let a' = time ltldecide' fm in
  if a = a' then a else failwith("*** Disparity");;

test << (()[]p ==> <>p) >>;;

test << [] (()([]p) ==> <>p) >>;;

test << <>p ==> ()<>p >>;;

test << ()<>p ==> <>p >>;;

test << <>[]p ==> <>[]p >>;;

test << <>[]p ==> []<>p >>;;

test << ()(p /\ q) <=> () p /\ () q >>;;

test << [](p /\ q) <=> [] p /\ [] q >>;;

test << <>(p /\ q) <=> <> p /\ <> q >>;;

test << <>(p /\ q) ==> <> p /\ <> q >>;;

test << [](p ==> ()p) ==> [](p ==> []p) >>;;

test << [](p ==> ()p) ==> p ==> []p >>;;

test << [](p ==> ()p) ==> []p >>;;

test << [](p ==> ()q) /\ [](q ==> ()p) ==> []<>p >>;;

test << [](p ==> ()q) /\ [](q ==> ()p) ==> <>p ==> []<>p >>;;

test << <>(<>p) <=> <>p >>;;

test << [][]p <=> []p >>;;

test << ()[]p <=> []()p >>;;

test << []p ==> <>p >>;;

test << []p ==> ()p >>;;

test << ()p ==> <>p >>;;

test << [](p ==> ()p) ==> ()p ==> p ==> [] p >>;;

test << ~[]p <=> <>(~p) >>;;

test << []p ==> p >>;;

test << [](p ==> []p) ==> (p <=> []p) >>;;

test << []([]p ==> []q) <=> []([]p ==> q) >>;;

test << <>[]p ==> ()()()()<>[]p >>;;

test << <>[]p ==> ()()()()()()()()()<>[]p >>;;

test << <>[]<>p ==> []<>p >>;;

test << <>[]<>p ==> []<>[]<>p >>;;

test << ()[]p ==> []p >>;;

END_INTERACTIVE;;
