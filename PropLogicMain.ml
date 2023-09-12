(* ========================================================================= *)
(*               Propositional logic implemented in HOL Light                *)
(* ========================================================================= *)

parse_as_prefix "Not";;
parse_as_infix("&&",(16,"right"));;    (* Conjunction *)
parse_as_infix("||",(15,"right"));;    (* Disjunction *)
parse_as_infix("-->",(14,"right"));;   (* Implication *)
parse_as_infix("<->",(13,"right"));;   (* Bi-implication *)

let fm_INDUCT,fm_RECURSION = define_type
  "fm = False
        | True
        | Atom string
        | Not fm
        | && fm fm      
        | || fm fm
        | --> fm fm
        | <-> fm fm";;

(*                           Theorem 2.1, p.34                               *)
(*       "For any propositional formula p, the set atoms(p) is finite"       *)

let ATOMSOF_RULES, ATOMSOF_INDUCT, ATOMSOF_CASES = new_inductive_set
  `(!s. s IN ATOMSOF (Atom s)) /\
   (!s p. s IN ATOMSOF p ==> s IN ATOMSOF (Not p)) /\
   (!s p q. s IN ATOMSOF p ==> s IN ATOMSOF (p && q)) /\ 
   (!s p q. s IN ATOMSOF p ==> s IN ATOMSOF (q && p)) /\
   (!s p q. s IN ATOMSOF p ==> s IN ATOMSOF (p || q)) /\ 
   (!s p q. s IN ATOMSOF p ==> s IN ATOMSOF (q || p)) /\ 
   (!s p q. s IN ATOMSOF p ==> s IN ATOMSOF (p --> q)) /\
   (!s p q. s IN ATOMSOF p ==> s IN ATOMSOF (q --> p)) /\
   (!s p q. s IN ATOMSOF p ==> s IN ATOMSOF (p <-> q)) /\
   (!s p q. s IN ATOMSOF p ==> s IN ATOMSOF (q <-> p))`;;

g `(!s. ~ (s IN ATOMSOF False)) /\
   (!s. ~ (s IN ATOMSOF True)) /\
   (!s t. s IN ATOMSOF (Atom t) <=> s = t) /\
   (!s p. s IN ATOMSOF (Not p) <=> s IN ATOMSOF p) /\
   (!s p q. s IN ATOMSOF (p && q) <=> s IN ATOMSOF p \/ s IN ATOMSOF q) /\
   (!s p q. s IN ATOMSOF (p || q) <=> s IN ATOMSOF p \/ s IN ATOMSOF q) /\
   (!s p q. s IN ATOMSOF (p --> q) <=> s IN ATOMSOF p \/ s IN ATOMSOF q) /\
   (!s p q. s IN ATOMSOF (p <-> q) <=> s IN ATOMSOF p \/ s IN ATOMSOF q)`;;

e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC 
   THEN GEN_REWRITE_TAC (fun c -> LAND_CONV c ORELSEC RAND_CONV c ORELSEC c)
                   [ATOMSOF_CASES] THEN
   REWRITE_TAC[distinctness "fm"; injectivity "fm"] THEN MESON_TAC[]);;
let ATOMSOF_INVERSION = top_thm();;

g `ATOMSOF True = {} /\
   ATOMSOF False = {} /\
   (!s. ATOMSOF (Atom s) = {s}) /\
   (!p. ATOMSOF (Not p) = ATOMSOF p) /\
   (!p q. ATOMSOF (p && q) = ATOMSOF p UNION ATOMSOF q) /\ 
   (!p q. ATOMSOF (p || q) = ATOMSOF p UNION ATOMSOF q) /\
   (!p q. ATOMSOF (p --> q) = ATOMSOF p UNION ATOMSOF q) /\
   (!p q. ATOMSOF (p <-> q) = ATOMSOF p UNION ATOMSOF q)`;;
e (SET_TAC[ATOMSOF_INVERSION]);;
let ATOMSOF_CLAUSES = top_thm();;

g `!p. FINITE (ATOMSOF p)`;;
e (MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[ATOMSOF_CLAUSES; FINITE_RULES]);;
e (CONJ_TAC);;
 e (MESON_TAC[FINITE_RULES]);;
e (REWRITE_TAC[FINITE_UNION]);;
let fm_FINITE = top_thm();;

(* ========================================================================= *)
(*                               Semantics                                   *)
(* ========================================================================= *)

let EVAL = define
  `(EVAL (v:string->bool) False <=> F) /\
   (EVAL v True <=> T) /\
   (!a. EVAL v (Atom a) <=> v a) /\
   (!p. EVAL v (Not p) <=> ~ EVAL v p) /\
   (!p q. EVAL v (p && q) <=> EVAL v p /\ EVAL v q) /\
   (!p q. EVAL v (p || q) <=> EVAL v p \/ EVAL v q) /\
   (!p q. EVAL v (p --> q) <=> EVAL v p ==> EVAL v q) /\
   (!p q. EVAL v (p <-> q) <=> EVAL v p = EVAL v q)`;;

(* Example of EVALuation theorem *)
g `EVAL v (p || Not p)`;;   
e (REWRITE_TAC[EVAL]);;
e (MESON_TAC[]);;
top_thm();;

g `EVAL v (Not (p && q)) = EVAL v (Not p || Not q)`;;
e (REWRITE_TAC[EVAL] THEN MESON_TAC[]);;
top_thm();;

(* Relation of EQUIValence *)

let EQUIV = define
`EQUIV p q <=> (!v. EVAL v p <=> EVAL v q)`;;

(*                           Theorem 2.2, p.34                               *)
(*                   "For any propositional formula p,                       *)
(*          if two valutations v and w agree on the set atoms(p)             *)
(*      then the EVALuation on p of v equals the EVALuation on p of w"       *)

g `!p v w. (!x. x IN ATOMSOF p ==> v x = w x) /\ EVAL v p 
            ==> EVAL w p`;;
e (MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[EVAL;ATOMSOF_INVERSION]);;
e (SIMP_TAC[]);;
e (MESON_TAC[]);;
let EVAL_EQ_AUX = top_thm();;

g `!p v w. (!x. x IN ATOMSOF p ==> v x = w x) 
            ==> EVAL v p = EVAL w p`;;
e (MESON_TAC[EVAL_EQ_AUX]);;
let EVAL_EQ = top_thm();;

(*                         Theorem 2.7, 2.8, p.49                            *)

let DUAL = define
  `(DUAL False = True) /\
   (DUAL True = False) /\
   (!a. DUAL (Atom a) = Not Atom a) /\
   (!p. DUAL (Not p) = Not DUAL p) /\
   (!p q. DUAL (p && q) = DUAL p || DUAL q) /\
   (!p q. DUAL (p || q) = DUAL p && DUAL q) /\
   (!p q. DUAL (p --> q) = Not DUAL p && DUAL q) /\
   (!p q. DUAL (p <-> q) = 
          DUAL p && Not DUAL q || Not DUAL p && DUAL q)`;;

g `EVAL v (DUAL (DUAL False || True)) = EVAL v False`;;  
e (REWRITE_TAC[DUAL; EVAL]);;    (* An example of APPLIED DUAL *)
top_thm();;

g `EQUIV (DUAL (DUAL False || True)) False`;;  
e (REWRITE_TAC[DUAL; EQUIV; EVAL]);;   
top_thm();;

(* Theorem 2.7    The EVALuation of p is always the opposite of its DUAL       *)

g `!v p. EVAL v (DUAL p) = ~EVAL v p`;; 
e (GEN_TAC THEN MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[DUAL; EVAL] THEN MESON_TAC[]);;
let EVAL_DUAL = top_thm();;

(* Theorem 2.8 "If p and q are logically EQUIValent, so are DUAL p and DUAL q" *)

g `!p q. EQUIV p q ==> EQUIV (DUAL p) (DUAL q)`;; 
e (REWRITE_TAC[EQUIV; EVAL_DUAL] THEN MESON_TAC[]);;
let COR_EVAL_DUAL = top_thm();;

(*    The EVALuation of p is the same as the EVALuation of DUAL DUAL p      *)

g `!v p. EVAL v (DUAL (DUAL p)) = EVAL v p`;; 
e (REWRITE_TAC[EVAL; EVAL_DUAL]);;
top_thm();;

g `!p. EQUIV (DUAL (DUAL p)) p`;; 
e (REWRITE_TAC[EQUIV; EVAL_DUAL]);;
let EVAL_DUAL_DUAL = top_thm();;

(* ========================================================================= *)

let TAUT = new_definition                       (* TAUTology for EVALuations *)
`TAUT p <=> (!v. EVAL v p)`;;

let CONTRAD = new_definition                (* CONTRADiction for EVALuations *)       
`CONTRAD p <=> (!v. ~ EVAL v p)`;;

g `!p. CONTRAD (p && Not p)`;;                   (* Example of CONTRADiction *)
e (REWRITE_TAC[CONTRAD; TAUT; EVAL] THEN MESON_TAC[]);;
top_thm();;

g `!p. CONTRAD p <=> TAUT (Not p)`;;
e (GEN_TAC THEN REWRITE_TAC[CONTRAD; TAUT; EVAL]);;
let INTERDEF_CONTRAD_TAUT = top_thm();;

(* Two ways of defining SATISfiability, explicitly and from CONTRADiction *)

let SATIS = new_definition                
`SATIS p <=> (?v. EVAL v p)`;;
               
g `!p. SATIS p <=> ~(CONTRAD p)`;;             
e (REWRITE_TAC[SATIS; CONTRAD; TAUT; EVAL]);;
e (MESON_TAC[]);;
let ALT_DEF_SATIS = top_thm();;

g `!p. TAUT p ==> SATIS p`;;             (* Every TAUTology is SATISfiable *)
e (REWRITE_TAC[TAUT; SATIS; EVAL]);;
e (MESON_TAC[]);;
let TAUT_IMP_SATIS = top_thm();;

g `!p. SATIS (p --> p --> p)`;;    (* Example of a trivial SATISfiable formula *)
e (REWRITE_TAC[SATIS; CONTRAD; TAUT; EVAL]);;
top_thm();;

g `?p q r. SATIS (Not (p --> q && r))`;; (* Example of a SATISfiable formula *)
e (REWRITE_TAC[SATIS; EVAL]);;           
e (EXISTS_TAC `True`);;
e (EXISTS_TAC `True`);;
e (EXISTS_TAC `False`);;
e (SIMP_TAC[EVAL]);;
top_thm();;

(*             If not p is SATISfiable, then p is not a TAUTology            *)

g `!p. SATIS (Not p) ==> ~ TAUT p`;;
e (REWRITE_TAC[SATIS; TAUT; EVAL]);;
e (MESON_TAC[]);;
top_thm();;

(*        Theorem 2.8 "If p is a TAUTology then so is Not (DUAL p)"          *)

g `!p. TAUT p ==> TAUT (Not (DUAL p))`;; 
e (GEN_TAC);;
e (REWRITE_TAC[TAUT; DUAL; EVAL; EVAL_DUAL]);;
let NOT_DUAL_TAUT = top_thm();;

(* Proof of some important TAUTologies, p. 44-45 *)

let NOT_TRUE = prove
(`TAUT (Not True <-> False)`, REWRITE_TAC[TAUT; EVAL]);;

let NOT_FALSE = prove
(`TAUT (Not False)`, REWRITE_TAC[TAUT; EVAL]);;

let DOUBLE_NEG = prove
(`TAUT (Not Not p <-> p)`, REWRITE_TAC[TAUT; EVAL]);;

let CONJ_FALSE = prove
(`TAUT (p && False <-> False)`, REWRITE_TAC[TAUT; EVAL]);;

let CONJ_TRUE = prove
(`TAUT (p && True <-> p)`, REWRITE_TAC[TAUT; EVAL]);;

let CONJ_FORMULA = prove
(`TAUT (p && p <-> p)`, REWRITE_TAC[TAUT; EVAL]);;

let CONT_LAW = prove
(`TAUT (p && Not p <-> False)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let COMM_CONJ = prove
(`TAUT (p && q <-> q && p)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let ASS_CONJ = prove
(`TAUT (p && (q && r) <-> (p && q) && r)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let DISJ_FALSE = prove
(`TAUT (p || False <-> p)`, REWRITE_TAC[TAUT; EVAL]);;

let DISJ_TRUE = prove
(`TAUT (p || True)`, REWRITE_TAC[TAUT; EVAL]);;

let DISJ_FORMULA = prove
(`TAUT (p || p <-> p)`, REWRITE_TAC[TAUT; EVAL]);;

let EXC_MID = prove
(`TAUT (p || Not p)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let COMM_DISJ = prove
(`TAUT (p || q <-> q || p)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let ASS_DISJ = prove
(`TAUT (p || (q || r) <-> (p || q) || r)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let DISTR_CONJ = prove
(`TAUT (p && (q || r) <-> (p && q) || (p && r))`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let DISTR_DISJ = prove
(`TAUT (p || (q && r) <-> (p || q) && (p || r))`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let EXFALSO = prove
(`TAUT (False --> p)`, REWRITE_TAC[TAUT; EVAL]);;

let IMP_TRUE = prove
(`TAUT (p --> True)`, REWRITE_TAC[TAUT; EVAL]);;

let IMP_FALSE = prove
(`TAUT (p --> False <-> Not p)`, REWRITE_TAC[TAUT; EVAL]);;

let IDENTITY = prove
(`TAUT (p --> p)`, REWRITE_TAC[TAUT; EVAL]);;

let CONTRAPOSITION = prove
(`TAUT (p --> q <-> Not q --> Not p)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let IMP1 = prove
(`TAUT (p --> q <-> (p <-> p && q))`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let IFF2 = prove
(`TAUT (p --> q <-> (q <-> q || p))`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let COMM_IFF = prove
(`TAUT ((p <-> q) <-> (q <-> p))`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let DISTR_IFF = prove
(`TAUT (p <-> (q <-> r) <-> (p <-> q) <-> r)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let DEMORGAN1 = prove
(`TAUT (Not(p || q) <-> Not p && Not q)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let DEMORGAN2 = prove
(`TAUT (Not(p && q) <-> Not p || Not q)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let DEMORGAN3 = prove     
(`TAUT (False <-> p && Not p)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);; 

let DEMORGAN4 = prove
(`TAUT (Not (p && Not p))`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let DEMORGAN5 = prove
(`TAUT (p || q <-> Not (Not p && Not q))`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let DEMORGAN6 = prove
(`TAUT (False <-> p && Not p)`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;
 
let DEMORGAN7 = prove
(`TAUT (p --> q <-> Not (p && Not q))`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

let DEMORGAN8 = prove
(`TAUT ((p <-> q) <-> Not (p && Not q) && Not (Not p && q))`, 
REWRITE_TAC[TAUT; EVAL] THEN MESON_TAC[]);;

(*  For any given p and q, if q is a TAUTology then p --> q is a TAUTology  *)

g `!p q. TAUT q ==> TAUT (p --> q)`;;
e (REWRITE_TAC[TAUT; EVAL]);;
e (REPEAT GEN_TAC);;
e (STRIP_TAC);;
e (ASM_REWRITE_TAC[]);;
top_thm();;

(*       Given two formulas p and q, their conjunction is a TAUTology        *)
(*         if and only if both are TAUTologies                               *)

g `!p q. TAUT (p && q) <=> TAUT p /\ TAUT q`;;
e (REWRITE_TAC[TAUT; EVAL]);;
e (MESON_TAC[]);;
top_thm();;

(* ========================================================================= *)
(*                                 Adequacy                                  *)
(* ========================================================================= *)

(* Instead of proving a general property of adequacy, we choose an example
    of adequate logic and prove that it SATISfy the adequacy condition *)

(* INTfm checks if the formula contains only atoms or 
      Implications, Negations and the truth value True *)

let INTfm_RULES, INTfm_INDUCT, INTfm_CASES = new_inductive_definition
       `INTfm True /\
   (!a. INTfm (Atom a)) /\
   (!p. INTfm p ==> INTfm (Not p)) /\
   (!p q. INTfm p /\ INTfm q ==> INTfm (p --> q))`;;

g `INTfm True /\
 ~ INTfm False /\
   (!a. INTfm (Atom a)) /\
   (!p. INTfm (Not p) <=> INTfm p) /\
   (!p q. INTfm (p --> q) <=> INTfm p /\ INTfm q) /\
   (!p q. ~ INTfm (p && q)) /\
   (!p q. ~ INTfm (p || q)) /\
   (!p q. ~ INTfm (p <-> q))`;;

e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC 
   THEN GEN_REWRITE_TAC (fun c -> LAND_CONV c ORELSEC RAND_CONV c ORELSEC c)
                   [INTfm_CASES] THEN
   REWRITE_TAC[distinctness "fm"; injectivity "fm"] THEN MESON_TAC[]);;
let INTfm_CLAUSES = top_thm();;

let RECINTfm = define
  `(RECINTfm True = True) /\
   (RECINTfm False = Not True) /\
   (!a. RECINTfm (Atom a) = Atom a) /\
   (!p. RECINTfm (Not p) = Not (RECINTfm p)) /\
   (!p q. RECINTfm (p && q) = Not (RECINTfm p --> Not (RECINTfm q))) /\
   (!p q. RECINTfm (p || q) = Not (RECINTfm p) --> RECINTfm q) /\
   (!p q. RECINTfm (p --> q) = RECINTfm p --> RECINTfm q) /\
   (!p q. RECINTfm (p <-> q) = 
   Not ((RECINTfm p --> RECINTfm q) --> Not (RECINTfm q --> RECINTfm p)))`;;

g `!p v. EVAL v (RECINTfm p) = EVAL v p`;;
e (MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[INTfm_CLAUSES; RECINTfm; EVAL]);;
e (MESON_TAC[]);;
let RECINTfm_EVAL = top_thm();; 

g `!p. INTfm (RECINTfm p)`;; 
e (MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[RECINTfm; EVAL; INTfm_CLAUSES] THEN MESON_TAC[]);;
let INTfm_RECINTfm = top_thm();;

g `!p. ?q. EQUIV p q /\ INTfm q`;;
e (MESON_TAC[EQUIV; RECINTfm_EVAL; INTfm_RECINTfm]);; 
let INTfm_ADEQUATE = top_thm();;

(* ========================================================================= *)

g `!p. EQUIV (RECINTfm p) p`;;
e (REWRITE_TAC[EQUIV; RECINTfm_EVAL]);;
let RECINTfm_EQUIV = top_thm();; 

g `(!p. TAUT (p <-> RECINTfm p))`;;
e (REWRITE_TAC[TAUT; RECINTfm_EVAL; EVAL]);;
let RECINTfm_TAUT = top_thm();;

g `!p. ?q. q = RECINTfm p /\ INTfm q`;;
e (MATCH_MP_TAC fm_INDUCT);;
e (MESON_TAC[RECINTfm; EVAL; INTfm_CLAUSES; INTfm_RECINTfm]);;
let RECINTfm_APPLIED = top_thm();;

g `!p. ?q. TAUT (p <-> q) /\ INTfm q`;;
e (MESON_TAC[RECINTfm_TAUT;RECINTfm_APPLIED]);; 
let INTfm_ADEQUATE_t = top_thm();;

(* ========================================================================= *)
(*                               Substitution                                *)
(* ========================================================================= *)

(* Teorema 2.3 p.42 *)
(*Corollario 2.4: se p è una TAUT, x è un Atom e q una formula qualunque
allora la sostituazione di x con q in p è una TAUT*)

let ATOMSUB = define
  `(!sub. ATOMSUB sub False = False) /\
   (!sub. ATOMSUB sub True = True) /\
   (!sub a. ATOMSUB sub (Atom a) = sub a) /\
   (!sub p. ATOMSUB sub (Not p) = Not (ATOMSUB sub p)) /\
   (!sub p q. ATOMSUB sub (p && q) = ATOMSUB sub p && ATOMSUB sub q) /\
   (!sub p q. ATOMSUB sub (p || q) = ATOMSUB sub p || ATOMSUB sub q) /\
   (!sub p q. ATOMSUB sub (p --> q) = ATOMSUB sub p --> ATOMSUB sub q) /\
   (!sub p q. ATOMSUB sub (p <-> q) = ATOMSUB sub p <-> ATOMSUB sub q)`;;

(* sub is a function that associates every (char)list to a fm 
 It can be defined to swap only a specific atom and leave others unchanged   *)

(* Since substituting only x to q is a particular case of sub, 
we can implicitly prove the theorem by showing that a broader case is true   *)

(*Theorem 2.3 "For any atomic proposition x and arbitrary formula p and q, 
and any valutations v, we have:
EVAL v (psubst (x |=> q) p) = EVAL v p ((x |-> EVAL v q))"                   *)

g `!p v sub. EVAL v (ATOMSUB sub p) = EVAL (EVAL v o sub) p`;;
e (MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[EVAL; ATOMSUB; o_THM]);;
e (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let EVAL_SUB = top_thm();;

(*        Theorem 2.4          *)      

g `!p sub. TAUT p ==> TAUT (ATOMSUB sub p)`;;
e (REWRITE_TAC[TAUT; EVAL_SUB] THEN MESON_TAC[]);;
let TAUT_SUB = top_thm();;

(*        Theorem 2.5 and 2.6         *) 

g `!v r. (!a. EVAL v (sub1 a) = EVAL v (sub2 a))
      ==> EVAL v (ATOMSUB sub1 r) = EVAL v (ATOMSUB sub2 r)`;;
e (GEN_TAC);;
e (MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[ATOMSUB; EVAL]);;
e (SIMP_TAC[]);;
let EVAL_ATOMSUB_EQ = top_thm();;

g `!p q. (!v. EVAL v p = EVAL v q)
      ==> !v. EVAL v (ATOMSUB sub p) = EVAL v (ATOMSUB sub q)`;;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC[EVAL_SUB]);;
e (ASM_REWRITE_TAC[]);;
let THM_2_5_G = top_thm();;

g `!p q r. (!v. EVAL v p = EVAL v q) ==>
   !v. (EVAL v (ATOMSUB (\a. if a = x then p else Atom a) r) = 
   EVAL v (ATOMSUB (\a. if a = x then q else Atom a) r))`;;
e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC EVAL_ATOMSUB_EQ);;
e (GEN_TAC);;
e (REWRITE_TAC[]);;
e (COND_CASES_TAC);;
e (REWRITE_TAC[]);;
e (ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[]);;
let THM_2_5 = top_thm();;

g `!p q. (!v. EVAL v (p <-> q)) <=> (!v. EVAL v p = EVAL v q)`;;
e (REWRITE_TAC[EVAL]);;
let COR_2_6_AUX = top_thm();;

g `!p q r. TAUT (p <-> q) ==> 
   !v. EVAL v (ATOMSUB (\a. if a = x then p else Atom a) r) =
       EVAL v (ATOMSUB (\a. if a = x then q else Atom a) r)`;;
e (REWRITE_TAC[TAUT;COR_2_6_AUX;THM_2_5]);;
let COR_2_6 = top_thm();;

(* ========================================================================= *)
(*                          Negational normal form                           *)
(* ========================================================================= *)

(*           A Literal is either an atomic formula or its negation           *)
(*                   We use the abbreviation LTR for literal                 *)
let LTR_RULES, LTR_INDUCT, LTR_CASES = new_inductive_definition
   `(!a. LTR (Atom a)) /\ (!a. LTR (Not Atom a))`;;

g `~LTR False /\
   ~LTR True /\
   (!a. LTR (Atom a)) /\ 
   (!p. LTR (Not p) <=> ?a. p = Atom a) /\ 
   (!p q. ~LTR (p && q)) /\
   (!p q. ~LTR (p || q)) /\
   (!p q. ~LTR (p --> q)) /\
   (!p q. ~LTR (p <-> q))`;;
e (REWRITE_TAC[LTR_CASES; distinctness "fm"; injectivity "fm"]);;
e (MESON_TAC[]);;
let LTR_CLAUSES = top_thm();;

g `!P. (!p. LTR p ==> P p) <=> (!a. P (Atom a)) /\ (!a. P (Not Atom a))`;;
e (GEN_TAC THEN EQ_TAC);;
 e (REWRITE_TAC[LTR_CASES]);;
 e (MESON_TAC[]);;
e (INTRO_TAC "hp1 hp2");;
e (MATCH_MP_TAC LTR_INDUCT);;
e (ASM_REWRITE_TAC[]);;
let FORALL_LTR_THM = top_thm();;

(*      A formula is in NNF if it is false, true, if it is a literal or      *)
(*             if it is a conjunction or disjunction of literals             *)

let ISNNF_RULES, ISNNF_INDUCT, ISNNF_CASES = 
   new_inductive_definition
  `(ISNNF False) /\ (ISNNF True) /\
   (!p. LTR p ==> ISNNF p) /\
   (!p q. ISNNF p /\ ISNNF q ==> ISNNF (p && q)) /\
   (!p q. ISNNF p /\ ISNNF q ==> ISNNF (p || q))`;;

g `ISNNF False /\
   ISNNF True /\
   (!a. ISNNF (Atom a)) /\
   (!p. ISNNF (Not p) <=> ?a. p = Atom a) /\
   (!p q. ISNNF (p && q) <=> ISNNF p /\ ISNNF q) /\
   (!p q. ISNNF (p || q) <=> ISNNF p /\ ISNNF q) /\
   (!p q. ~ISNNF (p --> q)) /\
   (!p q. ~ISNNF (p <-> q))`;;
e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
   FIRST [GEN_REWRITE_TAC I [ISNNF_CASES];
          GEN_REWRITE_TAC LAND_CONV [ISNNF_CASES];
          GEN_REWRITE_TAC RAND_CONV [ISNNF_CASES]] THEN
   REWRITE_TAC[distinctness "fm"; injectivity "fm"; LTR_CLAUSES] THEN
   MESON_TAC[]);;
let ISNNF_CLAUSES = top_thm();;

(*NNFREC is a recursive way to produce a NNF formula starting from any formula*)

let NNFREC = define
  `(!b. NNFREC b False = if b then False else True) /\
   (!b. NNFREC b True = if b then True else False) /\
   (!b a. NNFREC b (Atom a) = if b then Atom a else Not Atom a) /\
   (!b p. NNFREC b (Not p) = NNFREC (~b) p) /\
   (!b p q. NNFREC b (p && q) =
            if b then NNFREC T p && NNFREC T q
            else NNFREC F p || NNFREC F q) /\
   (!b p q. NNFREC b (p || q) =
            if b then NNFREC T p || NNFREC T q
            else NNFREC F p && NNFREC F q) /\
   (!b p q. NNFREC b (p --> q) =
            if b then NNFREC F p || NNFREC T q
            else NNFREC T p && NNFREC F q) /\
   (!b p q. NNFREC b (p <-> q) =
            if b then NNFREC T p && NNFREC T q ||
                      NNFREC F p && NNFREC F q
            else NNFREC T p && NNFREC F q ||
                 NNFREC F p && NNFREC T q)`;;

(*    Any propositional formula can be expressed in negational normal form    *)

g `!p b. ISNNF (NNFREC b p)`;;
e (MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[NNFREC]);;
e (MESON_TAC[ISNNF_CLAUSES]);;
let NNFREC_ISNNF = top_thm();;

g `!v p b. EVAL v (NNFREC b p) = if b then EVAL v p else ~EVAL v p`;;
e (GEN_TAC THEN MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[FORALL_BOOL_THM]);;
e (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NNFREC; EVAL] THEN MESON_TAC[]);;
let NNFREC_EVAL = top_thm();;

g `(!p. TAUT (p <-> NNFREC T p)) /\
   (!p. TAUT (Not p <-> NNFREC F p))`;;
e (REWRITE_TAC[TAUT; EVAL; NNFREC_EVAL]);;
let NNFREC_TAUT = top_thm();;

g `!p. ?q. q = NNFREC T p /\ ISNNF q`;;
e (MATCH_MP_TAC fm_INDUCT);;
e (MESON_TAC[NNFREC; EVAL; ISNNF_CLAUSES; NNFREC_ISNNF]);;
let NNF_APPLIED = top_thm();;

g `!p. ?q. TAUT (p <-> q) /\ ISNNF q`;;
e (MESON_TAC[NNFREC_TAUT;NNF_APPLIED]);; 
let NNF_THM = top_thm();;

(* Negational normal form is not canonical *)

g `?p q. ISNNF p /\ ISNNF q /\ ~(p = q) /\ (!v. EVAL v p = EVAL v q)`;;
e (EXISTS_TAC `Atom a && (Atom b || Not Atom c)`);; 
e (EXISTS_TAC `(Atom a && Atom b) || (Atom a && Not Atom c)`);; 
e (REWRITE_TAC[ISNNF_CLAUSES; EVAL; distinctness "fm"]);;
e (MESON_TAC[]);;
let NOT_CANONICAL_ISNNF = top_thm();;

(* ========================================================================= *)
(*      A more faithful to Harrison's version proof of existence of NNF      *)
(* ========================================================================= *)

(* PSIMPLIFY, like the name suggests, simplifies a formula using
very basic rules on truth values and double negations 
it requires two functions to work as expected, PSIMPLIFY1 and PSIMPLIFY *)

let PSIMPLIFY1 = new_definition
  `PSIMPLIFY1 fm = match fm with
                 | Not False   -> True
                 | Not True    -> False
                 | Not Not p   -> p
                 | p && False  -> False
                 | False && p  -> False
                 | p && True   -> p
                 | True && p   -> p
                 | p || True   -> True
                 | True || p   -> True
                 | p || False  -> p
                 | False || p  -> p
                 | False --> p -> True
                 | p --> True  -> True
                 | True --> p  -> p
                 | p --> False -> Not p
                 | p <-> True  -> p
                 | True <-> p  -> p
                 | False <-> False -> True
                 | p <-> False -> Not p
                 | False <-> p -> Not p
                 | p           -> p`;;

g `PSIMPLIFY1 True = True /\
   PSIMPLIFY1 False = False /\
   (!a. PSIMPLIFY1 (Atom a) = Atom a) /\
   PSIMPLIFY1 (Not True) = False /\
   PSIMPLIFY1 (Not False) = True /\
   (!a. PSIMPLIFY1 (Not Atom a) = Not Atom a) /\
   (!p. PSIMPLIFY1 (Not Not p) = p) /\
   (!p q. PSIMPLIFY1 (Not (p && q)) = Not (p && q)) /\
   (!p q. PSIMPLIFY1 (Not (p || q)) = Not (p || q)) /\
   (!p q. PSIMPLIFY1 (Not (p --> q)) = Not (p --> q)) /\
   (!p q. PSIMPLIFY1 (Not (p <-> q)) = Not (p <-> q)) /\
   (!p q. PSIMPLIFY1 (p && q) =
          if p = False \/ q = False then False else
          if p = True then q else
          if q = True then p else
          p && q) /\
   (!p q. PSIMPLIFY1 (p || q) =
          if p = True \/ q = True then True else
          if q = False then p else
          if p = False then q else
          p || q) /\
   (!p q. PSIMPLIFY1 (p --> q) =
          if p = False \/ q = True then True else
          if p = True then q else
          if q = False then
             if p = True then False else Not p
          else
             p --> q) /\
   (!p q. PSIMPLIFY1 (p <-> q) =
          if p = True then q else
          if q = True then p else
          if p = False then
             if q = False then True else
             if q = True then False else Not q
          else
             if q = False then Not p else p <-> q)`;;
e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[PSIMPLIFY1] THEN
   REPEAT (CONV_TAC (ONCE_DEPTH_CONV MATCH_CONV) THEN 
   COND_CASES_TAC THEN REPEAT (
     (FIRST_X_ASSUM SUBST_VAR_TAC THEN
      RULE_ASSUM_TAC (REWRITE_RULE[distinctness "fm"]) THEN
      TRY (FIRST_ASSUM CONTR_TAC)) ORELSE
     CHANGED_TAC (FIRST_X_ASSUM STRIP_ASSUME_TAC)
   ) THEN REWRITE_TAC[]));;
let PSIMPLIFY1_CLAUSES = top_thm();;
                 
(* The EVALuation of a formula simplified is the same of the original formula *)

g `!v p. EVAL v (PSIMPLIFY1 p) = EVAL v p`;;
e (GEN_TAC THEN MATCH_MP_TAC fm_INDUCT THEN REWRITE_TAC[PSIMPLIFY1; EVAL]);;
e (REPEAT CONJ_TAC THEN INTRO_TAC "![p]" 
THEN STRUCT_CASES_TAC (SPEC `p:fm` (cases "fm")) THEN REWRITE_TAC[EVAL] 
                   THEN INTRO_TAC "![q]" 
THEN STRUCT_CASES_TAC (SPEC `q:fm` (cases "fm")) THEN REWRITE_TAC[EVAL]);;
let EVAL_PSIMPLIFY1 = top_thm();;

g `!p. EQUIV (PSIMPLIFY1 p) p`;;
e (REWRITE_TAC[EVAL_PSIMPLIFY1; EQUIV]);;
let EQUIV_PSIMPLIFY1 = top_thm();;

let PSIMPLIFY = define
  `PSIMPLIFY fm = match fm with
                 | Not p    -> PSIMPLIFY1 (Not (PSIMPLIFY p))
                 | p && q   -> PSIMPLIFY1 ((PSIMPLIFY p) && (PSIMPLIFY q))
                 | p || q   -> PSIMPLIFY1 ((PSIMPLIFY p) || (PSIMPLIFY q))
                 | p --> q  -> PSIMPLIFY1 ((PSIMPLIFY p) --> (PSIMPLIFY q))
                 | p <-> q  -> PSIMPLIFY1 ((PSIMPLIFY p) <-> (PSIMPLIFY q))
                 | p        -> p`;;

let PSIMPLIFY_CLAUSES = prove
 (`PSIMPLIFY True = True /\
   PSIMPLIFY False = False /\
   (!a. PSIMPLIFY (Atom a) = Atom a) /\
   (!p. PSIMPLIFY (Not p) = PSIMPLIFY1 (Not PSIMPLIFY p)) /\
   (!p q. PSIMPLIFY (p && q) = PSIMPLIFY1 (PSIMPLIFY p && PSIMPLIFY q)) /\
   (!p q. PSIMPLIFY (p || q) = PSIMPLIFY1 (PSIMPLIFY p || PSIMPLIFY q)) /\
   (!p q. PSIMPLIFY (p --> q) = PSIMPLIFY1 (PSIMPLIFY p --> PSIMPLIFY q)) /\
   (!p q. PSIMPLIFY (p <-> q) = PSIMPLIFY1 (PSIMPLIFY p <-> PSIMPLIFY q))`,
  REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [PSIMPLIFY] THEN REWRITE_TAC[]);;

(* PSIMPLIFY does not change the evaluation of a formula *)

g `!v p. EVAL v (PSIMPLIFY p) = EVAL v p`;;
e (GEN_TAC THEN MATCH_MP_TAC fm_INDUCT);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC[PSIMPLIFY; EVAL]);;
e (REWRITE_TAC[PSIMPLIFY; EVAL]);;
e (REWRITE_TAC[PSIMPLIFY; EVAL]);;
e (ONCE_REWRITE_TAC[PSIMPLIFY]);;
e (CONV_TAC (LAND_CONV (RAND_CONV MATCH_CONV)));;
e (ASM_REWRITE_TAC[EVAL_PSIMPLIFY1; EVAL]);;
e (ONCE_REWRITE_TAC[PSIMPLIFY]);;
e (SIMP_TAC[]);;
e (ASM_REWRITE_TAC[EVAL_PSIMPLIFY1; EVAL]);;
e (REPEAT STRIP_TAC);;
e (ONCE_REWRITE_TAC[PSIMPLIFY]);;
e (SIMP_TAC[]);;
e (ASM_REWRITE_TAC[EVAL_PSIMPLIFY1; EVAL]);;
e (REPEAT STRIP_TAC);;
e (ONCE_REWRITE_TAC[PSIMPLIFY]);;
e (SIMP_TAC[]);;
e (ASM_REWRITE_TAC[EVAL_PSIMPLIFY1; EVAL]);;
e (REPEAT STRIP_TAC);;
e (ONCE_REWRITE_TAC[PSIMPLIFY]);;
e (SIMP_TAC[]);;
e (ASM_REWRITE_TAC[EVAL_PSIMPLIFY1; EVAL]);;
let PSIMPLIFY_EVAL = top_thm();;

g `!p. EQUIV (PSIMPLIFY p) p`;;
e (REWRITE_TAC[PSIMPLIFY_EVAL; EQUIV]);;
let PSIMPLIFY_EQUIV = top_thm();;

(* RECNNF turns a formula NNF using transformations recursively *)

let RECNNF = define
  `RECNNF fm = match fm with
                 | (p && q)        -> RECNNF p && RECNNF q
                 | (p || q)        -> RECNNF p || RECNNF q
                 | (p --> q)       -> RECNNF (Not p) || RECNNF q
                 | (p <-> q)       -> 
RECNNF p && RECNNF q || RECNNF (Not p) && RECNNF (Not q)
                 | Not True        -> False
                 | Not False       -> True
                 | Not (Not p)     -> RECNNF p
                 | Not (p && q)    -> RECNNF (Not p) || RECNNF (Not q)
                 | Not (p || q)    -> RECNNF (Not p) && RECNNF (Not q)
                 | Not (p --> q)   -> RECNNF p && RECNNF (Not q)
                 | Not (p <-> q)   -> 
RECNNF (Not p) && (RECNNF q) || RECNNF p && RECNNF (Not q)
                 | p               -> p`;;

g `RECNNF True = True /\
   RECNNF (Not True) = False /\
   RECNNF False = False /\
   RECNNF (Not False) = True /\
  (!a. RECNNF (Atom a) = Atom a) /\
  (!a. RECNNF (Not Atom a) = Not Atom a) /\
(!p q. RECNNF (p && q) = RECNNF p && RECNNF q) /\
(!p q. RECNNF (p || q) = RECNNF p || RECNNF q) /\
(!p q. RECNNF (p --> q) = RECNNF (Not p) || RECNNF q) /\
(!p q. RECNNF (p <-> q) = 
RECNNF p && RECNNF q || RECNNF (Not p) && RECNNF (Not q)) /\
(!p q. RECNNF (Not (p && q)) = RECNNF (Not p) || RECNNF (Not q)) /\
(!p q. RECNNF (Not (p || q)) = RECNNF (Not p) && RECNNF (Not q)) /\
(!p q. RECNNF (Not (p --> q)) = RECNNF p && RECNNF (Not q)) /\
(!p q. RECNNF (Not (p <-> q)) = 
RECNNF (Not p) && (RECNNF q) || RECNNF p && RECNNF (Not q))`;;

e (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [RECNNF] 
   THEN REWRITE_TAC[]);;
let RECNNF_CLAUSES = top_thm();;

(* The EVALuation of formulas obtained with RECNNF  
is equal to the original formula *)

g `!v p. EVAL v (RECNNF p) = EVAL v p /\ 
         EVAL v (RECNNF (Not p)) = ~ EVAL v p`;;
e (GEN_TAC THEN MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[RECNNF_CLAUSES; EVAL]);;
e (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[EVAL] THEN
ONCE_REWRITE_TAC[RECNNF] THEN SIMP_TAC[] 
THEN ASM_REWRITE_TAC[EVAL] THEN MESON_TAC[EVAL]);;
let RECNNF_EVAL_AUX = top_thm();;

g `!v p. EVAL v (RECNNF p) = EVAL v p`;;
e (REWRITE_TAC[RECNNF_EVAL_AUX]);;
let RECNNF_EVAL = top_thm();;

(* NNF turns any formula in NNF and applies simplifications *)

let NNF = define 
`NNF fm = RECNNF (PSIMPLIFY fm)`;; 

(* NNF does not change the EVALuation of the formula *)

g `!p v. EVAL v (NNF p) = EVAL v p `;;
e (REWRITE_TAC[NNF]);;
e (REWRITE_TAC[PSIMPLIFY_EVAL; RECNNF_EVAL]);;
let EVAL_NNF = top_thm();;

(* For every formula p, there is a formula q 
that is its NNF translation and 
its EVALuation is the same as the original formula  *)

g `!p. ?q. q = NNF p /\ (!v. EVAL v p = EVAL v q)`;;
e (MESON_TAC[EVAL_NNF]);;
let NNF_THM_2 = top_thm();;

(* A formula obtained with RECNNF is in NNF *)

g `!p. ISNNF (RECNNF p) /\ ISNNF (RECNNF (Not p))`;;
e (MATCH_MP_TAC fm_INDUCT THEN REPEAT STRIP_TAC 
THEN ASM_REWRITE_TAC[RECNNF_CLAUSES; ISNNF_CLAUSES] 
THEN ONCE_REWRITE_TAC[RECNNF] THEN ASM_REWRITE_TAC[]);;
e (MESON_TAC[]);;
let RECNNF_ISNNF_AUX = top_thm();;

g `!p. ISNNF (RECNNF p)`;;
e (REWRITE_TAC[RECNNF_ISNNF_AUX]);;
let RECNNF_ISNNF = top_thm();;

g `!p. ISNNF (NNF p)`;;
e (REWRITE_TAC[NNF; RECNNF_ISNNF]);;
let NNF_ISNNF = top_thm();;
