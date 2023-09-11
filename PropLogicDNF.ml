(* ========================================================================= *)
(* ITBINOP                                                                   *)
(* ========================================================================= *)

(* ITBINOP is applied to a property P, a binary operator op and an argument x
   It is true when x is composed of reiterated "op" (e.g.: conjunctions)
   eventually zero (a single argument)
      and each of its arguments has the property P. *)

let ITBINOP_RULES,ITBINOP_INDUCT,ITBINOP_CASES = new_inductive_definition
  `(!x:A. P x ==> ITBINOP P op x) /\
   (!x y. P x /\ ITBINOP P op y ==> ITBINOP P op (op x y))`;;

let ITBINOP_INC,ITBINOP_OP =
  CONJ_PAIR (REWRITE_RULE[FORALL_AND_THM] ITBINOP_RULES);;

(*       We prove a CLAUSES theorem for ITBINOP applied to the operator &&    *)

g `(!P. ITBINOP P (&&) True <=> P True) /\
   (!P. ITBINOP P (&&) False <=> P False) /\
   (!P a. ITBINOP P (&&) (Atom a) <=> P (Atom a)) /\
   (!P f. ITBINOP P (&&) (Not f) <=> P (Not f)) /\
   (!P f g. ITBINOP P (&&) (f && g) <=> 
            P (f && g) \/ (P f /\ ITBINOP P (&&) g)) /\
   (!P f g. ITBINOP P (&&) (f || g) <=> P (f || g)) /\
   (!P f g. ITBINOP P (&&) (f --> g) <=> P (f --> g)) /\
   (!P f g. ITBINOP P (&&) (f <-> g) <=> P (f <-> g))`;;
e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV) [ITBINOP_CASES] THEN 
   REWRITE_TAC[distinctness "fm"; injectivity "fm"] THEN MESON_TAC[]);;
let ITBINOPCONJ_CLAUSES = top_thm();;

(*        We prove a CASES theorem for ITBINOP applied to the operator ||    *)

g `(!P. ITBINOP P (||) True <=> P True) /\
   (!P. ITBINOP P (||) False <=> P False) /\
   (!P a. ITBINOP P (||) (Atom a) <=> P (Atom a)) /\
   (!P f. ITBINOP P (||) (Not f) <=> P (Not f)) /\
   (!P f g. ITBINOP P (||) (f || g) <=> 
            P (f || g) \/ (P f /\ ITBINOP P (||) g)) /\
   (!P f g. ITBINOP P (||) (f && g) <=> P (f && g)) /\
   (!P f g. ITBINOP P (||) (f --> g) <=> P (f --> g)) /\
   (!P f g. ITBINOP P (||) (f <-> g) <=> P (f <-> g))`;;
e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC (LAND_CONV) [ITBINOP_CASES] THEN 
   REWRITE_TAC[distinctness "fm"; injectivity "fm"] THEN MESON_TAC[]);;
let ITBINOPDISJ_CLAUSES = top_thm();;

(* ========================================================================= *)
(* (Strict) Disjunctive Normal Form (DNF)                                    *)
(* Strict means: conjunctions and disjunctions must be associated to right.  *)
(* ========================================================================= *)

(* We define DNF using ITBINOP, that is, a formula is DNF if it is
      True or False (degenerate cases)
      It is a disjunction of conjunctions *)

let ISDNF_RULES,ISDNF_INDUCT,ISDNF_CASES = new_inductive_definition
  `ISDNF False /\
   ISDNF True /\
   (!p. ITBINOP (ITBINOP LTR (&&)) (||) p ==> ISDNF p)`;;

(* We prove a theorem for ISDNF *)

g `ISDNF False /\
   ISDNF True /\
   (!a. ISDNF (Atom a)) /\
   (!p. ISDNF (Not p) <=> ?a. p = (Atom a)) /\
   (!p q. ~ISDNF (p --> q)) /\
   (!p q. ~ISDNF (p <-> q)) /\
   (!p q. ISDNF (p && q) <=> LTR p /\ ITBINOP LTR (&&) q) /\
   (!p q. ISDNF (p || q) <=> 
          ITBINOP LTR (&&) p /\ ITBINOP (ITBINOP LTR (&&)) (||) q)`;;
e (REWRITE_TAC[ISDNF_CASES]);;
e (REWRITE_TAC[ITBINOPCONJ_CLAUSES; ITBINOPDISJ_CLAUSES]);;
e (REWRITE_TAC[LTR_CASES; distinctness "fm"; injectivity "fm"]);;
e (MESON_TAC[]);;
let ISDNF_CLAUSES = top_thm();;

(* ========================================================================= *)
(* Predicate for binary trees.                                               *)
(* ========================================================================= *)

let BINTREE_RULES,BINTREE_INDUCT,BINTREE_CASES = new_inductive_definition
  `(!x. P x ==> BINTREE P op x) /\
   (!x y. BINTREE P op x /\ BINTREE P op y ==> BINTREE P op (op x y))`;;

let BINTREE_INC,BINTREE_OP =
   CONJ_PAIR (REWRITE_RULE[FORALL_AND_THM] BINTREE_RULES);;

(*        We prove a theorem for BINTREE applied to the operator &&    *)

g `(!P. BINTREE P (&&) True <=> P True) /\
   (!P. BINTREE P (&&) False <=> P False) /\
   (!P a. BINTREE P (&&) (Atom a) <=> P (Atom a)) /\
   (!P f. BINTREE P (&&) (Not f) <=> P (Not f)) /\
   (!P f g. BINTREE P (&&) (f && g) <=> 
            BINTREE P (&&) f /\ BINTREE P (&&) g \/ P (f && g)) /\
   (!P f g. BINTREE P (&&) (f || g) <=> P (f || g)) /\
   (!P f g. BINTREE P (&&) (f --> g) <=> P (f --> g)) /\
   (!P f g. BINTREE P (&&) (f <-> g) <=> P (f <-> g))`;;
e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [BINTREE_CASES] THEN
   REWRITE_TAC[distinctness "fm"; injectivity "fm"] THEN MESON_TAC[]);;
let BINTREE_CONJ_CLAUSES = top_thm();;

(*        We prove a theorem for BINTREE applied to the operator ||    *)

g `(!P. BINTREE P (||) True <=> P True) /\
   (!P. BINTREE P (||) False <=> P False) /\
   (!P a. BINTREE P (||) (Atom a) <=> P (Atom a)) /\
   (!P f. BINTREE P (||) (Not f) <=> P (Not f)) /\
   (!P f g. BINTREE P (||) (f && g) <=> P (f && g)) /\
   (!P f g. BINTREE P (||) (f || g) <=> 
            BINTREE P (||) f /\ BINTREE P (||) g \/ P (f || g)) /\
   (!P f g. BINTREE P (||) (f --> g) <=> P (f --> g)) /\
   (!P f g. BINTREE P (||) (f <-> g) <=> P (f <-> g))`;;
e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [BINTREE_CASES] THEN
   REWRITE_TAC[distinctness "fm"; injectivity "fm"] THEN MESON_TAC[]);;
let BINTREE_DISJ_CLAUSES = top_thm();;

(* ========================================================================= *)
(* WDNF (Weak DNF)                                                           *)
(* ========================================================================= *)

(* WLTR (weak literal) is true when the argument is False, True or a literal *)

let WLTR_RULES,WLTR_INDUCT,WLTR_CASES = new_inductive_definition
  `WLTR False /\
   WLTR True /\
   (!p. LTR p ==> WLTR p)`;;

(* We define two theorems on WLTR that will help further proofs *)

g `WLTR False /\
   WLTR True /\
   (!p. WLTR (Not p) <=> ?a. p = Atom a) /\
   (!a. WLTR (Atom a)) /\
   (!p q. ~WLTR (p && q)) /\
   (!p q. ~WLTR (p || q)) /\
   (!p q. ~WLTR (p --> q)) /\
   (!p q. ~WLTR (p <-> q))`;;
e (REWRITE_TAC[WLTR_CASES; distinctness "fm"; LTR_CLAUSES]);;
let WLTR_CLAUSES = top_thm();;

g `!P. (!p. WLTR p ==> P p) <=> (!a. P (Atom a)) /\ (!a. P (Not Atom a))
/\ (P False) /\ (P True)`;;
e (GEN_TAC THEN EQ_TAC);;
e (REWRITE_TAC[WLTR_CASES; LTR_CASES]);;
e (MESON_TAC[]);;
e (INTRO_TAC "hp1 hp2 hp3 hp4");;
e (MATCH_MP_TAC WLTR_INDUCT);;
e (ASM_REWRITE_TAC[]);;
e (MATCH_MP_TAC LTR_INDUCT);;
e (ASM_REWRITE_TAC[]);;
let FORALL_WLTR_THM = top_thm();;

(* WDNF stands for Weak Disjunctive Normal Form *)

let WDNF = new_definition
  `WDNF p = BINTREE (BINTREE WLTR (&&)) (||) p`;;

g `WDNF False /\
   WDNF True /\
   (!a. WDNF (Atom a)) /\
   (!p. WDNF (Not p) <=> ?a. p = (Atom a)) /\
   (!p q. ~WDNF (p --> q)) /\
   (!p q. ~WDNF (p <-> q)) /\
   (!p q. WDNF (p && q) <=> (BINTREE WLTR (&&) p) /\ (BINTREE WLTR (&&) q)) /\
   (!p q. WDNF (p || q) <=> BINTREE (BINTREE WLTR (&&)) (||) p /\ 
                            BINTREE (BINTREE WLTR (&&)) (||) q)`;;
e (REWRITE_TAC[WDNF; BINTREE_CONJ_CLAUSES; BINTREE_DISJ_CLAUSES; LTR_CASES;
               WLTR_CASES; distinctness "fm"; injectivity "fm"] THEN
   MESON_TAC[]);;
let WDNF_CLAUSES = top_thm();; (* todo questo teorema non viene mai usato *)

(* ========================================================================= *)

g `!p. LTR p ==> BINTREE WLTR (&&) p`;;
e (MATCH_MP_TAC LTR_INDUCT);;
e (REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e (MESON_TAC[]);;
let LTR_BINTREE_THM = top_thm();;

g `!p. ITBINOP LTR (&&) p ==> BINTREE WLTR (&&) p`;;
e (MATCH_MP_TAC fm_INDUCT);;
 e (REWRITE_TAC[ITBINOPCONJ_CLAUSES; BINTREE_CONJ_CLAUSES]);;
 e (REWRITE_TAC[LTR_CLAUSES; WLTR_CLAUSES]);;
e (REWRITE_TAC[LTR_CASES]);;
e (REPEAT STRIP_TAC);;
e (ASM_REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e (UNDISCH_TAC `ITBINOP LTR (&&) a1`);;
e (ASM_REWRITE_TAC[]);;
e (ASM_REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e (MESON_TAC[]);;
e (UNDISCH_TAC `ITBINOP LTR (&&) a1`);;
e (ASM_REWRITE_TAC[]);;
let ITBINOP_TO_BINTREE = top_thm();;

g `!p. ISDNF p ==> WDNF p`;;
e (MATCH_MP_TAC ISDNF_INDUCT);;
e (REWRITE_TAC[WDNF_CLAUSES]);;
e (REWRITE_TAC[WDNF]);;
e (MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[BINTREE_CONJ_CLAUSES; BINTREE_DISJ_CLAUSES; WLTR_CLAUSES]);;
e CONJ_TAC;;
 e (REWRITE_TAC[ITBINOPCONJ_CLAUSES; ITBINOPDISJ_CLAUSES; LTR_CLAUSES]);;
e CONJ_TAC;;
 e (REWRITE_TAC[ITBINOPCONJ_CLAUSES; ITBINOPDISJ_CLAUSES; LTR_CLAUSES]);;
 e (REWRITE_TAC[BINTREE_CONJ_CLAUSES]);;
 e (REPEAT STRIP_TAC);;
 e (UNDISCH_TAC `LTR a0`);;
 e (REWRITE_TAC[LTR_BINTREE_THM]);;
 e (UNDISCH_TAC `ITBINOP LTR (&&) a1`);;
 e (REWRITE_TAC[ITBINOP_TO_BINTREE]);;
e CONJ_TAC;;
 e (REWRITE_TAC[BINTREE_CONJ_CLAUSES; BINTREE_DISJ_CLAUSES;
      ITBINOPCONJ_CLAUSES; ITBINOPDISJ_CLAUSES; LTR_CLAUSES]);;
 e (REPEAT STRIP_TAC);;
 e (UNDISCH_TAC `ITBINOP LTR (&&) a0`);;
 e (ONCE_REWRITE_TAC[BINTREE_CASES]);;
 e (STRIP_TAC);;
 e (DISJ1_TAC);;
 e (UNDISCH_TAC `ITBINOP LTR (&&) a0`);;
 e (REWRITE_TAC[ITBINOP_TO_BINTREE]);;
 e (UNDISCH_TAC `ITBINOP (ITBINOP LTR (&&)) (||) a1`);;
 e (ASM_REWRITE_TAC[]);;
e CONJ_TAC;;
 e (REWRITE_TAC[ITBINOPDISJ_CLAUSES; ITBINOPCONJ_CLAUSES; LTR_CLAUSES]);;
 e (REWRITE_TAC[ITBINOPDISJ_CLAUSES; ITBINOPCONJ_CLAUSES; LTR_CLAUSES]);;
let DNF_IS_WDNF = top_thm();;

(* ========================================================================= *)
(*   Reduction to DNF: Non-structural method                                 *)
(* ========================================================================= *)

(* ISDISJ checks if the argument is a disjunction *)

let ISDISJ_RULES,ISDISJ_INDUCT,ISDISJ_CASES = new_inductive_definition
   `!p q. ISDISJ (p || q)`;;
 
 g `~ISDISJ False /\
 ~ISDISJ True /\
 (!a. ~ISDISJ (Atom a)) /\
 (!p. ~ISDISJ (Not p)) /\
 (!p q. ~ISDISJ (p && q)) /\
 (!p q. ISDISJ (p || q)) /\
 (!p q. ~ISDISJ (p --> q)) /\
 (!p q. ~ISDISJ (p <-> q))`;;
 e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[ISDISJ_CASES] THEN
 REWRITE_TAC[distinctness "fm"; injectivity "fm"] THEN MESON_TAC[]);;
 let ISDISJ_CLAUSES = top_thm();;
 
 (* LHS is Left Hand Side;  RHS is Right Hand Side
    They return, respectively, the first and the second argument of a 
       given formula with a binary operator *)
 
 let LHS = define
   `(!p q. LHS (p && q) = p) /\
    (!p q. LHS (p || q) = p) /\
    (!p q. LHS (p --> q) = p) /\
    (!p q. LHS (p <-> q) = p)`;;
 
 let RHS = define
   `(!p q. RHS (p && q) = q) /\
    (!p q. RHS (p || q) = q) /\
    (!p q. RHS (p --> q) = q) /\
    (!p q. RHS (p <-> q) = q)`;;

(*                DISTRIB is a fuction that recursively applies 
            the DISTRIButive property of conjunction on disjunction and
            the DISTRIButive property of disjunction on conjunction          *)

let DISTRIB = define
  `DISTRIB fm = match fm with
               | p && (q || r)   -> DISTRIB (p && q) || DISTRIB (p && r) 
               | (p || q) && r   -> DISTRIB (p && r) || DISTRIB (q && r) 
               | p               -> p`;;

g `DISTRIB False = False /\
   DISTRIB True = True /\
   (!a. DISTRIB (Atom a) = Atom a) /\
   (!p. DISTRIB (Not p) = Not p) /\
   (!p q. DISTRIB (p || q) = p || q) /\
   (!p q. DISTRIB (p --> q) = p --> q) /\
   (!p q. DISTRIB (p <-> q) = p <-> q)`;;
e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
   GEN_REWRITE_TAC LAND_CONV [DISTRIB] THEN REWRITE_TAC[]);;
let DISTRIB_CLAUSES_TRIVIAL = top_thm();;

g `DISTRIB False = False /\
   DISTRIB True = True /\
   (!a. DISTRIB (Atom a) = Atom a) /\
   (!p. DISTRIB (Not p) = Not p) /\
   (!p q. DISTRIB (p && q) =
          if ISDISJ q then
            DISTRIB (p && LHS q) || DISTRIB (p && RHS q)
          else if ISDISJ p then
            DISTRIB (LHS p && q) || DISTRIB (RHS p && q)
          else
            p && q) /\
   (!p q. DISTRIB (p || q) = p || q) /\
   (!p q. DISTRIB (p --> q) = p --> q) /\
   (!p q. DISTRIB (p <-> q) = p <-> q)`;;
e (REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN 
   GEN_REWRITE_TAC LAND_CONV [DISTRIB] THEN REWRITE_TAC[]);;
e (STRUCT_CASES_TAC (SPEC `q:fm` (cases "fm")) 
   THEN REWRITE_TAC[ISDISJ_CLAUSES; LHS; RHS] THEN
   STRUCT_CASES_TAC (SPEC `p:fm` (cases "fm")) 
   THEN REWRITE_TAC[ISDISJ_CLAUSES; LHS; RHS]);;
let DISTRIB_CLAUSES = top_thm();;

(* First lemma on DISTRIB: if both p and q are conjunction of (weak) literals
      then DISTRIB (p && q) is a conjunction of (weak) literals *)

g `!q p. BINTREE WLTR (&&) q /\
         BINTREE WLTR (&&) p
         ==> BINTREE WLTR (&&) (DISTRIB (p && q))`;;
e (REWRITE_TAC[IMP_CONJ]);;
e (REWRITE_TAC[RIGHT_FORALL_IMP_THM]);;
e (MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e (ONCE_REWRITE_TAC[DISTRIB_CLAUSES]);;
e (REWRITE_TAC[ISDISJ_CLAUSES; DISTRIB_CLAUSES_TRIVIAL]);;
e CONJ_TAC;;
 e (INTRO_TAC "!p; p");;
 e COND_CASES_TAC;;
  e (POP_ASSUM (DESTRUCT_TAC "@r s. p" o REWRITE_RULE[ISDISJ_CASES]));;
  e (POP_ASSUM SUBST_VAR_TAC);; 
  e (HYP_TAC "p" (REWRITE_RULE[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]));;
  e (POP_ASSUM CONTR_TAC);;
 e (ASM_REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e CONJ_TAC;;
 e (INTRO_TAC "!p; p");;
 e COND_CASES_TAC;;
  e (POP_ASSUM (DESTRUCT_TAC "@r s. p" o REWRITE_RULE[ISDISJ_CASES]));;
  e (POP_ASSUM SUBST_VAR_TAC);; 
  e (HYP_TAC "p" (REWRITE_RULE[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]));;
  e (POP_ASSUM CONTR_TAC);;
 e (ASM_REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e CONJ_TAC;;
 e (INTRO_TAC "!a p; p");;
 e COND_CASES_TAC;;
  e (POP_ASSUM (DESTRUCT_TAC "@r s. p" o REWRITE_RULE[ISDISJ_CASES]));;
  e (POP_ASSUM SUBST_VAR_TAC);; 
  e (HYP_TAC "p" (REWRITE_RULE[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]));;
  e (POP_ASSUM CONTR_TAC);;
 e (ASM_REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e CONJ_TAC;;
 e (INTRO_TAC "![r]; r; (@a. a); !p; p");;
 e (REMOVE_THEN "a" SUBST_VAR_TAC);;
 e (HYP_TAC "r" (REWRITE_RULE[ISDISJ_CLAUSES; BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]));;
 e COND_CASES_TAC;;
  e (POP_ASSUM (DESTRUCT_TAC "@u v. p" o REWRITE_RULE[ISDISJ_CASES]));;
  e (POP_ASSUM SUBST_VAR_TAC);; 
  e (HYP_TAC "p" (REWRITE_RULE[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]));;
  e (POP_ASSUM CONTR_TAC);;
 e (ASM_REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES; injectivity "fm"]);;
 e (MESON_TAC[]);;
e (INTRO_TAC "![r] [s]; indr inds; r s; !p; p");;
e COND_CASES_TAC;;
 e (POP_ASSUM (DESTRUCT_TAC "@u v. p" o REWRITE_RULE[ISDISJ_CASES]));;
 e (POP_ASSUM SUBST_VAR_TAC);;
 e (HYP_TAC "p" (REWRITE_RULE[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]));;
 e (POP_ASSUM CONTR_TAC);;
e (ASM_REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
let LEMMA_1 = top_thm();;

(* Second lemma on DISTRIB: if q is in WDNF and 
   p is a conjunction of literals
      then DISTRIB (p && q) is in WDNF *)

g `!q p. BINTREE (BINTREE WLTR (&&)) (||) q /\
         BINTREE WLTR (&&) p
         ==> BINTREE (BINTREE WLTR (&&)) (||) (DISTRIB (p && q))`;;
e (REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM]);;
e (MATCH_MP_TAC BINTREE_INDUCT);;
e CONJ_TAC;;
 e (REPEAT STRIP_TAC);;
 e (MATCH_MP_TAC BINTREE_INC);;
 e (MATCH_MP_TAC LEMMA_1);;
 e (ASM_REWRITE_TAC[]);;
e (INTRO_TAC "![r] [s]; ind_r ind_s");;
e (ONCE_REWRITE_TAC[DISTRIB_CLAUSES]);;
e (REWRITE_TAC[ISDISJ_CLAUSES; LHS; RHS]);;
e (REWRITE_TAC[BINTREE_DISJ_CLAUSES; BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e (ASM_SIMP_TAC[]);;
let LEMMA_2 = top_thm();;

(* Tool to prove the third lemma *)

g `!p. WLTR p ==> ~ISDISJ p`;;
e (REWRITE_TAC[FORALL_WLTR_THM; ISDISJ_CLAUSES]);;
let WLTR_NOT_ISDISJ = top_thm();;

(* Third lemma on DISTRIB: if q is a (weak) literal and p is in WDNF
   Then DISTRIB (p && q) is in WDNF 
   We ended up not using this theorem, 
   but it may have its purpose in the future *)

(* g `!q p. WLTR q /\
         BINTREE (BINTREE WLTR (&&)) (||) p  
         ==> BINTREE (BINTREE WLTR (&&)) (||) (DISTRIB (p && q))`;;
e (REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM]);;
e (INTRO_TAC "!q; q");;
e (MATCH_MP_TAC BINTREE_INDUCT);;
e CONJ_TAC;;
 e (REPEAT STRIP_TAC THEN MATCH_MP_TAC LEMMA_2);;
 e (ASM_REWRITE_TAC[]);;
 e (ASM_SIMP_TAC[BINTREE_INC]);;
e (INTRO_TAC "![r] [s]; r s");;
e (ONCE_REWRITE_TAC[DISTRIB_CLAUSES]);;
e (ASM_SIMP_TAC[WLTR_NOT_ISDISJ]);;
e (REWRITE_TAC[ISDISJ_CLAUSES; LHS; RHS]);;
e (ASM_REWRITE_TAC[BINTREE_DISJ_CLAUSES]);;
let LEMMA_3 = top_thm();;
*)

(* If p is WDNF and q is WDNF then DISTRIB (p && q) is WDNF *)

g `!p q. BINTREE (BINTREE WLTR (&&)) (||) p /\
         BINTREE (BINTREE WLTR (&&)) (||) q
         ==> BINTREE (BINTREE WLTR (&&)) (||) (DISTRIB (p && q))`;;
e (REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM]);;
e (MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[BINTREE_DISJ_CLAUSES; BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e CONJ_TAC;;
 e (REPEAT STRIP_TAC THEN MATCH_MP_TAC LEMMA_2);;
 e (ASM_REWRITE_TAC[]);;
 e (REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e CONJ_TAC;;
 e (REPEAT STRIP_TAC THEN MATCH_MP_TAC LEMMA_2);;
 e (ASM_REWRITE_TAC[]);;
 e (REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e CONJ_TAC;;
 e (REPEAT STRIP_TAC THEN MATCH_MP_TAC LEMMA_2);;
 e (ASM_REWRITE_TAC[]);;
 e (REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e CONJ_TAC;;
 e (REWRITE_TAC[WLTR_CLAUSES]);;
 e (REPEAT STRIP_TAC THEN MATCH_MP_TAC LEMMA_2);;
 e (ASM_REWRITE_TAC[]);;
 e (FIRST_X_ASSUM SUBST_VAR_TAC);;
 e (REWRITE_TAC[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES] THEN MESON_TAC[]);;
e CONJ_TAC;;
 e (REWRITE_TAC[IMP_IMP; GSYM RIGHT_FORALL_IMP_THM]);;
 e (INTRO_TAC "![r] [s] q; ((ind_r ind_s) (r s)) q");;
 e (MATCH_MP_TAC LEMMA_2);;
 e (ASM_REWRITE_TAC[BINTREE_CONJ_CLAUSES]);;
e (INTRO_TAC "![r] [s]; ind_r ind_s; r s");;
e (REMOVE_THEN "ind_r" (IMP_RES_THEN (LABEL_TAC "ind_r")));;
e (REMOVE_THEN "ind_s" (IMP_RES_THEN (LABEL_TAC "ind_s")));;
e (MATCH_MP_TAC BINTREE_INDUCT);;
e CONJ_TAC;;
 e (INTRO_TAC "![q]; q");;
 e (ONCE_REWRITE_TAC[DISTRIB_CLAUSES]);;
 e COND_CASES_TAC;;
  e (POP_ASSUM (DESTRUCT_TAC "@a b. q" o REWRITE_RULE[ISDISJ_CASES]));;
  e (POP_ASSUM SUBST_VAR_TAC);;
  e (HYP_TAC "q" (REWRITE_RULE[BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]));;
  e (USE_THEN "q" CONTR_TAC);;
 e (REWRITE_TAC[ISDISJ_CLAUSES; LHS; RHS]);;
 e (REWRITE_TAC[BINTREE_DISJ_CLAUSES; BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
 e (CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[BINTREE_INC]);;
e (INTRO_TAC "![u] [v]; u v");;
e (ONCE_REWRITE_TAC[DISTRIB_CLAUSES]);;
e (REWRITE_TAC[ISDISJ_CLAUSES; LHS; RHS]);;
e (REWRITE_TAC[BINTREE_DISJ_CLAUSES; BINTREE_CONJ_CLAUSES; WLTR_CLAUSES]);;
e (ASM_REWRITE_TAC[]);;
let WDNF_DISTRIB_CONJ_LEMMA = top_thm();;

(* ========================================================================= *)
(*       The evaluation of a formula is unchanged after applying DISTRIB     *)

g `DISTRIB False = False /\
   DISTRIB True = True /\
(!a. DISTRIB (Atom a) = Atom a) /\
(!p. DISTRIB (Not p) = Not p) /\
(!p q. DISTRIB (p || q) =  p || q) /\
(!p q. DISTRIB (p --> q) = p --> q) /\
(!p q. DISTRIB (p <-> q) = p <-> q) /\
(!p q r. DISTRIB (p && (q || r)) = 
   DISTRIB (p && q) || DISTRIB (p && r)) /\

(!p q r. DISTRIB ((p || q) && r) =
           match r with
           | r1 || r2 -> DISTRIB ((p || q) && r1) ||
                         DISTRIB ((p || q) && r2)
           | fm -> DISTRIB (p && r) || DISTRIB (q && r)) /\
(!r. DISTRIB (False && r) =
           match r with
           | r1 || r2 -> DISTRIB (False && r1) ||
                         DISTRIB (False && r2)
           | fm -> False && r) /\
(!r. DISTRIB (True && r) =
           match r with
           | r1 || r2 -> DISTRIB (True && r1) ||
                         DISTRIB (True && r2)
           | fm -> True && r) /\
(!r a. DISTRIB (Atom a && r) =
           match r with
           | r1 || r2 -> DISTRIB (Atom a && r1) ||
                         DISTRIB (Atom a && r2)
           | fm -> Atom a && r) /\
(!r p. DISTRIB (Not p && r) =
           match r with
           | r1 || r2 -> DISTRIB (Not p && r1) ||
                         DISTRIB (Not p && r2)
           | fm -> Not p && r) /\
(!r p q. DISTRIB ((p && q) && r) =
           match r with
           | r1 || r2 -> DISTRIB ((p && q) && r1) ||
                         DISTRIB ((p && q) && r2)
           | fm -> (p && q) && r) /\
(!r p q. DISTRIB ((p --> q) && r) =
           match r with
           | r1 || r2 -> DISTRIB ((p --> q) && r1) ||
                         DISTRIB ((p --> q) && r2)
           | fm -> (p --> q) && r) /\
(!r p q. DISTRIB ((p <-> q) && r) =
           match r with
           | r1 || r2 -> DISTRIB ((p <-> q) && r1) ||
                         DISTRIB ((p <-> q) && r2)
           | fm -> (p <-> q) && r) /\

(!p q. DISTRIB ((p || q) && False) = 
   DISTRIB (p && False) || DISTRIB (q && False)) /\
(!p q. DISTRIB ((p || q) && True) = 
   DISTRIB (p && True) || DISTRIB (q && True)) /\
(!p q a. DISTRIB ((p || q) && Atom a) = 
   DISTRIB (p && Atom a) || DISTRIB (q && Atom a)) /\
(!p q r. DISTRIB ((p || q) && (Not r)) = 
   DISTRIB (p && Not r) || DISTRIB (q && Not r)) /\
(!p q r s. DISTRIB ((p || q) && (r --> s)) = 
   DISTRIB (p && (r --> s)) || DISTRIB (q && (r --> s))) /\
(!p q r s. DISTRIB ((p || q) && (r <-> s)) = 
   DISTRIB (p && (r <-> s)) || DISTRIB (q && (r <-> s))) /\
(!p q r s. DISTRIB ((p || q) && (r && s)) = 
   DISTRIB (p && (r && s)) || DISTRIB (q && (r && s))) /\

(!a b c d. DISTRIB ((a || b) && (c || d)) = 
   DISTRIB ((a || b) && c) || DISTRIB ((a || b) && d))`;;

e (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [DISTRIB] 
THEN REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DISTRIB] THEN REWRITE_TAC[]
THEN STRUCT_CASES_TAC (SPEC `r:fm` (cases "fm")) THEN REWRITE_TAC[]);;
let DISTRIB_CLAUSES_ALT = top_thm();; 

g `(!v. EVAL v (DISTRIB False) = EVAL v False) /\
(!v. EVAL v (DISTRIB True) = EVAL v True) /\
(!v a. EVAL v (DISTRIB (Atom a)) = EVAL v (Atom a)) /\
(!v p. EVAL v (DISTRIB (Not p)) = EVAL v (Not p)) /\
(!v p q. EVAL v (DISTRIB (p --> q)) = EVAL v (p --> q)) /\
(!v p q. EVAL v (DISTRIB (p <-> q)) = EVAL v (p <-> q)) /\
(!v p q. EVAL v (DISTRIB (p || q)) = EVAL v (p || q)) /\
(!v p. EVAL v (DISTRIB (p && False)) = EVAL v (p && False)) /\ 
(!v p. EVAL v (DISTRIB (p && True)) = EVAL v (p && True)) /\
(!v p a. EVAL v (DISTRIB (p && Atom a)) = EVAL v (p && Atom a)) /\
(!v p q. EVAL v (DISTRIB (p && Not q)) = EVAL v (p && Not q)) /\
(!v p q r. EVAL v (DISTRIB (p && (q && r))) = EVAL v (p && (q && r))) /\
(!v p q r. EVAL v (DISTRIB (p && (q --> r))) = EVAL v (p && (q --> r))) /\
(!v p q r. EVAL v (DISTRIB (p && (q <-> r))) = EVAL v (p && (q <-> r)))`;;

e (REPEAT CONJ_TAC THEN GEN_TAC THEN REWRITE_TAC[DISTRIB_CLAUSES_ALT; EVAL] 
THEN MATCH_MP_TAC fm_INDUCT THEN REWRITE_TAC[EVAL;DISTRIB_CLAUSES_ALT]
THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[EVAL] THEN MESON_TAC[]);;
let EVAL_DISTRIB_AUX = top_thm();;

g `!v p q. (EVAL v (DISTRIB p) = EVAL v p) /\
           (EVAL v (DISTRIB (q && p)) = EVAL v (q && p))`;;
e (GEN_TAC THEN MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[EVAL_DISTRIB_AUX; EVAL; DISTRIB_CLAUSES_ALT]);;
e (CONJ_TAC);;
e (REPEAT STRIP_TAC);;
e (ASM_REWRITE_TAC[]);;
e (MESON_TAC[]);;
let EVAL_DISTRIB_AUX2 = top_thm();;

g `!v p q. (EVAL v (DISTRIB p) = EVAL v p)`;;
e (REWRITE_TAC[EVAL_DISTRIB_AUX2]);;
let EVAL_DISTRIB = top_thm();;

(* Alternative version of EVAL_DISTRIB using the SIZE property *)
(*
let SIZE = define
  `SIZE True = 1 /\
   SIZE False = 1 /\
   (!a. SIZE (Atom a) = 1) /\
   (!p. SIZE (Not p) = 1 + SIZE p) /\
   (!p q. SIZE (p && q) = 1 + SIZE p + SIZE q) /\
   (!p q. SIZE (p || q) = 1 + SIZE p + SIZE q) /\
   (!p q. SIZE (p --> q) = 1 + SIZE p + SIZE q) /\
   (!p q. SIZE (p <-> q) = 1 + SIZE p + SIZE q)`;;

g `!P. (!p. (!q. SIZE q < SIZE p ==> P q) ==> P p) ==> (!p. P p)`;;
e (INTRO_TAC "!P; hp; !p");;
e (SUBGOAL_THEN `!n p. SIZE p = n ==> P p` (fun th -> MESON_TAC[th]));;
e (MATCH_MP_TAC num_WF);;
e (REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP]);;
e (INTRO_TAC "!n p; hpind p");;
e (REMOVE_THEN "hp" MATCH_MP_TAC);;
e (INTRO_TAC "!q; hp");;
e (FIRST_X_ASSUM MATCH_MP_TAC);;
e (ASM_MESON_TAC[]);;
let SIZE_INDUCT = top_thm();;

(*     The EVALuation of a formula does not change after applying DISTRIB    *)

g `!v p. EVAL v (DISTRIB p) = EVAL v p`;;
e (GEN_TAC THEN MATCH_MP_TAC SIZE_INDUCT);;
e (INTRO_TAC "!p; hpind");;
e (GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [DISTRIB]);;
e (CONV_TAC (ONCE_DEPTH_CONV MATCH_CONV));;
e COND_CASES_TAC;;
 e (POP_ASSUM STRIP_ASSUME_TAC);;
 e (POP_ASSUM SUBST_VAR_TAC);;
 e (REWRITE_TAC[EVAL]);;
 e (SUBGOAL_THEN `SIZE (p' && q) < SIZE (p' && (q || r)) /\
                  SIZE (p' && r) < SIZE (p' && (q || r))`
      (fun th -> ASM_SIMP_TAC[th; EVAL]));;
  e (REWRITE_TAC[SIZE] THEN ARITH_TAC);;
 e (MESON_TAC[]);;
e (CONV_TAC (ONCE_DEPTH_CONV MATCH_CONV));;
e COND_CASES_TAC;;
 e (POP_ASSUM STRIP_ASSUME_TAC);;
 e (POP_ASSUM SUBST_VAR_TAC);;
 e (REWRITE_TAC[EVAL]);;
 e (SUBGOAL_THEN `SIZE (p' && r) < SIZE ((p' || q) && r) /\
                  SIZE (q && r) < SIZE ((p' || q) && r)`
      (fun th -> ASM_SIMP_TAC[th; EVAL]));;
  e (REWRITE_TAC[SIZE] THEN ARITH_TAC);;
 e (MESON_TAC[]);;
e (REWRITE_TAC[]);;
let EVAL_DISTRIB = top_thm();;   
*)

(* ========================================================================= *)
(* RAWDNF searches a formula for instances where DISTRIBution can be applied *)

let RAWDNF = define
  `RAWDNF fm = match fm with
               | p && q          -> DISTRIB (RAWDNF p && RAWDNF q)
               | (p || q)        -> RAWDNF p || RAWDNF q 
               | p               -> p`;;

g `RAWDNF False = False /\
   RAWDNF True = True /\
   (!a. RAWDNF (Atom a) = Atom a) /\
   (!p. RAWDNF (Not p) = Not p) /\
   (!p q. RAWDNF (p --> q) = p --> q) /\
   (!p q. RAWDNF (p <-> q) = p <-> q) /\
   (!p q. RAWDNF (p && q) = DISTRIB (RAWDNF p && RAWDNF q)) /\
   (!p q. RAWDNF (p || q) = (RAWDNF p) || (RAWDNF q))`;;
e (REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [RAWDNF] THEN
   REWRITE_TAC[]);;
let RAWDNF_CLAUSES = top_thm();;

(* RAWDNF does not change the EVALuation of the transformed formula *)

g `!v p. EVAL v (RAWDNF p) = EVAL v p`;;
e (GEN_TAC THEN MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[RAWDNF_CLAUSES; EVAL; EVAL_DISTRIB]);;
e (REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;
let RAWDNF_EVAL = top_thm();;

g `!v p q. EVAL v (p <-> q) <=> (EVAL v p <=> EVAL v q)`;;
e (REWRITE_TAC[EVAL]);;
let EVAL_IFF = top_thm();;

g `!p. TAUT (p <-> RAWDNF p)`;; 
e (REWRITE_TAC[TAUT; EVAL_IFF]);;
e (MESON_TAC[RAWDNF_EVAL]);;
let TAUT_RAWDNF = top_thm();;

(* If p is NNF then RAWDNF p is WDNF *)

g `!p. ISNNF p ==> WDNF (RAWDNF p)`;;
e (REWRITE_TAC[WDNF]);;
e (MATCH_MP_TAC ISNNF_INDUCT);;
e (REWRITE_TAC[RAWDNF_CLAUSES; BINTREE_CONJ_CLAUSES; 
BINTREE_DISJ_CLAUSES; WLTR_CLAUSES]);;
e CONJ_TAC;;
 e (MATCH_MP_TAC LTR_INDUCT);;
 e (REWRITE_TAC[RAWDNF_CLAUSES; BINTREE_CONJ_CLAUSES; 
 BINTREE_DISJ_CLAUSES; WLTR_CLAUSES]);;
 e (MESON_TAC[]);;
e (REPEAT STRIP_TAC);;
e (MATCH_MP_TAC WDNF_DISTRIB_CONJ_LEMMA);;
e (ASM_REWRITE_TAC[]);;
let WDNF_RAWDNF = top_thm();;

(* RECDNF is a function that first turns a formula in NNF
      then applies RAWDNF. 
   We'll prove that this process turns the formula in DNF *)

let RECDNF = define
   `!p. RECDNF p = RAWDNF (NNF p)`;;

(* The EVALuation of a formula does not change after applying RECDNF *)

g `!v p. EVAL v (RECDNF p) = EVAL v p`;;
e (GEN_TAC THEN REWRITE_TAC[RECDNF; RAWDNF_EVAL; EVAL_NNF]);;
let EVAL_RECDNF = top_thm();;

(* RECDNF applied to any formula returns a WDNF formula *)

g `!p. WDNF (RECDNF p)`;;
e (MESON_TAC[NNF_ISNNF; WDNF_RAWDNF; RECDNF]);;
let RECDNF_IS_WDNF = top_thm();;

g `!p. ?q. RECDNF p = q /\ WDNF q /\ (!v. EVAL v p = EVAL v q)`;;
e (MESON_TAC[RECDNF_IS_WDNF; EVAL_RECDNF]);;
let WDNF_THM = top_thm();;

(* ========================================================================= *)
(* Functions that should be used later in the code *)

let NEGATE = define
  `NEGATE fm = match fm with
                 | (Not p)       -> p
                 | p             -> Not p`;;

g `!v p. EVAL v (NEGATE p) = ~EVAL v p`;;
e (GEN_TAC THEN MATCH_MP_TAC fm_INDUCT);;
e (REWRITE_TAC[EVAL; NEGATE]);;
let NEGATE_EVAL = top_thm();;

let STRING_TO_ATOM = define
`STRING_TO_ATOM [] = [] /\
(!s sl. STRING_TO_ATOM (CONS s sl) = 
   APPEND [Atom s] (STRING_TO_ATOM sl))`;;

(* ========================================================================= *)
(*                            DNF via truth tables                           *)
(* ========================================================================= *)

let LIST_INSERT = new_definition
`LIST_INSERT x l = if MEM x l then l 
               else CONS x l`;;

g `(!x. LIST_INSERT x [] = [x]) /\
(!x. LIST_INSERT x [x] = [x]) /\
(!x z. ~(x = z) ==> LIST_INSERT x [z] = [x; z]) /\
(!x y. ~(MEM x y) ==> LIST_INSERT x y = APPEND [x] y) /\
(!x y. MEM x y ==> LIST_INSERT x y = y) /\
(!x y. LIST_INSERT x (CONS x y) = CONS x y)`;;

e (REPEAT STRIP_TAC THEN REWRITE_TAC[LIST_INSERT]
THEN COND_CASES_TAC THEN ASM_MESON_TAC[MEM; APPEND]);;
let LIST_INSERT_CLAUSES = top_thm();;

let LIST_UNION = define
`(!l. LIST_UNION [] l = l) /\
(!h t l. LIST_UNION (CONS h t) l = LIST_UNION t (LIST_INSERT h l))`;;

(* ATOMLIST returns the list of atoms in a given formula *)

let ATOMLIST = define
`(ATOMLIST True = []) /\
(ATOMLIST False = []) /\
(!a. ATOMLIST (Atom a) = [a]) /\
(!p. ATOMLIST (Not p) = ATOMLIST p) /\
(!p q. ATOMLIST (p && q) = (LIST_UNION (ATOMLIST p) (ATOMLIST q))) /\
(!p q. ATOMLIST (p || q) = (LIST_UNION (ATOMLIST p) (ATOMLIST q))) /\
(!p q. ATOMLIST (p --> q) = (LIST_UNION (ATOMLIST p) (ATOMLIST q))) /\
(!p q. ATOMLIST (p <-> q) = (LIST_UNION (ATOMLIST p) (ATOMLIST q)))`;;

(* ========================================================================= *)
(* Given a list of formulas, LIST_DISJ returns those formulas disjuncted *)
let LIST_DISJ = define
  `(LIST_DISJ [] = False) /\
  (!p ps. LIST_DISJ (CONS p ps) = if ps = [] then p 
                         else p || (LIST_DISJ ps))`;;

(* When the list is empty, the EVALuation of LIST_DISJ is F *)
g `!v. EVAL v (LIST_DISJ []) <=> F`;;
e (REWRITE_TAC[LIST_DISJ; EVAL]);;
let EMPTY_LISTDISJ_EVAL = top_thm();;

(* When the list has a single element, 
the EVALuation of LIST_DISJ is the EVALuation of that element *)
g `!v p. EVAL v (LIST_DISJ [p]) <=> EVAL v p`;;
e (REWRITE_TAC[LIST_DISJ; EVAL]);;
let SINGLET_LISTDISJ_EVAL = top_thm();;

(* When the list has two elements, the EVALuation of LIST_DISJ 
is the EVALuation of the disjunction of its elements *)
g `!v q p. EVAL v (LIST_DISJ [p; q]) <=> EVAL v p \/ EVAL v q`;;
e (REWRITE_TAC[LIST_DISJ; EVAL; distinctness "list"]);;
top_thm();;

(* Given a list ps of formulas, the EVALuation of LIST_DISJ ps
is true if and only if at least the EVALuation of one of its elements is true *)
g `!v ps. EVAL v (LIST_DISJ ps) <=> EX (EVAL v) ps`;;
e (GEN_TAC THEN MATCH_MP_TAC list_INDUCT);;
e (REWRITE_TAC[EMPTY_LISTDISJ_EVAL; EX; LIST_DISJ]);;
e (REPEAT STRIP_TAC);;
e (COND_CASES_TAC);;
e (ASM_REWRITE_TAC[EX; EVAL]);;
e (ASM_REWRITE_TAC[LIST_DISJ; EX; EVAL]);;
let EVAL_LIST_DISJ = top_thm();;

(* ========================================================================= *)
(* Given a list of formulas, LIST_CONJ returns those formulas conjuncted *)
let LIST_CONJ = define
  `(LIST_CONJ [] = True) /\
  (!p ps. LIST_CONJ (CONS p ps) = if ps = [] then p 
                         else p && (LIST_CONJ ps))`;;

(* When the list is empty, the EVALuation of LIST_CONJ is T *)
g `!v. EVAL v (LIST_CONJ []) <=> T`;;
e (REWRITE_TAC[LIST_CONJ; EVAL]);;
let EMPTY_LISTCONJ_EVAL = top_thm();;

(* Given a list ps of formulas, the EVALuation of LIST_CONJ ps
is true if and only if the EVALuation of all its elements is true *)
g `!v ps. EVAL v (LIST_CONJ ps) <=> ALL (EVAL v) ps`;;
e (GEN_TAC THEN MATCH_MP_TAC list_INDUCT);;
e (REWRITE_TAC[EMPTY_LISTCONJ_EVAL; ALL; LIST_CONJ]);;
e (REPEAT STRIP_TAC);;
e (COND_CASES_TAC);;
e (ASM_REWRITE_TAC[ALL; EVAL]);;
e (ASM_REWRITE_TAC[LIST_CONJ; ALL; EVAL]);;
let EVAL_LIST_CONJ = top_thm();;

(* ========================================================================= *)
(* MK_LITS returns the conjunction of atoms of a formula
   if the given evaluation assigns true to those atoms 
      they appear normally, otherwise they appear negated *)

let MK_LITS = new_definition
`MK_LITS pvs v = LIST_CONJ (MAP (\p. if EVAL v p then p 
                                 else Not p) pvs)`;;

(* ASV stands for All Satisfied Valuations *)

let ASV = define 
          `(!subfn v:string->bool. ASV subfn v [] = if subfn v then [v] 
                                                    else []) /\
          (!subfn v p:string ps. ASV subfn v (CONS p ps) = 
             APPEND (ASV subfn (\q. if q = p then F else v q) ps) 
                    (ASV subfn (\q. if q = p then T else v q) ps))`;;   

(* We can now define the function that builds DNF functions
   through Truth Tables, DNFTT *)

let DNFTT = new_definition
`DNFTT fm = let pvs = ATOMLIST fm in 
            LIST_DISJ (MAP (MK_LITS (MAP Atom pvs)) 
                     (ASV (\v. EVAL v fm) (\s. F) pvs))`;;

g `DNFTT (Atom p) = Atom p`;;
e (REWRITE_TAC[DNFTT; ATOMLIST]);;
e (LET_TAC);;
e (POP_ASSUM SUBST_VAR_TAC);; 
e (REWRITE_TAC[EVAL; MAP; MK_LITS; MAP; LIST_DISJ; ASV; APPEND; LIST_CONJ]);;
top_thm();;

g `(DNFTT (((Atom p) || (Atom p) && (Atom p)) && 
   (Not (Atom p) || Not (Atom p)))) =
   False`;;
e (REWRITE_TAC[DNFTT; ATOMLIST; LIST_UNION; LIST_INSERT; MEM; EVAL]);;
e (LET_TAC);;
e (POP_ASSUM SUBST_VAR_TAC);;
e (REWRITE_TAC[ASV; MAP; APPEND; LIST_DISJ]);;
top_thm();;

g `(DNFTT (((Atom p) || (Atom q) && (Atom p)) && 
   (Not (Atom p) || Not (Atom p)))) =
   False`;;
e (REWRITE_TAC[DNFTT; ATOMLIST; LIST_UNION; LIST_INSERT; MEM; EVAL]);;
e (LET_TAC);;
e (POP_ASSUM SUBST_VAR_TAC);;
e (REWRITE_TAC[ASV; MAP; APPEND; LIST_DISJ]);;
e (COND_CASES_TAC);;
e (COND_CASES_TAC);;
e (REWRITE_TAC[DNFTT; ATOMLIST; LIST_UNION; LIST_INSERT; MEM; EVAL]);;
e (POP_ASSUM SUBST_VAR_TAC);;
e (REWRITE_TAC[MAP; MK_LITS; MAP; ASV; APPEND; LIST_DISJ]);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT]);;
e (COND_CASES_TAC);;
e (COND_CASES_TAC);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (REWRITE_TAC[MAP; MK_LITS; MAP; ASV; APPEND; LIST_DISJ]);;
e (COND_CASES_TAC);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (COND_CASES_TAC);;
e (COND_CASES_TAC);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (COND_CASES_TAC);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (COND_CASES_TAC);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (REWRITE_TAC[MEM]);;
e (COND_CASES_TAC);;
e (COND_CASES_TAC);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (COND_CASES_TAC);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
e (REWRITE_TAC[MAP; MK_LITS; LIST_UNION; ASV; LIST_INSERT; APPEND; LIST_DISJ]);;
top_thm();;

(* An example of formula from p56*)
g `!p q r. ~ (p = q) /\ ~ (p = r) /\ ~ (q = r) ==>
   (DNFTT (((Atom p) || (Atom q) && (Atom r)) && 
   (Not (Atom p) || Not (Atom r)))) =
   Not Atom q && Atom p && Not Atom r ||
 Atom q && Not Atom p && Atom r ||
 Atom q && Atom p && Not Atom r`;;
e (REWRITE_TAC[DNFTT; ATOMLIST; LIST_UNION; LIST_INSERT; MEM; EVAL]);;
e (REPEAT STRIP_TAC);;
e (ASM_REWRITE_TAC[MEM; LIST_UNION; LIST_INSERT]);;
e (LET_TAC);;
e (POP_ASSUM SUBST_VAR_TAC);;
e (ASM_REWRITE_TAC[MAP; ASV; APPEND]);;
e (ASM_REWRITE_TAC[MK_LITS; MAP; EVAL; LIST_DISJ; LIST_CONJ; NOT_CONS_NIL]);;
top_thm();;

(* Some ideas to further extend the code beyond what Harrison proposed *)

g `!fm. set_of_list (ATOMLIST fm) = ATOMSOF fm`;;
e (REWRITE_TAC[])

g `set_of_list (LIST_UNION [] []) = {}`;;
e (REWRITE_TAC[set_of_list; LIST_UNION; UNION] THEN SET_TAC[]);;
let SET_LIST_AUX_1 = top_thm();;

g `!p. set_of_list (LIST_UNION [] p) = set_of_list p`;;
e (REWRITE_TAC[set_of_list; LIST_UNION; UNION] THEN SET_TAC[]);;
let SET_LIST_AUX_2 = top_thm();;

g `!l r. set_of_list (LIST_UNION l [r]) = 
         (set_of_list l) UNION {r}`;;