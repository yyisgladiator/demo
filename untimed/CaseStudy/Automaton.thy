(*  Title:        Automaton
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Frontend for deterministic Automatons, transformed from MontiArc-Automaton
*)

theory Automaton

imports "../../timesyn/tsynBundle" "../SpfStep"
begin
default_sort type

section \<open>Backend Signatures\<close>
(* This stuff is only here until the functions are defined in the backend, they will be in SPF.thy *)


(* VERY Basic automaton type *)
(* ToDo: wellformed condition *)

(* FYI: in the non-deterministic case the automaton will be a cpo *)

(* The content is:
  transition function \<times> initial state \<times> initial Output \<times> input domain \<times> output domain *)

definition automaton_well::"(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> ('state \<times> 'm SB)) \<times> 'state \<times> 'm SB \<times> channel set \<times> channel set \<Rightarrow> bool " where
"automaton_well automaton = finite (fst(snd(snd(snd automaton))))"

typedef ('state::type, 'm::message) automaton = 
  "{f::(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> ('state \<times> 'm SB)) \<times> 'state \<times> 'm SB \<times> channel set \<times> channel set. True}"
  by blast
setup_lifting type_definition_automaton

definition getTransition :: "('s, 'm::message) automaton \<Rightarrow> (('s \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> ('s \<times> 'm SB))" where
"getTransition automat = fst (Rep_automaton automat)"

definition getInitialState :: "('s, 'm::message) automaton \<Rightarrow> 's" where
"getInitialState automat = fst (snd (Rep_automaton automat))"

definition getInitialOutput :: "('s, 'm::message) automaton \<Rightarrow> 'm SB" where
"getInitialOutput automat = fst (snd (snd (Rep_automaton automat)))"

definition getDom :: "('s, 'm::message) automaton \<Rightarrow> channel set" where
"getDom automat = fst (snd (snd (snd (Rep_automaton automat))))"

definition getRan :: "('s, 'm::message) automaton \<Rightarrow> channel set" where
"getRan automat = (snd (snd (snd (snd (Rep_automaton automat)))))"


(* HK is defining this. returns the fixpoint *)
(* thm spfStateFix_def *)
(* definition myFixxer :: "channel set \<Rightarrow> channel set \<Rightarrow> (('s \<Rightarrow> 'm::message SPF)\<rightarrow>('s \<Rightarrow> 'm SPF)) \<rightarrow> ('s \<Rightarrow> 'm SPF)" where
"myFixxer = undefined" *)
(* is defined in spfStep.thy 
definition spfStep :: "channel set\<Rightarrow> channel set \<Rightarrow> ((channel \<Rightarrow> 'm option) \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF" where
"spfStep = undefined"
*)
(* Defined by SWS *)
(* thm spfApplyIn_def
thm spfRt_def *)
(* 
definition spfRt :: "'m SPF \<rightarrow> 'm SPF" where
"spfRt = undefined"
*)


(* thm spfConc_def *)
(*
(* Defined by JCB *)
definition spfCons :: "'m SB \<Rightarrow> 'm SPF \<rightarrow> 'm SPF" where
"spfCons = undefined"
*)

(* Converter function. *)
  (* definition should be right, but needs to be nicer *)
definition helper:: "(('s \<times>'e) \<Rightarrow> ('s \<times> 'm::message  SB)) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> 'm SPF) \<rightarrow> ('e \<Rightarrow> 'm SPF)" where
"helper f s \<equiv> \<Lambda> h. (\<lambda> e. spfRt\<cdot>(spfConc (snd (f (s,e)))\<cdot>(h (fst (f (s,e))))))" 

lemma helper_cont: "cont (\<lambda>h. (\<lambda> e. spfConc (snd (f (s,e)))\<cdot>(h (fst (f (s,e))))))"
  by simp

(* As defined in Rum96 *)
definition h :: "('s::type, 'm::message) automaton \<Rightarrow> ('s \<Rightarrow> 'm SPF)" where
"h automat = spfStateFix (getDom automat)(getRan automat)\<cdot>
     (\<Lambda> h. (\<lambda>s. spfStep  (getDom automat) (getRan automat)\<cdot>(helper (getTransition automat) s\<cdot>h)))"

lemma h_cont: "cont (\<lambda> h. (\<lambda>s. spfStep  (getDom automat) (getRan automat)\<cdot>(helper (getTransition automat) s\<cdot>h)))"
  by simp

(* This function also prepends the first SB ... *)
(* But basically she just calls h *)
definition H :: "('s, 'm::message) automaton \<Rightarrow> 'm SPF" where
"H automat = spfConc (getInitialOutput automat)\<cdot>(h automat (getInitialState automat))"




section \<open>stuff i need in spfStep\<close>
lemma stepstep_step: "spfStep In Out\<cdot>f\<rightleftharpoons>sb = (f ((inv convDiscrUp)(sbHdElem\<cdot>sb)))\<rightleftharpoons>sb"
  sorry




section \<open>Lemma about h\<close>
(*
lemma h_dom [simp]: "ufDom\<cdot>(h automat s) = getDom automat"
  by (metis (no_types, lifting) Abs_cfun_inverse2 h_cont h_def spfStateFix_fix spfstep_dom spfstep_ran automaton_well_def finite_code) 

lemma h_ran [simp]: "ufRan\<cdot>(h automat s) = getRan automat"
  by (metis spfstep_dom spfstep_ran Automaton.stepstep_step ufran_2_ubdom2 finite_code)

lemma h_unfolding: "(h automat s) = spfStep (getDom automat) (getRan automat)\<cdot>(helper (getTransition automat) s\<cdot>(h automat))"
  by (metis (no_types, lifting) Abs_cfun_inverse2 h_cont h_def spfStateFix_fix spfstep_dom spfstep_ran finite_code)

lemma h_step: assumes "ubDom\<cdot>sb = getDom automat" and "\<forall>c\<in>getDom automat. sb  .  c \<noteq> \<epsilon>" 
              and "ufDom\<cdot>((helper (getTransition automat) s\<cdot>(h automat)) (spfStep_h2 (sbHdElem\<cdot>sb))) = getDom automat \<and>
                   ufRan\<cdot>((helper (getTransition automat) s\<cdot>(h automat)) (spfStep_h2 (sbHdElem\<cdot>sb))) = getRan automat"
            shows "(h automat s)\<rightleftharpoons>sb = ((helper (getTransition automat) s\<cdot>(h automat)) ((inv convDiscrUp)(sbHdElem\<cdot>sb))) \<rightleftharpoons>sb"
  apply (simp add: h_unfolding)
  apply(rule SpfStep.stepstep_step)
  by (simp add: assms)+

definition autGetNextState:: "('s::type, 'm::message) automaton \<Rightarrow> 's \<Rightarrow>  ((channel \<rightharpoonup> 'm)) \<Rightarrow> 's" where
"autGetNextState aut s m = fst ((getTransition aut) (s,m))"

definition autGetNextOutput:: "('s::type, 'm::message) automaton \<Rightarrow> 's \<Rightarrow>  ((channel \<rightharpoonup> 'm)) \<Rightarrow>  'm SB" where
"autGetNextOutput aut s m = snd ((getTransition aut) (s,m))"

(* ToDo: make a bit more readable *)
lemma h_final: 
  assumes "ubDom\<cdot>sb = getDom automat"
  shows "(h automat s)\<rightleftharpoons>sb = 
  spfConc (autGetNextOutput automat s ((inv convDiscrUp)(sbHdElem\<cdot>sb)))\<cdot>(spfRt\<cdot>(h automat (autGetNextState automat s ((inv convDiscrUp)(sbHdElem\<cdot>sb))))) \<rightleftharpoons>sb"
  unfolding h_step 
  by(simp add: helper_def autGetNextOutput_def autGetNextState_def assms spfRt_def )
  *)

section \<open>Lemma about H\<close>







end