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

(* Converter function. *)
  (* definition should be right, but needs to be nicer *)
 

fun automaton_well::"((('state \<times>(channel \<rightharpoonup> 'm::message)) \<Rightarrow> ('state \<times> 'm SB)) \<times> 'state \<times> 'm SB \<times> channel set \<times> channel set) \<Rightarrow> bool " where
"automaton_well (transition, initialState, initialOut, chIn, chOut) = (finite chIn \<and> (\<forall>s f. dom f = chIn \<longrightarrow> ubDom\<cdot>(snd(transition (s,f))) = chOut))"

lemma automaton_wellI: assumes "finite In" and "(\<forall>s f. dom f = In \<longrightarrow> ubDom\<cdot>(snd(transition (s,f))) = Out)" shows "automaton_well (transition, initialState, initialOut, In, Out)"
by(simp add: assms)

 
lemma automaton_ex:"automaton_well ((\<lambda>f. (myState, ubLeast {})), State, ubLeast {}, {}, {})"
  by(rule automaton_wellI,auto)

  

typedef ('state::type, 'm::message) automaton = 
  "{f::(('state \<times>(channel \<rightharpoonup> 'm)) \<Rightarrow> ('state \<times> 'm SB)) \<times> 'state \<times> 'm SB \<times> channel set \<times> channel set. automaton_well f}"
  using automaton_ex exI automaton_wellI  by fastforce
    
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






lemma automat_well[simp]:"automaton_well (Rep_automaton automat)"
  using Rep_automaton by auto
    
lemma automat_finite_dom[simp]:"finite (getDom automat)"
proof -
  have "\<forall>p. \<not> automaton_well p \<or> (\<exists>f a u C Ca. p = (f, a::'a, u::'b stream\<^sup>\<Omega>, C, Ca) \<and> finite C \<and> (\<forall>a fa. dom fa \<noteq> C \<or> UBundle.ubDom\<cdot>(snd (f (a, fa))) = Ca))"
    by auto
  then show ?thesis
    by (metis (no_types) automat_well getDom_def prod.sel(1) prod.sel(2))
qed

(*spfStateFix lemmas*)  
lemma spfsl_below_spfsf:"spfStateLeast In Out \<sqsubseteq> spfStateFix In Out\<cdot>f"
  proof(simp add: spfStateFix_def, auto)
    assume a1:"\<forall>x::'a. UFun.ufDom\<cdot>((f\<cdot>(spfStateLeast In Out)) x) = In \<and> UFun.ufRan\<cdot>((f\<cdot>(spfStateLeast In Out)) x) = Out"
    then have "spfStateLeast In Out \<sqsubseteq> (f\<cdot>(spfStateLeast In Out))"
      by simp
    then show"spfStateLeast In Out \<sqsubseteq> fixg (spfStateLeast In Out) f" 
     by (smt fixg_def below_lub iterate_0 iterate_Suc2 monofunE monofun_Rep_cfun2 po_class.chain_def)
  qed
    
lemma spfstatefix_dom:"ufDom\<cdot>((spfStateFix In Out\<cdot> f) s) = In"
  by (metis below_fun_def spfsl_below_spfsf spfStateLeast_dom ufdom_below_eq)
  
    
lemma spfstatefix_ran:"ufRan\<cdot>((spfStateFix In Out\<cdot> f) s) = Out"
  by (metis below_fun_def spfsl_below_spfsf spfStateLeast_ran ufran_below)
(*spfStateFix lemmas end*) 
    
(*Sorrys*)
    
lemma spfRt_dom:"ufDom\<cdot>(spfRt\<cdot>spf) = ufDom\<cdot>spf"
  sorry

lemma spfConc_dom:"ufDom\<cdot>(spfConc sb \<cdot>spf) = ufDom\<cdot>spf"
  sorry
    
lemma spfRt_ran:"ufRan\<cdot>(spfRt\<cdot>spf) = ufRan\<cdot>spf"
  sorry

lemma spfConc_ran:"ufRan\<cdot>(spfConc sb \<cdot>spf) = ufRan\<cdot>spf"
  sorry
    

lemma [simp]:"dom (inv convDiscrUp f) = dom f"
  apply(unfold convDiscrUp_def)
  sorry
 
 
lemma spfRt_spfConc: "(spfRt\<cdot>(spfConc sb \<cdot>spf)) = (spfConc sb \<cdot>(spfRt\<cdot>spf))"
  sorry

(*Sorrys ende*)
    
lemma helper_dom:"ufDom\<cdot>((helper (getTransition automat) s\<cdot>(h automat)) f) = ufDom\<cdot>((h automat) s)"
proof(simp add: helper_def spfRt_dom spfConc_dom) 
  show "ufDom\<cdot>(h automat (fst (getTransition automat (s, f)))) = ufDom\<cdot>((h automat) s)"
    by(simp add: h_def spfstatefix_dom)
qed
  
  
lemma helper_ran:"ufRan\<cdot>((helper (getTransition automat) s\<cdot>(h automat)) f) = ufRan\<cdot>((h automat) s)"
proof(simp add: helper_def spfRt_ran spfConc_ran) 
  show "ufRan\<cdot>(h automat (fst (getTransition automat (s, f)))) = ufRan\<cdot>(h automat s)"
    by(simp add: h_def spfstatefix_ran)
qed

  
lemma [simp]:"dom (inv convDiscrUp (sbHdElem\<cdot>sb)) = ubDom\<cdot>sb"
  by(simp add: ubdom_insert)

section \<open>Lemma about h\<close>
  
lemma[simp]:"ufDom\<cdot>(h automat s) = getDom automat"  
  by(simp add: h_def spfstatefix_dom) 
    
lemma[simp]:"ufRan\<cdot>(h automat s) = getRan automat"
  by(simp add: h_def spfstatefix_ran)

(*Assumption for spfStep is always true for an automaton*)
lemma automat_dom_ran_well[simp]:assumes "ubDom\<cdot>sb = getDom automat" shows "ufDom\<cdot>((helper (getTransition automat) s\<cdot>(h automat)) (spfStep_h2 (sbHdElem\<cdot>sb))) = getDom automat \<and>
                   ufRan\<cdot>((helper (getTransition automat) s\<cdot>(h automat)) (spfStep_h2 (sbHdElem\<cdot>sb))) = getRan automat" 
proof
  show "ufDom\<cdot>((helper (getTransition automat) s\<cdot>(h automat)) (spfStep_h2 (sbHdElem\<cdot>sb))) = getDom automat"
    by(simp add: helper_dom)
next
  show "ufRan\<cdot>((helper (getTransition automat) s\<cdot>(h automat)) (spfStep_h2 (sbHdElem\<cdot>sb))) = getRan automat"
    by(simp add: helper_ran)
qed

  
lemma h_dom [simp]: "ufDom\<cdot>(h automat s) = getDom automat" 
  apply(simp add: h_def h_cont)
  by(subst spfStateFix_fix,simp_all)

lemma h_ran [simp]: "ufRan\<cdot>(h automat s) = getRan automat"
  apply(simp add: h_def h_cont)
  by(subst spfStateFix_fix,simp_all)

lemma h_unfolding: "(h automat s) = spfStep (getDom automat) (getRan automat)\<cdot>(helper (getTransition automat) s\<cdot>(h automat))"
  apply(simp add: h_def)
  by(subst spfStateFix_fix,simp_all)

lemma h_step: assumes "ubDom\<cdot>sb = getDom automat" and "\<forall>c\<in>getDom automat. sb  .  c \<noteq> \<epsilon>" 
            shows "(h automat s)\<rightleftharpoons>sb = ((helper (getTransition automat) s\<cdot>(h automat)) ((inv convDiscrUp)(sbHdElem\<cdot>sb))) \<rightleftharpoons>sb"
  apply (simp add: h_unfolding)
  apply(rule SpfStep.stepstep_step)
  by (simp_all add: assms)

definition autGetNextState:: "('s::type, 'm::message) automaton \<Rightarrow> 's \<Rightarrow>  ((channel \<rightharpoonup> 'm)) \<Rightarrow> 's" where
"autGetNextState aut s m = fst ((getTransition aut) (s,m))"

definition autGetNextOutput:: "('s::type, 'm::message) automaton \<Rightarrow> 's \<Rightarrow>  ((channel \<rightharpoonup> 'm)) \<Rightarrow>  'm SB" where
"autGetNextOutput aut s m = snd ((getTransition aut) (s,m))"
       
    
(* ToDo: make a bit more readable *)
lemma h_final: 
  assumes "ubDom\<cdot>sb = getDom automat" and "\<forall>c\<in>getDom automat. sb  .  c \<noteq> \<epsilon>"
  shows "(h automat s)\<rightleftharpoons>sb = 
  spfConc (autGetNextOutput automat s ((inv convDiscrUp)(sbHdElem\<cdot>sb)))\<cdot>(spfRt\<cdot>(h automat (autGetNextState automat s ((inv convDiscrUp)(sbHdElem\<cdot>sb))))) \<rightleftharpoons>sb"
  apply(subst h_step, simp_all add: assms)
  by(simp add: autGetNextOutput_def autGetNextState_def helper_def spfRt_spfConc)
  

section \<open>Lemma about H\<close>







end