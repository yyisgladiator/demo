(*  Title:        Automaton
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Frontend for deterministic Automatons, transformed from MontiArc-Automaton
*)

theory Automaton

imports "../SPF" "../../inc/Event" "../SpfStep"
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
definition ubElemWell::"(channel \<rightharpoonup> 'm::message) \<Rightarrow> bool" where
"ubElemWell f \<equiv> \<forall>c\<in> dom f. f\<rightharpoonup>c \<in> ctype c"

lemma ubElemWellI: assumes "ubElemWell f" and "c \<in> dom f"
  shows "(f \<rightharpoonup> c) \<in> ctype c"
  using assms(1) assms(2) ubElemWell_def by auto

lemma ubElemWellI2: assumes "ubElemWell f" and "c \<in> dom f"
and "(f \<rightharpoonup> c) = a"
shows "a \<in> ctype c"
  using assms(1) assms(2) assms(3) ubElemWellI by auto

fun automaton_well::"((('state \<times>(channel \<rightharpoonup> 'm::message)) \<Rightarrow> ('state \<times> 'm SB)) \<times> 'state \<times> 'm SB \<times> channel set \<times> channel set) \<Rightarrow> bool " where
"automaton_well (transition, initialState, initialOut, chIn, chOut) = (finite chIn \<and> (\<forall>s f. (dom f = chIn \<and> ubElemWell f) \<longrightarrow> ubDom\<cdot>(snd(transition (s,f))) = chOut))"

lemma automaton_wellI: assumes "finite In" and "\<And>s f. (dom f = In \<and> ubElemWell f) \<Longrightarrow> ubDom\<cdot>(snd(transition (s,f))) = Out" 
                       shows "automaton_well (transition, initialState, initialOut, In, Out)"
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
  by simp

(*spfRt and spfConc*)

lemma spfRt_dom [simp] :"ufDom\<cdot>(spfRt\<cdot>spf) = ufDom\<cdot>spf"
  unfolding spfRt_def
  by (simp add: ubclDom_ubundle_def ufapplyin_dom)

lemma spfConc_dom[simp]:"ufDom\<cdot>(spfConc sb \<cdot>spf) = ufDom\<cdot>spf"
  unfolding spfConc_def
  apply(subst ufapplyout_dom)
  apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast

lemma spfRt_ran [simp]:"ufRan\<cdot>(spfRt\<cdot>spf) = ufRan\<cdot>spf"
  unfolding spfRt_def
  apply(subst ufapplyin_ran2)
   apply (simp add: ubclDom_ubundle_def)
  by blast

lemma spfConc_ran [simp]:"ufRan\<cdot>(spfConc sb \<cdot>spf) = ufRan\<cdot>spf"
  unfolding spfConc_def
  apply(subst ufapplyout_ran)
   apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast

lemma spfRt_spfConc: "(spfRt\<cdot>(spfConc sb \<cdot>spf)) = (spfConc sb \<cdot>(spfRt\<cdot>spf))"
  unfolding spfConc_def
  unfolding spfRt_def
  apply(subst ufapply_eq)
  apply (simp add: ubclDom_ubundle_def)
  apply (metis ubclDom_ubundle_def ubconceq_dom)
  by blast

(*spfStateFix lemmas*)  
lemma spfsl_below_spfsf: "spfStateLeast In Out \<sqsubseteq> spfStateFix In Out\<cdot>F"
proof (simp add: spfStateFix_def, simp add: fixg_def)
  have "\<forall>x0 x1. ((x1::'a \<Rightarrow> ('b stream\<^sup>\<Omega>) ufun) \<sqsubseteq> (if x1 \<sqsubseteq> x0\<cdot>x1 then \<Squnion>uub. iterate uub\<cdot>x0\<cdot>x1 else x1)) = (if x1 \<sqsubseteq> x0\<cdot>x1 then x1 \<sqsubseteq> (\<Squnion>uub. iterate uub\<cdot>x0\<cdot>x1) else x1 \<sqsubseteq> x1)"
    by simp
  then show "spfStateLeast In Out \<sqsubseteq> F\<cdot>(spfStateLeast In Out) \<longrightarrow> spfStateLeast In Out \<sqsubseteq> (\<Squnion>n. iterate n\<cdot>F\<cdot>(spfStateLeast In Out))"
    by (metis (no_types) fixg_pre)
qed


lemma spfstatefix_dom:"ufDom\<cdot>((spfStateFix In Out\<cdot> f) s) = In"
  by (metis (mono_tags) below_fun_def spfStateLeast_def spfsl_below_spfsf ufdom_below_eq ufleast_ufdom)
  
    
lemma spfstatefix_ran:"ufRan\<cdot>((spfStateFix In Out\<cdot> f) s) = Out"
  by (metis below_fun_def spfStateLeast_ran spfsl_below_spfsf ufran_below)
    
lemma ufLeast_apply:assumes "ubDom\<cdot>sb = In" shows "ufLeast In  Out \<rightleftharpoons> sb = ubclLeast Out"
  apply (simp add: ufLeast_def)
  unfolding ubclLeast_ubundle_def
  unfolding ubclDom_ubundle_def
  by (simp add: assms)
    
   
lemma ubclDom2ubDom:"ubclDom\<cdot>sb = ubDom\<cdot>sb"
  by (simp add: ubclDom_ubundle_def)
    
section \<open>Lemma about helper\<close>
  
lemma helper_dom:"ufDom\<cdot>((helper (getTransition automat) s\<cdot>(h automat)) f) = ufDom\<cdot>((h automat) s)"
proof(simp add: helper_def)
  show "ufDom\<cdot>(h automat (fst (getTransition automat (s, f)))) = ufDom\<cdot>((h automat) s)"
    by(simp add: h_def spfstatefix_dom)
qed


lemma helper_ran:"ufRan\<cdot>((helper (getTransition automat) s\<cdot>(h automat)) f) = ufRan\<cdot>((h automat) s)"
proof(simp add: helper_def)
  show "ufRan\<cdot>(h automat (fst (getTransition automat (s, f)))) = ufRan\<cdot>(h automat s)"
    by(simp add: h_def spfstatefix_ran)
qed

section \<open>Lemma about h\<close>

lemma[simp]:"ufDom\<cdot>(h automat s) = getDom automat"
  by(simp add: h_def spfstatefix_dom)

lemma[simp]:"ufRan\<cdot>(h automat s) = getRan automat"
  by(simp add: h_def spfstatefix_ran)

(*Assumption for spfStep is always true for an automaton*)
lemma automat_dom_ran_well[simp]:assumes "ubDom\<cdot>sb = getDom automat" 
  shows "ufDom\<cdot>((helper (getTransition automat) s\<cdot>(h automat)) (spfStep_h2 (sbHdElem\<cdot>sb))) = getDom automat \<and>
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
 
lemma h_out_dom:assumes "ubDom\<cdot>sb = getDom automat" shows " ubDom\<cdot>(h automat state \<rightleftharpoons> sb) = getRan automat"
  by (simp add: assms spf_ubDom)

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
  by (simp add: assms(1) autGetNextOutput_def autGetNextState_def helper_def spfRt_spfConc)
    
lemma h_bottom: assumes "ubDom\<cdot>sb = getDom automat" and "\<exists>c\<in>getDom automat. sb  .  c = \<epsilon>"
  shows "(h automat s)\<rightleftharpoons>sb = ubclLeast (getRan automat)"
  apply(simp add: h_unfolding spfStep_def, subst beta_cfun, subst spfStep_cont, simp_all add: spfStep_h1_def)
  using assms(1) assms(2) sbHdElem_bottom_exI ufLeast_apply by blast

section \<open>Lemma about H\<close>








(* From here everything should be automatically transformed from MontiArc-Automaton *)
section \<open>Automaton Datatypes\<close>

(* Only on idea how the states could be implemented *)
datatype substate = even | odd  (* This are the actual states from MAA *)
datatype myState = State substate nat bool (* And these have also the variables *)

fun getVarI :: "myState \<Rightarrow> nat" where
"getVarI (State _ n _) = n"

fun getSubState :: "myState \<Rightarrow> substate" where
"getSubState (State s _ _) = s"



datatype myM = N nat | B bool

instance myM :: countable
apply(intro_classes)
by(countable_datatype)


instantiation myM :: message
begin
  fun ctype_myM :: "channel \<Rightarrow> myM set" where
  "ctype_myM c1 = range N"  |
  "ctype_myM c2 = range B"

  instance
    by(intro_classes)
end



section \<open>Automaton Functions\<close>

(* Creates a fitting SB given the right output values *)
(* Parameter:
  nat         \<Rightarrow> maps to channel c1, in MAA called "XXXX"
  bool        \<Rightarrow> maps to channel c2, in MAA calles "YYYY" *)
lift_definition createOutput :: "nat \<Rightarrow> bool \<Rightarrow> myM SB" is
"\<lambda>n b. ([c1 \<mapsto> \<up>(N n), c2 \<mapsto> \<up>(B b)])"
  apply(auto simp add: ubWell_def)
  sorry (* fails because stream instantiation is not there *)

function test4 :: "(channel \<rightharpoonup> nat stream) \<Rightarrow> bool" where
  "test4 [c1 \<mapsto> a] = True" |
  "dom f \<noteq> {c1} \<Longrightarrow> test4 f = False"
  sorry

(* Somehow define the transition function *)
(* use the createOutput function *)
function myTransition :: "(myState \<times>(channel \<rightharpoonup> myM)) \<Rightarrow> (myState \<times> myM SB)" where
"myTransition (State even n b,  [c1 \<mapsto> z])= (case z of N n \<Rightarrow> ((State odd n b), createOutput n True) | _ \<Rightarrow> undefined)" |
"myTransition (State odd n b, [c1 \<mapsto> z]) = ((State even n b), createOutput 0 False)"  |

"dom f\<noteq> {c1} \<Longrightarrow> myTransition (_,f) = undefined"
  apply auto
  apply (smt dom_eq_singleton_conv getSubState.elims myM.exhaust substate.exhaust)
  using map_upd_eqD1 apply fastforce
  apply (metis option.simps(3))
  by (metis option.simps(3))

lift_definition myAutomaton :: "(myState, myM) automaton" is "(myTransition, State even 0 True, ubLeast {}, {}, {})"
  sorry  (* In the final form of the automaton datatype we will have to proof stuff *)

definition mySPF :: "myM SPF" where
"mySPF = H myAutomaton"

section \<open>Automaton Lemma\<close>

end
