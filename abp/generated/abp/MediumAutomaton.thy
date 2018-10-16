(*
 * DO NOT MODIFY!
 * This file was generated from Medium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 16, 2018 10:17:27 PM by isartransformer 3.1.0
 *)
theory MediumAutomaton
  imports MediumDatatype MediumStates automat.ndAutomaton automat.ndaComplete automat.ndaTotal

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Function for each transition to allow transition overlap\<close>

fun mediumTransitionH_0_0 :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"mediumTransitionH_0_0 (MediumState Single var_coin, (Msg port_i)) =
  (if (var_coin=0) then {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)}
   else {})" |
"mediumTransitionH_0_0 _ = {}"

fun mediumTransitionH_0_1 :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"mediumTransitionH_0_1 (MediumState Single var_coin, (Msg port_i)) =
  (if (var_coin=1) then {(MediumState Single var_coin, (mediumOut_o (Msg (port_i)))) | var_coin . (var_coin = 0 \<or> var_coin = 1)}
   else {})" |
"mediumTransitionH_0_1 _ = {}"

fun mediumTransitionH_1_0 :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"mediumTransitionH_1_0 (MediumState Single var_coin, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if (var_coin=0) then {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)}
   else {})" |
"mediumTransitionH_1_0 _ = {}"

fun mediumTransitionH_1_1 :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"mediumTransitionH_1_1 (MediumState Single var_coin, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if (var_coin=1) then {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)}
   else {})" |
"mediumTransitionH_1_1 _ = {}"


section \<open>Automaton definition\<close>

(* Helper that combines all transitions into one function *)
fun mediumTransitionH :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumTransitionH input = Rev ((mediumTransitionH_0_0 input) \<union> (mediumTransitionH_0_1 input) \<union> (mediumTransitionH_1_0 input) \<union> (mediumTransitionH_1_1 input))"

(* Transition function *)
definition mediumTransition :: "(MediumState \<times> ('e::countable) mediumMessage tsyn sbElem) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumTransition = (\<lambda> (s,b). (if (sbeDom b) = mediumDom then mediumTransitionH (s, (mediumElem_get_i b)) else undefined))"

(* Initial states with initial outputs *)
definition mediumInitials :: "(MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumInitials = Rev (setflat\<cdot>{{(MediumState Single (var_coin::int), (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)}})"

(* The -potentially partial- automaton *)
lift_definition mediumAutomaton_partial :: "(MediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" is
"(mediumTransition, mediumInitials, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def mediumRan_def)

(* The final -totalised- automaton *)
definition mediumAutomaton :: "(MediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" where
"mediumAutomaton = ndaChaosCompletion mediumAutomaton_partial"

(* Stream processing function for each state (handy for step lemmata) *)
definition mediumStep :: "MediumState \<Rightarrow> ('e::countable) mediumMessage tsyn SPS" where
"mediumStep = nda_h mediumAutomaton"

(* The final SPS *)
definition mediumSPS :: "('e::countable) mediumMessage tsyn SPS" where
"mediumSPS = nda_H (mediumAutomaton::(MediumState, ('e::countable) mediumMessage tsyn) ndAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma mediumautomaton_trans[simp]: "ndaTransition\<cdot>mediumAutomaton = chaosTransCompletion mediumTransition"
  apply(simp add: mediumAutomaton_def)
  by(simp add: mediumAutomaton_partial.rep_eq ndaTransition.rep_eq)

lemma mediumautomaton_initialstate[simp]: "ndaInitialState\<cdot>mediumAutomaton = (initCompletion chaosInit_h) mediumInitials"
  apply(simp add: mediumAutomaton_def)
  by(simp add: mediumAutomaton_partial.rep_eq ndaInitialState.rep_eq)

lemma mediumautomaton_dom[simp]: "ndaDom\<cdot>mediumAutomaton = mediumDom"
  apply(simp add: mediumAutomaton_def)
  by(simp add: mediumAutomaton_partial.rep_eq ndaDom.rep_eq)

lemma mediumautomaton_ran[simp]: "ndaRan\<cdot>mediumAutomaton = mediumRan"
  apply(simp add: mediumAutomaton_def)
  by(simp add: mediumAutomaton_partial.rep_eq ndaRan.rep_eq)


section \<open>Consistency\<close>

lemma mediumstep_consistent [simp]: "uspecIsConsistent (mediumStep s)"
  unfolding mediumStep_def
  by(rule nda_consistent, simp_all)

lemma mediumsps_consistent [simp]: "uspecIsConsistent mediumSPS"
  oops


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 16:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma mediumTransition_0_0:
  assumes "var_coin=0"
    shows "inv Rev (mediumTransition ((MediumState Single var_coin), (mediumElemIn_i (Msg port_i))))
         \<supseteq> {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)}"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 17:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma mediumTransition_0_1:
  assumes "var_coin=1"
    shows "inv Rev (mediumTransition ((MediumState Single var_coin), (mediumElemIn_i (Msg port_i))))
         \<supseteq> {(MediumState Single var_coin, (mediumOut_o (Msg (port_i)))) | var_coin . (var_coin = 0 \<or> var_coin = 1)}"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 16:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma mediumTransition_1_0:
  assumes "var_coin=0"
    shows "inv Rev (mediumTransition ((MediumState Single var_coin), (mediumElemIn_i null)))
         \<supseteq> {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)}"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 17:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma mediumTransition_1_1:
  assumes "var_coin=1"
    shows "inv Rev (mediumTransition ((MediumState Single var_coin), (mediumElemIn_i null)))
         \<supseteq> {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)}"
  using assms by(auto simp add: mediumTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma mediumSps2Step: "mediumSPS = ndaConcOutFlatten mediumDom mediumRan (initCompletion chaosInit_h mediumInitials) mediumStep"
  by (simp add: mediumSPS_def mediumStep_def nda_H_def)

(* Line 16:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma mediumStep_0_0:
  assumes "var_coin=0"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (mediumStep (MediumState Single var_coin))
         \<sqsubseteq> uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o null) (mediumStep (MediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  sorry (* Muss sorry wegen mediumSteps *)

(* Line 17:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma mediumStep_0_1:
  assumes "var_coin=1"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (mediumStep (MediumState Single var_coin))
         \<sqsubseteq> uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o (Msg (port_i))) (mediumStep (MediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  sorry (* Muss sorry wegen mediumSteps *)

(* Line 16:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma mediumStep_1_0:
  assumes "var_coin=0"
    shows "spsConcIn  (mediumIn_i null) (mediumStep (MediumState Single var_coin))
         \<sqsubseteq> uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o null) (mediumStep (MediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  sorry (* Muss sorry wegen mediumSteps *)

(* Line 17:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma mediumStep_1_1:
  assumes "var_coin=1"
    shows "spsConcIn  (mediumIn_i null) (mediumStep (MediumState Single var_coin))
         \<sqsubseteq> uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o null) (mediumStep (MediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  sorry (* Muss sorry wegen mediumSteps *)

lemmas mediumSteps = mediumStep_0_0 mediumStep_0_1 mediumStep_1_0 mediumStep_1_1

end