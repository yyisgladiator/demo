(*
 * DO NOT MODIFY!
 * This file was generated from Medium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 16, 2018 10:34:43 PM by isartransformer 3.1.0
 *)
theory MediumAutomaton
  imports MediumDatatype MediumStates automat.ndAutomaton automat.ndaComplete automat.ndaTotal

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Function for each transition to allow transition overlap\<close>

fun mediumTransitionH_0_0 :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"mediumTransitionH_0_0 (MediumState Single, (Msg port_i)) =
  (if (True) then {(MediumState Single, (mediumOut_o null))}
   else {})" |
"mediumTransitionH_0_0 _ = {}"

fun mediumTransitionH_0_1 :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"mediumTransitionH_0_1 (MediumState Single, (Msg port_i)) =
  (if (True) then {(MediumState Single, (mediumOut_o (Msg (port_i))))}
   else {})" |
"mediumTransitionH_0_1 _ = {}"

fun mediumTransitionH_1_0 :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"mediumTransitionH_1_0 (MediumState Single, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if (True) then {(MediumState Single, (mediumOut_o null))}
   else {})" |
"mediumTransitionH_1_0 _ = {}"

fun mediumTransitionH_1_1 :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"mediumTransitionH_1_1 (MediumState Single, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if (True) then {(MediumState Single, (mediumOut_o null))}
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
"mediumInitials = Rev (setflat\<cdot>{{(MediumState Single , (mediumOut_o null))}})"

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

(* Line 14:  Single / {o=null}; *)
lemma mediumTransition_0_0:
  assumes "True"
    shows "inv Rev (mediumTransition ((MediumState Single ), (mediumElemIn_i (Msg port_i))))
         \<supseteq> {(MediumState Single, (mediumOut_o null))}"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 15:  Single / {o=i}; *)
lemma mediumTransition_0_1:
  assumes "True"
    shows "inv Rev (mediumTransition ((MediumState Single ), (mediumElemIn_i (Msg port_i))))
         \<supseteq> {(MediumState Single, (mediumOut_o (Msg (port_i))))}"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 14:  Single / {o=null}; *)
lemma mediumTransition_1_0:
  assumes "True"
    shows "inv Rev (mediumTransition ((MediumState Single ), (mediumElemIn_i null)))
         \<supseteq> {(MediumState Single, (mediumOut_o null))}"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 15:  Single / {o=i}; *)
lemma mediumTransition_1_1:
  assumes "True"
    shows "inv Rev (mediumTransition ((MediumState Single ), (mediumElemIn_i null)))
         \<supseteq> {(MediumState Single, (mediumOut_o null))}"
  using assms by(auto simp add: mediumTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma mediumSps2Step: "mediumSPS = ndaConcOutFlatten mediumDom mediumRan (initCompletion chaosInit_h mediumInitials) mediumStep"
  by (simp add: mediumSPS_def mediumStep_def nda_H_def)

(* Line 14:  Single / {o=null}; *)
lemma mediumStep_0_0:
  assumes "True"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (mediumStep (MediumState Single ))
         \<sqsubseteq> spsConcOut (mediumOut_o null) (mediumStep (MediumState Single))"
  sorry (* Muss sorry wegen mediumSteps *)

(* Line 15:  Single / {o=i}; *)
lemma mediumStep_0_1:
  assumes "True"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (mediumStep (MediumState Single ))
         \<sqsubseteq> spsConcOut (mediumOut_o (Msg (port_i))) (mediumStep (MediumState Single))"
  sorry (* Muss sorry wegen mediumSteps *)

(* Line 14:  Single / {o=null}; *)
lemma mediumStep_1_0:
  assumes "True"
    shows "spsConcIn  (mediumIn_i null) (mediumStep (MediumState Single ))
         \<sqsubseteq> spsConcOut (mediumOut_o null) (mediumStep (MediumState Single))"
  sorry (* Muss sorry wegen mediumSteps *)

(* Line 15:  Single / {o=i}; *)
lemma mediumStep_1_1:
  assumes "True"
    shows "spsConcIn  (mediumIn_i null) (mediumStep (MediumState Single ))
         \<sqsubseteq> spsConcOut (mediumOut_o null) (mediumStep (MediumState Single))"
  sorry (* Muss sorry wegen mediumSteps *)

lemmas mediumSteps = mediumStep_0_0 mediumStep_0_1 mediumStep_1_0 mediumStep_1_1

end