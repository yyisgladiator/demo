(*
 * DO NOT MODIFY!
 * This file was generated from IdMedium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 16, 2018 10:17:27 PM by isartransformer 3.1.0
 *)
theory IdMediumAutomaton
  imports MediumDatatype IdMediumStates automat.ndAutomaton automat.ndaComplete automat.ndaTotal

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Function for each transition to allow transition overlap\<close>

fun idMediumTransitionH_0_0 :: "(IdMediumState \<times> ('e tsyn)) \<Rightarrow> (IdMediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"idMediumTransitionH_0_0 (IdMediumState Single, (Msg port_i)) =
  (if (True) then {(IdMediumState Single, (mediumOut_o (Msg (port_i))))}
   else {})" |
"idMediumTransitionH_0_0 _ = {}"

fun idMediumTransitionH_1_0 :: "(IdMediumState \<times> ('e tsyn)) \<Rightarrow> (IdMediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"idMediumTransitionH_1_0 (IdMediumState Single, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if (True) then {(IdMediumState Single, (mediumOut_o null))}
   else {})" |
"idMediumTransitionH_1_0 _ = {}"


section \<open>Automaton definition\<close>

(* Helper that combines all transitions into one function *)
fun idMediumTransitionH :: "(IdMediumState \<times> ('e tsyn)) \<Rightarrow> (IdMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"idMediumTransitionH input = Rev ((idMediumTransitionH_0_0 input) \<union> (idMediumTransitionH_1_0 input))"

(* Transition function *)
definition idMediumTransition :: "(IdMediumState \<times> ('e::countable) mediumMessage tsyn sbElem) \<Rightarrow> (IdMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"idMediumTransition = (\<lambda> (s,b). (if (sbeDom b) = mediumDom then idMediumTransitionH (s, (mediumElem_get_i b)) else undefined))"

(* Initial states with initial outputs *)
definition idMediumInitials :: "(IdMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"idMediumInitials = Rev (setflat\<cdot>{{(IdMediumState Single , (mediumOut_o null))}})"

(* The -potentially partial- automaton *)
lift_definition idMediumAutomaton_partial :: "(IdMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" is
"(idMediumTransition, idMediumInitials, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def mediumRan_def)

(* The final -totalised- automaton *)
definition idMediumAutomaton :: "(IdMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" where
"idMediumAutomaton = ndaChaosCompletion idMediumAutomaton_partial"

(* Stream processing function for each state (handy for step lemmata) *)
definition idMediumStep :: "IdMediumState \<Rightarrow> ('e::countable) mediumMessage tsyn SPS" where
"idMediumStep = nda_h idMediumAutomaton"

(* The final SPS *)
definition idMediumSPS :: "('e::countable) mediumMessage tsyn SPS" where
"idMediumSPS = nda_H (idMediumAutomaton::(IdMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma idmediumautomaton_trans[simp]: "ndaTransition\<cdot>idMediumAutomaton = chaosTransCompletion idMediumTransition"
  apply(simp add: idMediumAutomaton_def)
  by(simp add: idMediumAutomaton_partial.rep_eq ndaTransition.rep_eq)

lemma idmediumautomaton_initialstate[simp]: "ndaInitialState\<cdot>idMediumAutomaton = (initCompletion chaosInit_h) idMediumInitials"
  apply(simp add: idMediumAutomaton_def)
  by(simp add: idMediumAutomaton_partial.rep_eq ndaInitialState.rep_eq)

lemma idmediumautomaton_dom[simp]: "ndaDom\<cdot>idMediumAutomaton = mediumDom"
  apply(simp add: idMediumAutomaton_def)
  by(simp add: idMediumAutomaton_partial.rep_eq ndaDom.rep_eq)

lemma idmediumautomaton_ran[simp]: "ndaRan\<cdot>idMediumAutomaton = mediumRan"
  apply(simp add: idMediumAutomaton_def)
  by(simp add: idMediumAutomaton_partial.rep_eq ndaRan.rep_eq)


section \<open>Consistency\<close>

lemma idmediumstep_consistent [simp]: "uspecIsConsistent (idMediumStep s)"
  unfolding idMediumStep_def
  by(rule nda_consistent, simp_all)

lemma idmediumsps_consistent [simp]: "uspecIsConsistent idMediumSPS"
  oops


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 14:  Single / {o=i}; *)
lemma idMediumTransition_0_0:
  assumes "True"
    shows "inv Rev (idMediumTransition ((IdMediumState Single ), (mediumElemIn_i (Msg port_i))))
         \<supseteq> {(IdMediumState Single, (mediumOut_o (Msg (port_i))))}"
  using assms by(auto simp add: idMediumTransition_def assms)

(* Line 14:  Single / {o=i}; *)
lemma idMediumTransition_1_0:
  assumes "True"
    shows "inv Rev (idMediumTransition ((IdMediumState Single ), (mediumElemIn_i null)))
         \<supseteq> {(IdMediumState Single, (mediumOut_o null))}"
  using assms by(auto simp add: idMediumTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma idMediumSps2Step: "idMediumSPS = ndaConcOutFlatten mediumDom mediumRan (initCompletion chaosInit_h idMediumInitials) idMediumStep"
  by (simp add: idMediumSPS_def idMediumStep_def nda_H_def)

(* Line 14:  Single / {o=i}; *)
lemma idMediumStep_0_0:
  assumes "True"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (idMediumStep (IdMediumState Single ))
         \<sqsubseteq> spsConcOut (mediumOut_o (Msg (port_i))) (idMediumStep (IdMediumState Single))"
  sorry (* Muss sorry wegen idMediumSteps *)

(* Line 14:  Single / {o=i}; *)
lemma idMediumStep_1_0:
  assumes "True"
    shows "spsConcIn  (mediumIn_i null) (idMediumStep (IdMediumState Single ))
         \<sqsubseteq> spsConcOut (mediumOut_o null) (idMediumStep (IdMediumState Single))"
  sorry (* Muss sorry wegen idMediumSteps *)

lemmas idMediumSteps = idMediumStep_0_0 idMediumStep_1_0

end