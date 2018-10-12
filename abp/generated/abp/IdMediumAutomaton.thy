(*
 * DO NOT MODIFY!
 * This file was generated from IdMedium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 12, 2018 3:13:56 PM by isartransformer 2.0.0
 *)
theory IdMediumAutomaton
  imports MediumDatatype IdMediumStates automat.ndAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Automaton definition\<close>

(* Helper that allows us to utilize pattern matching *)
fun idMediumTransitionH :: "(IdMediumState \<times> ('e tsyn)) \<Rightarrow> (IdMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"idMediumTransitionH (IdMediumState Single, (\<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (Rev {(IdMediumState Single, (mediumOut_o (Msg (port_i))))})" |

"idMediumTransitionH (IdMediumState Single, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (Rev {(IdMediumState Single, (mediumOut_o null))})"

(* Transition function *)
definition idMediumTransition :: "(IdMediumState \<times> ('e::countable) mediumMessage tsyn sbElem) \<Rightarrow> (IdMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"idMediumTransition = (\<lambda> (s,b). (if (sbeDom b) = mediumDom then idMediumTransitionH (s, (mediumElem_get_i b)) else undefined))"

(* Initial states with initial outputs *)
definition idMediumInitials :: "(IdMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"idMediumInitials = Rev (setflat\<cdot>{{(IdMediumState Single , (mediumOut_o null))}})"

(* The final automaton *)
lift_definition idMediumAutomaton :: "(IdMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" is
"(idMediumTransition, idMediumInitials, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def mediumRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition idMediumStep :: "IdMediumState \<Rightarrow> ('e::countable) mediumMessage tsyn SPS" where
"idMediumStep = nda_h idMediumAutomaton"

(* The final SPS *)
definition idMediumSPS :: "('e::countable) mediumMessage tsyn SPS" where
"idMediumSPS = nda_H (idMediumAutomaton::(IdMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma idmediumautomaton_trans[simp]: "ndaTransition\<cdot>idMediumAutomaton = idMediumTransition"
  by(simp add: idMediumAutomaton.rep_eq ndaTransition.rep_eq)

lemma idmediumautomaton_initialstate[simp]: "ndaInitialState\<cdot>idMediumAutomaton = idMediumInitials"
  by(simp add: idMediumAutomaton.rep_eq ndaInitialState.rep_eq)

lemma idmediumautomaton_dom[simp]: "ndaDom\<cdot>idMediumAutomaton = mediumDom"
  by(simp add: idMediumAutomaton.rep_eq ndaDom.rep_eq)

lemma idmediumautomaton_ran[simp]: "ndaRan\<cdot>idMediumAutomaton = mediumRan"
  by(simp add: idMediumAutomaton.rep_eq ndaRan.rep_eq)


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 14:  Single / {o=i}; *)
lemma idMediumTransition_0_0:
  assumes "True"
    shows "idMediumTransition ((IdMediumState Single ), (mediumElemIn_i (Msg port_i)))
         = (Rev {(IdMediumState Single, (mediumOut_o (Msg (port_i))))})"
  using assms by(auto simp add: idMediumTransition_def assms)

(* Line 14:  Single / {o=i}; *)
lemma idMediumTransition_1_0:
  assumes "True"
    shows "idMediumTransition ((IdMediumState Single ), (mediumElemIn_i null))
         = (Rev {(IdMediumState Single, (mediumOut_o null))})"
  using assms by(auto simp add: idMediumTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma idMediumSps2Step: "idMediumSPS = spsConcOut (mediumOut_o null) (idMediumStep (IdMediumState Single ))"
  sorry

(* Line 14:  Single / {o=i}; *)
lemma idMediumStep_0_0:
  assumes "True"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (idMediumStep (IdMediumState Single ))
         = spsConcOut (mediumOut_o (Msg (port_i))) (idMediumStep (IdMediumState Single))"
  oops

(* Line 14:  Single / {o=i}; *)
lemma idMediumStep_1_0:
  assumes "True"
    shows "spsConcIn  (mediumIn_i null) (idMediumStep (IdMediumState Single ))
         = spsConcOut (mediumOut_o null) (idMediumStep (IdMediumState Single))"
  oops


end