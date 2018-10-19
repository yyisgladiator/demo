(*
 * DO NOT MODIFY!
 * This file was generated from Fair99Medium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 16, 2018 10:17:27 PM by isartransformer 3.1.0
 *)
theory Fair99MediumAutomaton
  imports MediumDatatype FairMediumStates automat.ndAutomaton automat.ndaComplete automat.ndaTotal

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Function for each transition to allow transition overlap\<close>

fun fair99MediumTransitionH_0_0 :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"fair99MediumTransitionH_0_0 (FairMediumState Single var_counter, (Msg port_i)) =
  (if (var_counter\<noteq>0) then {(FairMediumState Single (var_counter-1), (mediumOut_o null))}
   else {})" |
"fair99MediumTransitionH_0_0 _ = {}"

fun fair99MediumTransitionH_0_1 :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"fair99MediumTransitionH_0_1 (FairMediumState Single var_counter, (Msg port_i)) =
  (if (var_counter=0) then {(FairMediumState Single var_counter, (mediumOut_o (Msg (port_i)))) | var_counter . (var_counter>=0 \<and> var_counter<100)}
   else {})" |
"fair99MediumTransitionH_0_1 _ = {}"

fun fair99MediumTransitionH_1_0 :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"fair99MediumTransitionH_1_0 (FairMediumState Single var_counter, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if (var_counter\<noteq>0) then {(FairMediumState Single (var_counter-1), (mediumOut_o null))}
   else {})" |
"fair99MediumTransitionH_1_0 _ = {}"

fun fair99MediumTransitionH_1_1 :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"fair99MediumTransitionH_1_1 (FairMediumState Single var_counter, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if (var_counter=0) then {(FairMediumState Single var_counter, (mediumOut_o null)) | var_counter . (var_counter>=0 \<and> var_counter<100)}
   else {})" |
"fair99MediumTransitionH_1_1 _ = {}"


section \<open>Automaton definition\<close>

(* Helper that combines all transitions into one function *)
fun fair99MediumTransitionH :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fair99MediumTransitionH input = Rev ((fair99MediumTransitionH_0_0 input) \<union> (fair99MediumTransitionH_0_1 input) \<union> (fair99MediumTransitionH_1_0 input) \<union> (fair99MediumTransitionH_1_1 input))"

(* Transition function *)
definition fair99MediumTransition :: "(FairMediumState \<times> ('e::countable) mediumMessage tsyn sbElem) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fair99MediumTransition = (\<lambda> (s,b). (if (sbeDom b) = mediumDom then fair99MediumTransitionH (s, (mediumElem_get_i b)) else undefined))"

(* Initial states with initial outputs *)
definition fair99MediumInitials :: "(FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fair99MediumInitials = Rev (setflat\<cdot>{{(FairMediumState Single (var_counter::int), (mediumOut_o null)) | var_counter . (var_counter>=0 \<and> var_counter<100)}})"

(* The -potentially partial- automaton *)
lift_definition fair99MediumAutomaton_partial :: "(FairMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" is
"(fair99MediumTransition, fair99MediumInitials, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def mediumRan_def)

(* The final -totalised- automaton *)
definition fair99MediumAutomaton :: "(FairMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" where
"fair99MediumAutomaton = ndaChaosCompletion fair99MediumAutomaton_partial"

(* Stream processing function for each state (handy for step lemmata) *)
definition fair99MediumStep :: "FairMediumState \<Rightarrow> ('e::countable) mediumMessage tsyn SPS" where
"fair99MediumStep = nda_h fair99MediumAutomaton"

(* The final SPS *)
definition fair99MediumSPS :: "('e::countable) mediumMessage tsyn SPS" where
"fair99MediumSPS = nda_H (fair99MediumAutomaton::(FairMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma fair99mediumautomaton_trans[simp]: "ndaTransition\<cdot>fair99MediumAutomaton = chaosTransCompletion fair99MediumTransition"
  apply(simp add: fair99MediumAutomaton_def)
  by(simp add: fair99MediumAutomaton_partial.rep_eq ndaTransition.rep_eq)

lemma fair99mediumautomaton_initialstate[simp]: "ndaInitialState\<cdot>fair99MediumAutomaton = (initCompletion chaosInit_h) fair99MediumInitials"
  apply(simp add: fair99MediumAutomaton_def)
  by(simp add: fair99MediumAutomaton_partial.rep_eq ndaInitialState.rep_eq)

lemma fair99mediumautomaton_dom[simp]: "ndaDom\<cdot>fair99MediumAutomaton = mediumDom"
  apply(simp add: fair99MediumAutomaton_def)
  by(simp add: fair99MediumAutomaton_partial.rep_eq ndaDom.rep_eq)

lemma fair99mediumautomaton_ran[simp]: "ndaRan\<cdot>fair99MediumAutomaton = mediumRan"
  apply(simp add: fair99MediumAutomaton_def)
  by(simp add: fair99MediumAutomaton_partial.rep_eq ndaRan.rep_eq)


section \<open>Consistency\<close>

lemma fair99mediumstep_consistent [simp]: "uspecIsConsistent (fair99MediumStep s)"
  unfolding fair99MediumStep_def
  by(rule nda_consistent, simp_all)

lemma fair99mediumsps_consistent [simp]: "uspecIsConsistent fair99MediumSPS"
  oops


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fair99MediumTransition_0_0:
  assumes "var_counter\<noteq>0"
    shows "inv Rev (fair99MediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i (Msg port_i))))
         \<supseteq> {(FairMediumState Single (var_counter-1), (mediumOut_o null))}"
  using assms by(auto simp add: fair99MediumTransition_def assms)

(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0 && j<100}, o=i}; *)
lemma fair99MediumTransition_0_1:
  assumes "var_counter=0"
    shows "inv Rev (fair99MediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i (Msg port_i))))
         \<supseteq> {(FairMediumState Single var_counter, (mediumOut_o (Msg (port_i)))) | var_counter . (var_counter>=0 \<and> var_counter<100)}"
  using assms by(auto simp add: fair99MediumTransition_def assms)

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fair99MediumTransition_1_0:
  assumes "var_counter\<noteq>0"
    shows "inv Rev (fair99MediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i null)))
         \<supseteq> {(FairMediumState Single (var_counter-1), (mediumOut_o null))}"
  using assms by(auto simp add: fair99MediumTransition_def assms)

(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0 && j<100}, o=i}; *)
lemma fair99MediumTransition_1_1:
  assumes "var_counter=0"
    shows "inv Rev (fair99MediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i null)))
         \<supseteq> {(FairMediumState Single var_counter, (mediumOut_o null)) | var_counter . (var_counter>=0 \<and> var_counter<100)}"
  using assms by(auto simp add: fair99MediumTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma fair99MediumSps2Step: "fair99MediumSPS = ndaConcOutFlatten mediumDom mediumRan (initCompletion chaosInit_h fair99MediumInitials) fair99MediumStep"
  by (simp add: fair99MediumSPS_def fair99MediumStep_def nda_H_def)

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fair99MediumStep_0_0:
  assumes "var_counter\<noteq>0"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (fair99MediumStep (FairMediumState Single var_counter))
         \<sqsubseteq> spsConcOut (mediumOut_o null) (fair99MediumStep (FairMediumState Single (var_counter-1)))"
  sorry (* Muss sorry wegen fair99MediumSteps *)

(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0 && j<100}, o=i}; *)
lemma fair99MediumStep_0_1:
  assumes "var_counter=0"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (fair99MediumStep (FairMediumState Single var_counter))
         \<sqsubseteq> uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o (Msg (port_i))) (fair99MediumStep (FairMediumState Single var_counter)) | var_counter . (var_counter>=0 \<and> var_counter<100)})"
  sorry (* Muss sorry wegen fair99MediumSteps *)

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fair99MediumStep_1_0:
  assumes "var_counter\<noteq>0"
    shows "spsConcIn  (mediumIn_i null) (fair99MediumStep (FairMediumState Single var_counter))
         \<sqsubseteq> spsConcOut (mediumOut_o null) (fair99MediumStep (FairMediumState Single (var_counter-1)))"
  sorry (* Muss sorry wegen fair99MediumSteps *)

(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0 && j<100}, o=i}; *)
lemma fair99MediumStep_1_1:
  assumes "var_counter=0"
    shows "spsConcIn  (mediumIn_i null) (fair99MediumStep (FairMediumState Single var_counter))
         \<sqsubseteq> uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o null) (fair99MediumStep (FairMediumState Single var_counter)) | var_counter . (var_counter>=0 \<and> var_counter<100)})"
  sorry (* Muss sorry wegen fair99MediumSteps *)

lemmas fair99MediumSteps = fair99MediumStep_0_0 fair99MediumStep_0_1 fair99MediumStep_1_0 fair99MediumStep_1_1

end