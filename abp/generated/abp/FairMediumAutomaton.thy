(*
 * DO NOT MODIFY!
 * This file was generated from FairMedium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 16, 2018 10:17:27 PM by isartransformer 3.1.0
 *)
theory FairMediumAutomaton
  imports MediumDatatype FairMediumStates automat.ndAutomaton automat.ndaComplete automat.ndaTotal

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Function for each transition to allow transition overlap\<close>

fun fairMediumTransitionH_0_0 :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"fairMediumTransitionH_0_0 (FairMediumState Single var_counter, (Msg port_i)) =
  (if (var_counter\<noteq>0) then {(FairMediumState Single (var_counter-1), (mediumOut_o null))}
   else {})" |
"fairMediumTransitionH_0_0 _ = {}"

fun fairMediumTransitionH_0_1 :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"fairMediumTransitionH_0_1 (FairMediumState Single var_counter, (Msg port_i)) =
  (if (var_counter=0) then {(FairMediumState Single var_counter, (mediumOut_o (Msg (port_i)))) | var_counter . (var_counter>=0)}
   else {})" |
"fairMediumTransitionH_0_1 _ = {}"

fun fairMediumTransitionH_1_0 :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"fairMediumTransitionH_1_0 (FairMediumState Single var_counter, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if (var_counter\<noteq>0) then {(FairMediumState Single (var_counter-1), (mediumOut_o null))}
   else {})" |
"fairMediumTransitionH_1_0 _ = {}"

fun fairMediumTransitionH_1_1 :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set" where
"fairMediumTransitionH_1_1 (FairMediumState Single var_counter, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if (var_counter=0) then {(FairMediumState Single var_counter, (mediumOut_o null)) | var_counter . (var_counter>=0)}
   else {})" |
"fairMediumTransitionH_1_1 _ = {}"


section \<open>Automaton definition\<close>

(* Helper that combines all transitions into one function *)
fun fairMediumTransitionH :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fairMediumTransitionH input = Rev ((fairMediumTransitionH_0_0 input) \<union> (fairMediumTransitionH_0_1 input) \<union> (fairMediumTransitionH_1_0 input) \<union> (fairMediumTransitionH_1_1 input))"

(* Transition function *)
definition fairMediumTransition :: "(FairMediumState \<times> ('e::countable) mediumMessage tsyn sbElem) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fairMediumTransition = (\<lambda> (s,b). (if (sbeDom b) = mediumDom then fairMediumTransitionH (s, (mediumElem_get_i b)) else undefined))"

(* Initial states with initial outputs *)
definition fairMediumInitials :: "(FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fairMediumInitials = Rev (setflat\<cdot>{{(FairMediumState Single (var_counter::int), (mediumOut_o null)) | var_counter . (var_counter>=0)}})"

(* The -potentially partial- automaton *)
lift_definition fairMediumAutomaton_partial :: "(FairMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" is
"(fairMediumTransition, fairMediumInitials, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def mediumRan_def)

(* The final -totalised- automaton *)
definition fairMediumAutomaton :: "(FairMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" where
"fairMediumAutomaton = ndaChaosCompletion fairMediumAutomaton_partial"

(* Stream processing function for each state (handy for step lemmata) *)
definition fairMediumStep :: "FairMediumState \<Rightarrow> ('e::countable) mediumMessage tsyn SPS" where
"fairMediumStep = nda_h fairMediumAutomaton"

(* The final SPS *)
definition fairMediumSPS :: "('e::countable) mediumMessage tsyn SPS" where
"fairMediumSPS = nda_H (fairMediumAutomaton::(FairMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma fairmediumautomaton_trans[simp]: "ndaTransition\<cdot>fairMediumAutomaton = chaosTransCompletion fairMediumTransition"
  apply(simp add: fairMediumAutomaton_def)
  by(simp add: fairMediumAutomaton_partial.rep_eq ndaTransition.rep_eq)

lemma fairmediumautomaton_initialstate[simp]: "ndaInitialState\<cdot>fairMediumAutomaton = (initCompletion chaosInit_h) fairMediumInitials"
  apply(simp add: fairMediumAutomaton_def)
  by(simp add: fairMediumAutomaton_partial.rep_eq ndaInitialState.rep_eq)

lemma fairmediumautomaton_dom[simp]: "ndaDom\<cdot>fairMediumAutomaton = mediumDom"
  apply(simp add: fairMediumAutomaton_def)
  by(simp add: fairMediumAutomaton_partial.rep_eq ndaDom.rep_eq)

lemma fairmediumautomaton_ran[simp]: "ndaRan\<cdot>fairMediumAutomaton = mediumRan"
  apply(simp add: fairMediumAutomaton_def)
  by(simp add: fairMediumAutomaton_partial.rep_eq ndaRan.rep_eq)


section \<open>Consistency\<close>

lemma fairmediumstep_consistent [simp]: "uspecIsConsistent (fairMediumStep s)"
  unfolding fairMediumStep_def
  by(rule nda_consistent, simp_all)

lemma fairmediumsps_consistent [simp]: "uspecIsConsistent fairMediumSPS"
  oops


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fairMediumTransition_0_0:
  assumes "var_counter\<noteq>0"
    shows "inv Rev (fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i (Msg port_i))))
         \<supseteq> {(FairMediumState Single (var_counter-1), (mediumOut_o null))}"
  using assms by(auto simp add: fairMediumTransition_def assms)

(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0}, o=i}; *)
lemma fairMediumTransition_0_1:
  assumes "var_counter=0"
    shows "inv Rev (fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i (Msg port_i))))
         \<supseteq> {(FairMediumState Single var_counter, (mediumOut_o (Msg (port_i)))) | var_counter . (var_counter>=0)}"
  using assms by(auto simp add: fairMediumTransition_def assms)

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fairMediumTransition_1_0:
  assumes "var_counter\<noteq>0"
    shows "inv Rev (fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i null)))
         \<supseteq> {(FairMediumState Single (var_counter-1), (mediumOut_o null))}"
  using assms by(auto simp add: fairMediumTransition_def assms)

(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0}, o=i}; *)
lemma fairMediumTransition_1_1:
  assumes "var_counter=0"
    shows "inv Rev (fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i null)))
         \<supseteq> {(FairMediumState Single var_counter, (mediumOut_o null)) | var_counter . (var_counter>=0)}"
  using assms by(auto simp add: fairMediumTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma fairMediumSps2Step: "fairMediumSPS = ndaConcOutFlatten mediumDom mediumRan (initCompletion chaosInit_h fairMediumInitials) fairMediumStep"
  by (simp add: fairMediumSPS_def fairMediumStep_def nda_H_def)

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fairMediumStep_0_0:
  assumes "var_counter\<noteq>0"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (fairMediumStep (FairMediumState Single var_counter))
         \<sqsubseteq> spsConcOut (mediumOut_o null) (fairMediumStep (FairMediumState Single (var_counter-1)))"
  sorry (* Muss sorry wegen fairMediumSteps *)

(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0}, o=i}; *)
lemma fairMediumStep_0_1:
  assumes "var_counter=0"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (fairMediumStep (FairMediumState Single var_counter))
         \<sqsubseteq> uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o (Msg (port_i))) (fairMediumStep (FairMediumState Single var_counter)) | var_counter . (var_counter>=0)})"
  sorry (* Muss sorry wegen fairMediumSteps *)

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fairMediumStep_1_0:
  assumes "var_counter\<noteq>0"
    shows "spsConcIn  (mediumIn_i null) (fairMediumStep (FairMediumState Single var_counter))
         \<sqsubseteq> spsConcOut (mediumOut_o null) (fairMediumStep (FairMediumState Single (var_counter-1)))"
  sorry (* Muss sorry wegen fairMediumSteps *)

(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0}, o=i}; *)
lemma fairMediumStep_1_1:
  assumes "var_counter=0"
    shows "spsConcIn  (mediumIn_i null) (fairMediumStep (FairMediumState Single var_counter))
         \<sqsubseteq> uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o null) (fairMediumStep (FairMediumState Single var_counter)) | var_counter . (var_counter>=0)})"
  sorry (* Muss sorry wegen fairMediumSteps *)

lemmas fairMediumSteps = fairMediumStep_0_0 fairMediumStep_0_1 fairMediumStep_1_0 fairMediumStep_1_1

end