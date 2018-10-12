(*
 * DO NOT MODIFY!
 * This file was generated from FairMedium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 12, 2018 1:15:31 PM by isartransformer 2.0.0
 *)
theory FairMediumAutomaton
  imports MediumDatatype FairMediumStates automat.ndAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Automaton definition\<close>

(* Helper that allows us to utilize pattern matching *)
fun fairMediumTransitionH :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fairMediumTransitionH (FairMediumState Single var_counter, (\<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if(var_counter\<noteq>0) then (Rev {(FairMediumState Single (var_counter-1), (mediumOut_o null))})
   else if(var_counter=0) then (Rev {(FairMediumState Single var_counter, (mediumOut_o (Msg (port_i)))) | var_counter . (True)})
   else (Rev {(FairMediumState Single var_counter, (mediumOut_o null))}))" |

"fairMediumTransitionH (FairMediumState Single var_counter, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if(var_counter\<noteq>0) then (Rev {(FairMediumState Single (var_counter-1), (mediumOut_o null))})
   else if(var_counter=0) then (Rev {(FairMediumState Single var_counter, (mediumOut_o null)) | var_counter . (True)})
   else (Rev {(FairMediumState Single var_counter, (mediumOut_o null))}))"

(* Transition function *)
definition fairMediumTransition :: "(FairMediumState \<times> ('e::countable) mediumMessage tsyn sbElem) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fairMediumTransition = (\<lambda> (s,b). (if (sbeDom b) = mediumDom then fairMediumTransitionH (s, (mediumElem_get_i b)) else undefined))"

(* Initial states with initial outputs *)
definition fairMediumInitials :: "(FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fairMediumInitials = Rev (setflat\<cdot>{{(FairMediumState Single (var_counter::nat), (mediumOut_o null)) | var_counter . (True)}})"

(* The final automaton *)
lift_definition fairMediumAutomaton :: "(FairMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" is
"(fairMediumTransition, fairMediumInitials, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def mediumRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition fairMediumStep :: "FairMediumState \<Rightarrow> ('e::countable) mediumMessage tsyn SPS" where
"fairMediumStep = nda_h fairMediumAutomaton"

(* The final SPS *)
definition fairMediumSPS :: "('e::countable) mediumMessage tsyn SPS" where
"fairMediumSPS = nda_H (fairMediumAutomaton::(FairMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma fairmediumautomaton_trans[simp]: "ndaTransition\<cdot>fairMediumAutomaton = fairMediumTransition"
  by(simp add: fairMediumAutomaton.rep_eq ndaTransition.rep_eq)

lemma fairmediumautomaton_initialstate[simp]: "ndaInitialState\<cdot>fairMediumAutomaton = fairMediumInitials"
  by(simp add: fairMediumAutomaton.rep_eq ndaInitialState.rep_eq)

lemma fairmediumautomaton_dom[simp]: "ndaDom\<cdot>fairMediumAutomaton = mediumDom"
  by(simp add: fairMediumAutomaton.rep_eq ndaDom.rep_eq)

lemma fairmediumautomaton_ran[simp]: "ndaRan\<cdot>fairMediumAutomaton = mediumRan"
  by(simp add: fairMediumAutomaton.rep_eq ndaRan.rep_eq)


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fairMediumTransition_0_0:
  assumes "var_counter\<noteq>0"
    shows "fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i (Msg port_i)))
         = (Rev {(FairMediumState Single (var_counter-1), (mediumOut_o null))})"
  using assms by(auto simp add: fairMediumTransition_def assms)

(* Line 16:  Single [counter==0] / {counter=rand{j. True}, o=i}; *)
lemma fairMediumTransition_0_1:
  assumes "var_counter=0"
    shows "fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i (Msg port_i)))
         = (Rev {(FairMediumState Single var_counter, (mediumOut_o (Msg (port_i)))) | var_counter . (True)})"
  using assms by(auto simp add: fairMediumTransition_def assms)

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fairMediumTransition_1_0:
  assumes "var_counter\<noteq>0"
    shows "fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i null))
         = (Rev {(FairMediumState Single (var_counter-1), (mediumOut_o null))})"
  using assms by(auto simp add: fairMediumTransition_def assms)

(* Line 16:  Single [counter==0] / {counter=rand{j. True}, o=i}; *)
lemma fairMediumTransition_1_1:
  assumes "var_counter=0"
    shows "fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i null))
         = (Rev {(FairMediumState Single var_counter, (mediumOut_o null)) | var_counter . (True)})"
  using assms by(auto simp add: fairMediumTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma fairMediumSps2Step: "fairMediumSPS = uspecFlatten mediumDom mediumRan
    (Rev {spsConcOut (mediumOut_o null) (fairMediumStep (FairMediumState Single (var_counter::nat))) | var_counter . (True)})"
  sorry

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fairMediumStep_0_0:
  assumes "var_counter\<noteq>0"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (fairMediumStep (FairMediumState Single var_counter))
         = spsConcOut (mediumOut_o null) (fairMediumStep (FairMediumState Single (var_counter-1)))"
  oops

(* Line 16:  Single [counter==0] / {counter=rand{j. True}, o=i}; *)
lemma fairMediumStep_0_1:
  assumes "var_counter=0"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (fairMediumStep (FairMediumState Single var_counter))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o (Msg (port_i))) (fairMediumStep (FairMediumState Single var_counter)) | var_counter . (True)})"
  oops

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fairMediumStep_1_0:
  assumes "var_counter\<noteq>0"
    shows "spsConcIn  (mediumIn_i null) (fairMediumStep (FairMediumState Single var_counter))
         = spsConcOut (mediumOut_o null) (fairMediumStep (FairMediumState Single (var_counter-1)))"
  oops

(* Line 16:  Single [counter==0] / {counter=rand{j. True}, o=i}; *)
lemma fairMediumStep_1_1:
  assumes "var_counter=0"
    shows "spsConcIn  (mediumIn_i null) (fairMediumStep (FairMediumState Single var_counter))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o null) (fairMediumStep (FairMediumState Single var_counter)) | var_counter . (True)})"
  oops


end