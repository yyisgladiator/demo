(*
 * DO NOT MODIFY!
 * This file was generated from Medium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 1.0.0
 *)
theory MediumAutomaton
  imports MediumDatatype automat.ndAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Automaton definition\<close>

(* These are the actual states from MAA *)
datatype MediumSubstate = Single

(* And these have also the variables *)
datatype MediumState = MediumState MediumSubstate (* c = *) "nat"

(* Function to get the substate *)
fun getMediumSubState :: "MediumState \<Rightarrow> MediumSubstate" where
"getMediumSubState (MediumState s _) = s"

(* Functions to get the variables *)
fun getC :: "MediumState \<Rightarrow> nat" where
"getC (MediumState _ var_c) = var_c"

(* Helper that allows us to utilize pattern matching *)
fun mediumTransitionH :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumTransitionH (MediumState Single var_c, (\<^cancel>\<open>ar\<mapsto>\<close>Msg port_ar)) =
  (if(var_c>0) then (Rev {(MediumState Single (var_c-1), (mediumOut_as null))})
   else if(var_c=0) then (Rev {(MediumState Single var_c, (mediumOut_as (Msg (port_ar)))) | var_c . (True)})
   else (Rev {(MediumState Single var_c, (mediumOut_as null))}))" |

"mediumTransitionH (MediumState Single var_c, (\<^cancel>\<open>ar\<mapsto>\<close>null)) =
  (if(var_c>0) then (Rev {(MediumState Single (var_c-1), (mediumOut_as null))})
   else if(var_c=0) then (Rev {(MediumState Single var_c, (mediumOut_as null)) | var_c . (True)})
   else (Rev {(MediumState Single var_c, (mediumOut_as null))}))"

(* Transition function *)
definition mediumTransition :: "(MediumState \<times> ('e::countable) mediumMessage tsyn sbElem) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumTransition = (\<lambda> (s,b). (if (sbeDom b) = mediumDom then mediumTransitionH (s, (mediumElem_get_ar b)) else undefined))"

(* Initial states with initial outputs *)
definition mediumInitials :: "(MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumInitials = Rev (setflat\<cdot>{{(MediumState Single (var_c::nat), (mediumOut_as null)) | var_c . (True)}})"

(* The final automaton *)
lift_definition mediumAutomaton :: "(MediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" is
"(mediumTransition, mediumInitials, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def mediumRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition mediumStep :: "MediumState \<Rightarrow> ('e::countable) mediumMessage tsyn SPS" where
"mediumStep = nda_h mediumAutomaton"

(* The final SPS *)
definition mediumSPS :: "('e::countable) mediumMessage tsyn SPS" where
"mediumSPS = nda_H (mediumAutomaton::(MediumState, ('e::countable) mediumMessage tsyn) ndAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma mediumautomaton_trans[simp]: "ndaTransition\<cdot>mediumAutomaton = mediumTransition"
  by(simp add: mediumAutomaton.rep_eq ndaTransition.rep_eq)

lemma mediumautomaton_initialstate[simp]: "ndaInitialState\<cdot>mediumAutomaton = mediumInitials"
  by(simp add: mediumAutomaton.rep_eq ndaInitialState.rep_eq)

lemma mediumautomaton_dom[simp]: "ndaDom\<cdot>mediumAutomaton = mediumDom"
  by(simp add: mediumAutomaton.rep_eq ndaDom.rep_eq)

lemma mediumautomaton_ran[simp]: "ndaRan\<cdot>mediumAutomaton = mediumRan"
  by(simp add: mediumAutomaton.rep_eq ndaRan.rep_eq)


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 15:  Single [c>0] / {c = c-1}; *)
lemma mediumTransition_0_0:
  assumes "var_c>0"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar (Msg port_ar)))
         = (Rev {(MediumState Single (var_c-1), (mediumOut_as null))})"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 16:  Single [c==0] / {c = rand {i. True}, as = ar}; *)
lemma mediumTransition_0_1:
  assumes "var_c=0"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar (Msg port_ar)))
         = (Rev {(MediumState Single var_c, (mediumOut_as (Msg (port_ar)))) | var_c . (True)})"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 15:  Single [c>0] / {c = c-1}; *)
lemma mediumTransition_1_0:
  assumes "var_c>0"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar null))
         = (Rev {(MediumState Single (var_c-1), (mediumOut_as null))})"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 16:  Single [c==0] / {c = rand {i. True}, as = ar}; *)
lemma mediumTransition_1_1:
  assumes "var_c=0"
    shows "mediumTransition ((MediumState Single var_c), (mediumElemIn_ar null))
         = (Rev {(MediumState Single var_c, (mediumOut_as null)) | var_c . (True)})"
  using assms by(auto simp add: mediumTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma mediumSps2Step: "mediumSPS = uspecFlatten mediumDom mediumRan
    (Rev {spsConcOut (mediumOut_as null) (mediumStep (MediumState Single (var_c::nat))) | var_c . (True)})"
  sorry

(* Line 15:  Single [c>0] / {c = c-1}; *)
lemma mediumStep_0_0:
  assumes "var_c>0"
    shows "spsConcIn  (mediumIn_ar (Msg port_ar)) (mediumStep (MediumState Single var_c))
         = spsConcOut (mediumOut_as null) (mediumStep (MediumState Single (var_c-1)))"
  oops

(* Line 16:  Single [c==0] / {c = rand {i. True}, as = ar}; *)
lemma mediumStep_0_1:
  assumes "var_c=0"
    shows "spsConcIn  (mediumIn_ar (Msg port_ar)) (mediumStep (MediumState Single var_c))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_as (Msg (port_ar))) (mediumStep (MediumState Single var_c)) | var_c . (True)})"
  oops

(* Line 15:  Single [c>0] / {c = c-1}; *)
lemma mediumStep_1_0:
  assumes "var_c>0"
    shows "spsConcIn  (mediumIn_ar null) (mediumStep (MediumState Single var_c))
         = spsConcOut (mediumOut_as null) (mediumStep (MediumState Single (var_c-1)))"
  oops

(* Line 16:  Single [c==0] / {c = rand {i. True}, as = ar}; *)
lemma mediumStep_1_1:
  assumes "var_c=0"
    shows "spsConcIn  (mediumIn_ar null) (mediumStep (MediumState Single var_c))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_as null) (mediumStep (MediumState Single var_c)) | var_c . (True)})"
  oops


end