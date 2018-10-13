(*
 * DO NOT MODIFY!
 * This file was generated from Medium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 12, 2018 1:15:32 PM by isartransformer 2.0.0
 *)
theory MediumAutomaton
  imports MediumDatatype MediumStates automat.ndAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Automaton definition\<close>

(* Helper that allows us to utilize pattern matching *)
fun mediumTransitionH :: "(MediumState \<times> ('e tsyn)) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumTransitionH (MediumState Single var_coin, (\<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if(var_coin=0) then (Rev {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})
   else if(var_coin=1) then (Rev {(MediumState Single var_coin, (mediumOut_o (Msg (port_i)))) | var_coin . (var_coin = 0 \<or> var_coin = 1)})
   else (Rev {(MediumState Single var_coin, (mediumOut_o null))}))" |

"mediumTransitionH (MediumState Single var_coin, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if(var_coin=0) then (Rev {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})
   else if(var_coin=1) then (Rev {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})
   else (Rev {(MediumState Single var_coin, (mediumOut_o null))}))"

(* Transition function *)
definition mediumTransition :: "(MediumState \<times> ('e::countable) mediumMessage tsyn sbElem) \<Rightarrow> (MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumTransition = (\<lambda> (s,b). (if (sbeDom b) = mediumDom then mediumTransitionH (s, (mediumElem_get_i b)) else undefined))"

(* Initial states with initial outputs *)
definition mediumInitials :: "(MediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"mediumInitials = Rev (setflat\<cdot>{{(MediumState Single (var_coin::nat), (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)}})"

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

(* Line 16:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma mediumTransition_0_0:
  assumes "var_coin=0"
    shows "mediumTransition ((MediumState Single var_coin), (mediumElemIn_i (Msg port_i)))
         = (Rev {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 17:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma mediumTransition_0_1:
  assumes "var_coin=1"
    shows "mediumTransition ((MediumState Single var_coin), (mediumElemIn_i (Msg port_i)))
         = (Rev {(MediumState Single var_coin, (mediumOut_o (Msg (port_i)))) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 16:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma mediumTransition_1_0:
  assumes "var_coin=0"
    shows "mediumTransition ((MediumState Single var_coin), (mediumElemIn_i null))
         = (Rev {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  using assms by(auto simp add: mediumTransition_def assms)

(* Line 17:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma mediumTransition_1_1:
  assumes "var_coin=1"
    shows "mediumTransition ((MediumState Single var_coin), (mediumElemIn_i null))
         = (Rev {(MediumState Single var_coin, (mediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  using assms by(auto simp add: mediumTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma mediumSps2Step: "mediumSPS = uspecFlatten mediumDom mediumRan
    (Rev {spsConcOut (mediumOut_o null) (mediumStep (MediumState Single (var_coin::nat))) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  sorry

(* Line 16:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma mediumStep_0_0:
  assumes "var_coin=0"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (mediumStep (MediumState Single var_coin))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o null) (mediumStep (MediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  oops

(* Line 17:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma mediumStep_0_1:
  assumes "var_coin=1"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (mediumStep (MediumState Single var_coin))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o (Msg (port_i))) (mediumStep (MediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  oops

(* Line 16:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma mediumStep_1_0:
  assumes "var_coin=0"
    shows "spsConcIn  (mediumIn_i null) (mediumStep (MediumState Single var_coin))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o null) (mediumStep (MediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  oops

(* Line 17:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma mediumStep_1_1:
  assumes "var_coin=1"
    shows "spsConcIn  (mediumIn_i null) (mediumStep (MediumState Single var_coin))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o null) (mediumStep (MediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  oops


end