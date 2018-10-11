(*
 * DO NOT MODIFY!
 * This file was generated from UnfairMedium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 2.0.0
 *)
theory UnfairMediumAutomaton
  imports UnfairMediumDatatype automat.ndAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Automaton definition\<close>

(* These are the actual states from MAA *)
datatype UnfairMediumSubstate = Single

(* And these have also the variables *)
datatype UnfairMediumState = UnfairMediumState UnfairMediumSubstate (* coin = *) "nat"

(* Function to get the substate *)
fun getUnfairMediumSubState :: "UnfairMediumState \<Rightarrow> UnfairMediumSubstate" where
"getUnfairMediumSubState (UnfairMediumState s _) = s"

(* Functions to get the variables *)
fun getCoin :: "UnfairMediumState \<Rightarrow> nat" where
"getCoin (UnfairMediumState _ var_coin) = var_coin"

(* Helper that allows us to utilize pattern matching *)
fun unfairMediumTransitionH :: "(UnfairMediumState \<times> ('e tsyn)) \<Rightarrow> (UnfairMediumState \<times> ('e::countable) unfairMediumMessage tsyn SB) set rev" where
"unfairMediumTransitionH (UnfairMediumState Single var_coin, (\<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if(var_coin=0) then (Rev {(UnfairMediumState Single var_coin, (unfairMediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})
   else if(var_coin=1) then (Rev {(UnfairMediumState Single var_coin, (unfairMediumOut_o (Msg (port_i)))) | var_coin . (var_coin = 0 \<or> var_coin = 1)})
   else (Rev {(UnfairMediumState Single var_coin, (unfairMediumOut_o null))}))" |

"unfairMediumTransitionH (UnfairMediumState Single var_coin, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if(var_coin=0) then (Rev {(UnfairMediumState Single var_coin, (unfairMediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})
   else if(var_coin=1) then (Rev {(UnfairMediumState Single var_coin, (unfairMediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})
   else (Rev {(UnfairMediumState Single var_coin, (unfairMediumOut_o null))}))"

(* Transition function *)
definition unfairMediumTransition :: "(UnfairMediumState \<times> ('e::countable) unfairMediumMessage tsyn sbElem) \<Rightarrow> (UnfairMediumState \<times> ('e::countable) unfairMediumMessage tsyn SB) set rev" where
"unfairMediumTransition = (\<lambda> (s,b). (if (sbeDom b) = unfairMediumDom then unfairMediumTransitionH (s, (unfairMediumElem_get_i b)) else undefined))"

(* Initial states with initial outputs *)
definition unfairMediumInitials :: "(UnfairMediumState \<times> ('e::countable) unfairMediumMessage tsyn SB) set rev" where
"unfairMediumInitials = Rev (setflat\<cdot>{{(UnfairMediumState Single (var_coin::nat), (unfairMediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)}})"

(* The final automaton *)
lift_definition unfairMediumAutomaton :: "(UnfairMediumState, ('e::countable) unfairMediumMessage tsyn) ndAutomaton" is
"(unfairMediumTransition, unfairMediumInitials, Discr unfairMediumDom, Discr unfairMediumRan)"
  by (simp add: unfairMediumDom_def unfairMediumRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition unfairMediumStep :: "UnfairMediumState \<Rightarrow> ('e::countable) unfairMediumMessage tsyn SPS" where
"unfairMediumStep = nda_h unfairMediumAutomaton"

(* The final SPS *)
definition unfairMediumSPS :: "('e::countable) unfairMediumMessage tsyn SPS" where
"unfairMediumSPS = nda_H (unfairMediumAutomaton::(UnfairMediumState, ('e::countable) unfairMediumMessage tsyn) ndAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma unfairmediumautomaton_trans[simp]: "ndaTransition\<cdot>unfairMediumAutomaton = unfairMediumTransition"
  by(simp add: unfairMediumAutomaton.rep_eq ndaTransition.rep_eq)

lemma unfairmediumautomaton_initialstate[simp]: "ndaInitialState\<cdot>unfairMediumAutomaton = unfairMediumInitials"
  by(simp add: unfairMediumAutomaton.rep_eq ndaInitialState.rep_eq)

lemma unfairmediumautomaton_dom[simp]: "ndaDom\<cdot>unfairMediumAutomaton = unfairMediumDom"
  by(simp add: unfairMediumAutomaton.rep_eq ndaDom.rep_eq)

lemma unfairmediumautomaton_ran[simp]: "ndaRan\<cdot>unfairMediumAutomaton = unfairMediumRan"
  by(simp add: unfairMediumAutomaton.rep_eq ndaRan.rep_eq)


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 15:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma unfairMediumTransition_0_0:
  assumes "var_coin=0"
    shows "unfairMediumTransition ((UnfairMediumState Single var_coin), (unfairMediumElemIn_i (Msg port_i)))
         = (Rev {(UnfairMediumState Single var_coin, (unfairMediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  using assms by(auto simp add: unfairMediumTransition_def assms)

(* Line 16:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma unfairMediumTransition_0_1:
  assumes "var_coin=1"
    shows "unfairMediumTransition ((UnfairMediumState Single var_coin), (unfairMediumElemIn_i (Msg port_i)))
         = (Rev {(UnfairMediumState Single var_coin, (unfairMediumOut_o (Msg (port_i)))) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  using assms by(auto simp add: unfairMediumTransition_def assms)

(* Line 15:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma unfairMediumTransition_1_0:
  assumes "var_coin=0"
    shows "unfairMediumTransition ((UnfairMediumState Single var_coin), (unfairMediumElemIn_i null))
         = (Rev {(UnfairMediumState Single var_coin, (unfairMediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  using assms by(auto simp add: unfairMediumTransition_def assms)

(* Line 16:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma unfairMediumTransition_1_1:
  assumes "var_coin=1"
    shows "unfairMediumTransition ((UnfairMediumState Single var_coin), (unfairMediumElemIn_i null))
         = (Rev {(UnfairMediumState Single var_coin, (unfairMediumOut_o null)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  using assms by(auto simp add: unfairMediumTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma unfairMediumSps2Step: "unfairMediumSPS = uspecFlatten unfairMediumDom unfairMediumRan
    (Rev {spsConcOut (unfairMediumOut_o null) (unfairMediumStep (UnfairMediumState Single (var_coin::nat))) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  sorry

(* Line 15:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma unfairMediumStep_0_0:
  assumes "var_coin=0"
    shows "spsConcIn  (unfairMediumIn_i (Msg port_i)) (unfairMediumStep (UnfairMediumState Single var_coin))
         = uspecFlatten unfairMediumDom unfairMediumRan
          (Rev {spsConcOut (unfairMediumOut_o null) (unfairMediumStep (UnfairMediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  oops

(* Line 16:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma unfairMediumStep_0_1:
  assumes "var_coin=1"
    shows "spsConcIn  (unfairMediumIn_i (Msg port_i)) (unfairMediumStep (UnfairMediumState Single var_coin))
         = uspecFlatten unfairMediumDom unfairMediumRan
          (Rev {spsConcOut (unfairMediumOut_o (Msg (port_i))) (unfairMediumStep (UnfairMediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  oops

(* Line 15:  Single [coin==0] / {coin=alt{0,1}}; *)
lemma unfairMediumStep_1_0:
  assumes "var_coin=0"
    shows "spsConcIn  (unfairMediumIn_i null) (unfairMediumStep (UnfairMediumState Single var_coin))
         = uspecFlatten unfairMediumDom unfairMediumRan
          (Rev {spsConcOut (unfairMediumOut_o null) (unfairMediumStep (UnfairMediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  oops

(* Line 16:  Single [coin==1] / {coin=alt{0,1}, o=i}; *)
lemma unfairMediumStep_1_1:
  assumes "var_coin=1"
    shows "spsConcIn  (unfairMediumIn_i null) (unfairMediumStep (UnfairMediumState Single var_coin))
         = uspecFlatten unfairMediumDom unfairMediumRan
          (Rev {spsConcOut (unfairMediumOut_o null) (unfairMediumStep (UnfairMediumState Single var_coin)) | var_coin . (var_coin = 0 \<or> var_coin = 1)})"
  oops


end