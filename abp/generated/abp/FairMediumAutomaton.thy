(*
 * DO NOT MODIFY!
 * This file was generated from FairMedium.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 12, 2018 5:31:31 PM by isartransformer 2.0.0
 *)
theory FairMediumAutomaton
  imports MediumDatatype FairMediumStates automat.ndAutomaton automat.ndaComplete automat.ndaTotal

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Automaton definition\<close>

(* Helper that allows us to utilize pattern matching *)
fun fairMediumTransitionH :: "(FairMediumState \<times> ('e tsyn)) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fairMediumTransitionH (FairMediumState Single var_counter, (\<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if(var_counter\<noteq>0) then (Rev {(FairMediumState Single (var_counter-1), (mediumOut_o null))})
   else if(var_counter=0) then (Rev {(FairMediumState Single var_counter, (mediumOut_o (Msg (port_i)))) | var_counter . (var_counter>=0)})
   else (Rev {(FairMediumState Single var_counter, (mediumOut_o null))}))" |

"fairMediumTransitionH (FairMediumState Single var_counter, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if(var_counter\<noteq>0) then (Rev {(FairMediumState Single (var_counter-1), (mediumOut_o null))})
   else if(var_counter=0) then (Rev {(FairMediumState Single var_counter, (mediumOut_o null)) | var_counter . (var_counter>=0)})
   else (Rev {(FairMediumState Single var_counter, (mediumOut_o null))}))"

(* Transition function *)
definition fairMediumTransition :: "(FairMediumState \<times> ('e::countable) mediumMessage tsyn sbElem) \<Rightarrow> (FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fairMediumTransition = (\<lambda> (s,b). (if (sbeDom b) = mediumDom then fairMediumTransitionH (s, (mediumElem_get_i b)) else undefined))"

(* Initial states with initial outputs *)
(* SWS: Why setflat? *)
definition fairMediumInitials :: "(FairMediumState \<times> ('e::countable) mediumMessage tsyn SB) set rev" where
"fairMediumInitials = Rev ({(FairMediumState Single (var_counter::nat), (mediumOut_o null)) | var_counter . (var_counter>=0)})"

(* The final automaton *)
lift_definition fairMediumAutomaton_incomplete :: "(FairMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" is
"(fairMediumTransition, fairMediumInitials, Discr mediumDom, Discr mediumRan)"
  by (simp add: mediumDom_def mediumRan_def)

(* SWS: Erstmal nur completion-chaos. Der rest läuft noch nicht. 
   Soll aber so ähnlich aussehen, die function heißt dann "ndaErrorCompletion" *)
definition fairMediumAutomaton :: "(FairMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton" where
"fairMediumAutomaton = ndaChaosCompletion fairMediumAutomaton_incomplete"
                             

(* Stream processing function for each state (handy for step lemmata) *)
definition fairMediumStep :: "FairMediumState \<Rightarrow> ('e::countable) mediumMessage tsyn SPS" where
"fairMediumStep = nda_h fairMediumAutomaton"

(* The final SPS *)
definition fairMediumSPS :: "('e::countable) mediumMessage tsyn SPS" where
"fairMediumSPS = nda_H (fairMediumAutomaton::(FairMediumState, ('e::countable) mediumMessage tsyn) ndAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma fairmediumautomaton_trans[simp]: "ndaTransition\<cdot>fairMediumAutomaton = chaosTransCompletion fairMediumTransition"
  apply(simp add: fairMediumAutomaton_def)
  by(simp add: ndaTransition.rep_eq fairMediumAutomaton_incomplete.rep_eq )

lemma fairmediumautomaton_initialstate[simp]: "ndaInitialState\<cdot>fairMediumAutomaton = (initCompletion chaosInit_h) fairMediumInitials"
  apply(simp add: fairMediumAutomaton_def)
  by(simp add: ndaInitialState.rep_eq fairMediumAutomaton_incomplete.rep_eq)

lemma fairmediumautomaton_dom[simp]: "ndaDom\<cdot>fairMediumAutomaton = mediumDom"
  apply(simp add: fairMediumAutomaton_def)
  by(simp add: ndaDom.rep_eq fairMediumAutomaton_incomplete.rep_eq)

lemma fairmediumautomaton_ran[simp]: "ndaRan\<cdot>fairMediumAutomaton = mediumRan"
  apply(simp add: fairMediumAutomaton_def)
  by(simp add: ndaRan.rep_eq fairMediumAutomaton_incomplete.rep_eq)


section \<open>Consistent\<close>

lemma fairmediumstep_consistent [simp]:  "uspecIsConsistent (fairMediumStep s)"
  unfolding fairMediumStep_def
  by(rule nda_consistent, simp_all)

lemma fairmedium_consistent [simp]:  "uspecIsConsistent fairMediumSPS"
  oops  (* ToDo *)


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fairMediumTransition_0_0[simp]:
  assumes "var_counter\<noteq>0"
    shows "fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i (Msg port_i)))
         = (Rev {(FairMediumState Single (var_counter-1), (mediumOut_o null))})"
  using assms by(auto simp add: fairMediumTransition_def assms)

(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0}, o=i}; *)
lemma fairMediumTransition_0_1[simp]:
  assumes "var_counter=0"
    shows "fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i (Msg port_i)))
         = (Rev {(FairMediumState Single var_counter, (mediumOut_o (Msg (port_i)))) | var_counter . (var_counter>=0)})"
  using assms by(auto simp add: fairMediumTransition_def assms)

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fairMediumTransition_1_0:
  assumes "var_counter\<noteq>0"
    shows "fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i null))
         = (Rev {(FairMediumState Single (var_counter-1), (mediumOut_o null))})"
  using assms by(auto simp add: fairMediumTransition_def assms)

(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0}, o=i}; *)
lemma fairMediumTransition_1_1:
  assumes "var_counter=0"
    shows "fairMediumTransition ((FairMediumState Single var_counter), (mediumElemIn_i null))
         = (Rev {(FairMediumState Single var_counter, (mediumOut_o null)) | var_counter . (var_counter>=0)})"
  using assms by(auto simp add: fairMediumTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma fairMediumSps2Step: "fairMediumSPS = ndaConcOutFlatten mediumDom mediumRan (initCompletion chaosInit_h fairMediumInitials) fairMediumStep"
  by (simp add: fairMediumSPS_def fairMediumStep_def nda_H_def)

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)

(* SWS: So sollen erstmal alle steps aussehen. Die form klappt für alle *)
(* Für die deterministischen steps kann man noch eine einfachere form generieren, ohne "ndaConcOutFlatten" *)
lemma fairMediumStep_0_0:
  assumes "var_counter\<noteq>0"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (fairMediumStep (FairMediumState Single var_counter))
         = ndaConcOutFlatten mediumDom mediumRan (initCompletion (Rev UNIV) (Rev {(FairMediumState Single (var_counter - 1), mediumOut_o -)})) fairMediumStep"
  unfolding fairMediumStep_def mediumIn_i_def
  apply(subst nda_h_I, simp_all)
   apply (metis fairMediumStep_def fairmediumstep_consistent)
  by(simp add: assms transCompletion_def chaosTrans_h_def)


(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0}, o=i}; *)
lemma fairMediumStep_0_1:
  assumes "var_counter=0"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (fairMediumStep (FairMediumState Single var_counter))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o (Msg (port_i))) (fairMediumStep (FairMediumState Single var_counter)) | var_counter . (var_counter>=0)})"
  oops

(* Line 15:  Single [counter!=0] / {counter=counter-1}; *)
lemma fairMediumStep_1_0:
  assumes "var_counter\<noteq>0"
    shows "spsConcIn  (mediumIn_i null) (fairMediumStep (FairMediumState Single var_counter))
         = spsConcOut (mediumOut_o null) (fairMediumStep (FairMediumState Single (var_counter-1)))"
  oops

(* Line 16:  Single [counter==0] / {counter=rand{j. j>=0}, o=i}; *)
lemma fairMediumStep_1_1:
  assumes "var_counter=0"
    shows "spsConcIn  (mediumIn_i null) (fairMediumStep (FairMediumState Single var_counter))
         = uspecFlatten mediumDom mediumRan
          (Rev {spsConcOut (mediumOut_o null) (fairMediumStep (FairMediumState Single var_counter)) | var_counter . (var_counter>=0)})"
  oops





(* SWS: Example for a deterministic step. ONLY works for deterministic steps *)
lemma fairMediumStep_det_0_0:
  assumes "var_counter\<noteq>0"
    shows "spsConcIn  (mediumIn_i (Msg port_i)) (fairMediumStep (FairMediumState Single   var_counter))
         = spsConcOut (mediumOut_o -)           (fairMediumStep (FairMediumState Single (var_counter - 1)))"
  sorry

end