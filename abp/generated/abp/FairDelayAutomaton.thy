(*
 * DO NOT MODIFY!
 * This file was generated from FairDelay.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 12, 2018 1:15:32 PM by isartransformer 2.0.0
 *)
theory FairDelayAutomaton
  imports FairDelayDatatype FairDelayStates automat.ndAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Automaton definition\<close>

(* Helper that allows us to utilize pattern matching *)
fun fairDelayTransitionH :: "('e FairDelayState \<times> ('e tsyn)) \<Rightarrow> ('e FairDelayState \<times> ('e::countable) fairDelayMessage tsyn SB) set rev" where
"fairDelayTransitionH (FairDelayState Single var_ctr var_buffer, (\<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if(var_ctr>0) then (Rev {(FairDelayState Single (var_ctr-1) (prepend var_buffer port_i), (fairDelayOut_o null))})
   else if(var_ctr=0 \<and> (size var_buffer)>0) then (Rev {(FairDelayState Single var_ctr (prepend (butlast var_buffer) port_i), (fairDelayOut_o (Msg ((last var_buffer))))) | var_ctr . (True)})
   else if(var_ctr=0 \<and> (size var_buffer)=0) then (Rev {(FairDelayState Single var_ctr var_buffer, (fairDelayOut_o (Msg (port_i)))) | var_ctr . (True)})
   else (Rev {(FairDelayState Single var_ctr var_buffer, (fairDelayOut_o null))}))" |

"fairDelayTransitionH (FairDelayState Single var_ctr var_buffer, (\<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if(var_ctr>0) then (Rev {(FairDelayState Single (var_ctr-1) var_buffer, (fairDelayOut_o null))})
   else if(var_ctr=0 \<and> (size var_buffer)>0) then (Rev {(FairDelayState Single var_ctr (butlast var_buffer), (fairDelayOut_o (Msg ((last var_buffer))))) | var_ctr . (True)})
   else if(var_ctr=0 \<and> (size var_buffer)=0) then (Rev {(FairDelayState Single var_ctr var_buffer, (fairDelayOut_o null)) | var_ctr . (True)})
   else (Rev {(FairDelayState Single var_ctr var_buffer, (fairDelayOut_o null))}))"

(* Transition function *)
definition fairDelayTransition :: "('e FairDelayState \<times> ('e::countable) fairDelayMessage tsyn sbElem) \<Rightarrow> ('e FairDelayState \<times> ('e::countable) fairDelayMessage tsyn SB) set rev" where
"fairDelayTransition = (\<lambda> (s,b). (if (sbeDom b) = fairDelayDom then fairDelayTransitionH (s, (fairDelayElem_get_i b)) else undefined))"

(* Initial states with initial outputs *)
definition fairDelayInitials :: "('e FairDelayState \<times> ('e::countable) fairDelayMessage tsyn SB) set rev" where
"fairDelayInitials = Rev (setflat\<cdot>{{(FairDelayState Single (var_ctr::nat)([] ::'e list), (fairDelayOut_o null)) | var_ctr . (True)}})"

(* The final automaton *)
lift_definition fairDelayAutomaton :: "('e FairDelayState, ('e::countable) fairDelayMessage tsyn) ndAutomaton" is
"(fairDelayTransition, fairDelayInitials, Discr fairDelayDom, Discr fairDelayRan)"
  by (simp add: fairDelayDom_def fairDelayRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition fairDelayStep :: "'e FairDelayState \<Rightarrow> ('e::countable) fairDelayMessage tsyn SPS" where
"fairDelayStep = nda_h fairDelayAutomaton"

(* The final SPS *)
definition fairDelaySPS :: "('e::countable) fairDelayMessage tsyn SPS" where
"fairDelaySPS = nda_H (fairDelayAutomaton::('e FairDelayState, ('e::countable) fairDelayMessage tsyn) ndAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma fairdelayautomaton_trans[simp]: "ndaTransition\<cdot>fairDelayAutomaton = fairDelayTransition"
  by(simp add: fairDelayAutomaton.rep_eq ndaTransition.rep_eq)

lemma fairdelayautomaton_initialstate[simp]: "ndaInitialState\<cdot>fairDelayAutomaton = fairDelayInitials"
  by(simp add: fairDelayAutomaton.rep_eq ndaInitialState.rep_eq)

lemma fairdelayautomaton_dom[simp]: "ndaDom\<cdot>fairDelayAutomaton = fairDelayDom"
  by(simp add: fairDelayAutomaton.rep_eq ndaDom.rep_eq)

lemma fairdelayautomaton_ran[simp]: "ndaRan\<cdot>fairDelayAutomaton = fairDelayRan"
  by(simp add: fairDelayAutomaton.rep_eq ndaRan.rep_eq)


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 19:  Single [ctr>0 && i!=null] / {ctr=ctr-1, buffer=buffer.prepend(i)}; *)
lemma fairDelayTransition_0_0:
  assumes "var_ctr>0"
    shows "fairDelayTransition ((FairDelayState Single var_ctr var_buffer), (fairDelayElemIn_i (Msg port_i)))
         = (Rev {(FairDelayState Single (var_ctr-1) (prepend var_buffer port_i), (fairDelayOut_o null))})"
  using assms by(auto simp add: fairDelayTransition_def assms)

(* Line 22:  Single [ctr==0 && i!=null && buffer.size()>0] / {ctr=rand{j.true}, o=buffer.last(), buffer=buffer.butlast().prepend(i)}; *)
lemma fairDelayTransition_0_1:
  assumes "var_ctr=0 \<and> (size var_buffer)>0"
    shows "fairDelayTransition ((FairDelayState Single var_ctr var_buffer), (fairDelayElemIn_i (Msg port_i)))
         = (Rev {(FairDelayState Single var_ctr (prepend (butlast var_buffer) port_i), (fairDelayOut_o (Msg ((last var_buffer))))) | var_ctr . (True)})"
  using assms by(auto simp add: fairDelayTransition_def assms)

(* Line 25:  Single [ctr==0 && buffer.size()==0] / {ctr=rand{j.true}, o=i}; *)
lemma fairDelayTransition_0_2:
  assumes "var_ctr=0 \<and> (size var_buffer)=0"
    shows "fairDelayTransition ((FairDelayState Single var_ctr var_buffer), (fairDelayElemIn_i (Msg port_i)))
         = (Rev {(FairDelayState Single var_ctr var_buffer, (fairDelayOut_o (Msg (port_i)))) | var_ctr . (True)})"
  using assms by(auto simp add: fairDelayTransition_def assms)

(* Line 20:  Single [ctr>0 && i==null] / {ctr=ctr-1}; *)
lemma fairDelayTransition_1_0:
  assumes "var_ctr>0"
    shows "fairDelayTransition ((FairDelayState Single var_ctr var_buffer), (fairDelayElemIn_i null))
         = (Rev {(FairDelayState Single (var_ctr-1) var_buffer, (fairDelayOut_o null))})"
  using assms by(auto simp add: fairDelayTransition_def assms)

(* Line 23:  Single [ctr==0 && i==null && buffer.size()>0] / {ctr=rand{j.true}, o=buffer.last(), buffer=buffer.butlast()}; *)
lemma fairDelayTransition_1_1:
  assumes "var_ctr=0 \<and> (size var_buffer)>0"
    shows "fairDelayTransition ((FairDelayState Single var_ctr var_buffer), (fairDelayElemIn_i null))
         = (Rev {(FairDelayState Single var_ctr (butlast var_buffer), (fairDelayOut_o (Msg ((last var_buffer))))) | var_ctr . (True)})"
  using assms by(auto simp add: fairDelayTransition_def assms)

(* Line 25:  Single [ctr==0 && buffer.size()==0] / {ctr=rand{j.true}, o=i}; *)
lemma fairDelayTransition_1_2:
  assumes "var_ctr=0 \<and> (size var_buffer)=0"
    shows "fairDelayTransition ((FairDelayState Single var_ctr var_buffer), (fairDelayElemIn_i null))
         = (Rev {(FairDelayState Single var_ctr var_buffer, (fairDelayOut_o null)) | var_ctr . (True)})"
  using assms by(auto simp add: fairDelayTransition_def assms)


section \<open>Step-wise lemmata for the SPS\<close>

(* Convert the SPS to step notation *)
lemma fairDelaySps2Step: "fairDelaySPS = uspecFlatten fairDelayDom fairDelayRan
    (Rev {spsConcOut (fairDelayOut_o null) (fairDelayStep (FairDelayState Single (var_ctr::nat)([] ::'e::countable list))) | var_ctr . (True)})"
  sorry

(* Line 19:  Single [ctr>0 && i!=null] / {ctr=ctr-1, buffer=buffer.prepend(i)}; *)
lemma fairDelayStep_0_0:
  assumes "var_ctr>0"
    shows "spsConcIn  (fairDelayIn_i (Msg port_i)) (fairDelayStep (FairDelayState Single var_ctr var_buffer))
         = spsConcOut (fairDelayOut_o null) (fairDelayStep (FairDelayState Single (var_ctr-1) (prepend var_buffer port_i)))"
  oops

(* Line 22:  Single [ctr==0 && i!=null && buffer.size()>0] / {ctr=rand{j.true}, o=buffer.last(), buffer=buffer.butlast().prepend(i)}; *)
lemma fairDelayStep_0_1:
  assumes "var_ctr=0 \<and> (size var_buffer)>0"
    shows "spsConcIn  (fairDelayIn_i (Msg port_i)) (fairDelayStep (FairDelayState Single var_ctr var_buffer))
         = uspecFlatten fairDelayDom fairDelayRan
          (Rev {spsConcOut (fairDelayOut_o (Msg ((last var_buffer)))) (fairDelayStep (FairDelayState Single var_ctr (prepend (butlast var_buffer) port_i))) | var_ctr . (True)})"
  oops

(* Line 25:  Single [ctr==0 && buffer.size()==0] / {ctr=rand{j.true}, o=i}; *)
lemma fairDelayStep_0_2:
  assumes "var_ctr=0 \<and> (size var_buffer)=0"
    shows "spsConcIn  (fairDelayIn_i (Msg port_i)) (fairDelayStep (FairDelayState Single var_ctr var_buffer))
         = uspecFlatten fairDelayDom fairDelayRan
          (Rev {spsConcOut (fairDelayOut_o (Msg (port_i))) (fairDelayStep (FairDelayState Single var_ctr var_buffer)) | var_ctr . (True)})"
  oops

(* Line 20:  Single [ctr>0 && i==null] / {ctr=ctr-1}; *)
lemma fairDelayStep_1_0:
  assumes "var_ctr>0"
    shows "spsConcIn  (fairDelayIn_i null) (fairDelayStep (FairDelayState Single var_ctr var_buffer))
         = spsConcOut (fairDelayOut_o null) (fairDelayStep (FairDelayState Single (var_ctr-1) var_buffer))"
  oops

(* Line 23:  Single [ctr==0 && i==null && buffer.size()>0] / {ctr=rand{j.true}, o=buffer.last(), buffer=buffer.butlast()}; *)
lemma fairDelayStep_1_1:
  assumes "var_ctr=0 \<and> (size var_buffer)>0"
    shows "spsConcIn  (fairDelayIn_i null) (fairDelayStep (FairDelayState Single var_ctr var_buffer))
         = uspecFlatten fairDelayDom fairDelayRan
          (Rev {spsConcOut (fairDelayOut_o (Msg ((last var_buffer)))) (fairDelayStep (FairDelayState Single var_ctr (butlast var_buffer))) | var_ctr . (True)})"
  oops

(* Line 25:  Single [ctr==0 && buffer.size()==0] / {ctr=rand{j.true}, o=i}; *)
lemma fairDelayStep_1_2:
  assumes "var_ctr=0 \<and> (size var_buffer)=0"
    shows "spsConcIn  (fairDelayIn_i null) (fairDelayStep (FairDelayState Single var_ctr var_buffer))
         = uspecFlatten fairDelayDom fairDelayRan
          (Rev {spsConcOut (fairDelayOut_o null) (fairDelayStep (FairDelayState Single var_ctr var_buffer)) | var_ctr . (True)})"
  oops


end