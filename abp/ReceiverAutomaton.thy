(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 2.0.0
 *)
theory ReceiverAutomaton
  imports ReceiverDatatype ReceiverStates automat.dAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Automaton definition\<close>

(* Helper that allows us to utilize pattern matching *)
fun receiverTransitionH :: "(ReceiverState \<times> (('e\<times>bool) tsyn)) \<Rightarrow> (ReceiverState \<times> ('e::countable) receiverMessage tsyn SB)" where
"receiverTransitionH (ReceiverState Rf, (\<^cancel>\<open>dr\<mapsto>\<close>Msg port_dr)) =
  (if((snd port_dr)=True) then ((ReceiverState Rf, (receiverOut_ar_o (Msg (True)) null)))
   else if((snd port_dr)=False) then ((ReceiverState Rt, (receiverOut_ar_o (Msg (False)) (Msg ((fst port_dr))))))
   else (ReceiverState Rf, (receiverOut_ar_o null null)))" |

"receiverTransitionH (ReceiverState Rf, (\<^cancel>\<open>dr\<mapsto>\<close>null)) =
  (ReceiverState Rf, (receiverOut_ar_o null null))" |

"receiverTransitionH (ReceiverState Rt, (\<^cancel>\<open>dr\<mapsto>\<close>Msg port_dr)) =
  (if((snd port_dr)=True) then ((ReceiverState Rf, (receiverOut_ar_o (Msg (True)) (Msg ((fst port_dr))))))
   else if((snd port_dr)=False) then ((ReceiverState Rt, (receiverOut_ar_o (Msg (False)) null)))
   else (ReceiverState Rt, (receiverOut_ar_o null null)))" |

"receiverTransitionH (ReceiverState Rt, (\<^cancel>\<open>dr\<mapsto>\<close>null)) =
  (ReceiverState Rt, (receiverOut_ar_o null null))"

(* Transition function *)
definition receiverTransition :: "(ReceiverState \<times> ('e::countable) receiverMessage tsyn sbElem) \<Rightarrow> (ReceiverState \<times> ('e::countable) receiverMessage tsyn SB)" where
"receiverTransition = (\<lambda> (s,b). (if (sbeDom b) = receiverDom then receiverTransitionH (s, (receiverElem_get_dr b)) else undefined))"

(* Initial state *)
definition receiverInitialState :: "ReceiverState" where
"receiverInitialState = ReceiverState Rt "

(* Initial output *)
definition receiverInitialOutput :: "('e::countable) receiverMessage tsyn SB" where
"receiverInitialOutput = receiverOut_ar_o null null"

(* The final automaton *)
lift_definition receiverAutomaton :: "(ReceiverState, ('e::countable) receiverMessage tsyn) dAutomaton" is
"(receiverTransition, receiverInitialState, receiverInitialOutput, receiverDom, receiverRan)"
  by (simp add: receiverDom_def receiverRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition receiverStep :: "(ReceiverState \<Rightarrow> (('e::countable) receiverMessage tsyn, ('e::countable) receiverMessage tsyn) SPF)" where
"receiverStep = da_h receiverAutomaton"

(* The final SPF *)
definition receiverSPF :: "(('e::countable) receiverMessage tsyn, ('e::countable) receiverMessage tsyn) SPF" where
"receiverSPF = da_H (receiverAutomaton::(ReceiverState, ('e::countable) receiverMessage tsyn) dAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma receiverautomaton_trans[simp]: "daTransition receiverAutomaton = receiverTransition"
  unfolding daTransition_def
  by(simp add: receiverAutomaton.rep_eq)

lemma receiverautomaton_initialstate[simp]: "daInitialState receiverAutomaton = receiverInitialState"
  unfolding daInitialState_def
  by(simp add: receiverAutomaton.rep_eq)

lemma receiverautomaton_initialoutput[simp]: "daInitialOutput receiverAutomaton = receiverInitialOutput"
  unfolding daInitialOutput_def
  by(simp add: receiverAutomaton.rep_eq)

lemma receiverautomaton_dom[simp]: "daDom receiverAutomaton = receiverDom"
  unfolding daDom_def
  by(simp add: receiverAutomaton.rep_eq)

lemma receiverautomaton_ran[simp]: "daRan receiverAutomaton = receiverRan"
  unfolding daRan_def
  by(simp add: receiverAutomaton.rep_eq)


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 18:  Rf -> Rf [dr.snd=true] / {ar=true}; *)
lemma receiverTransition_0_0[simp]:
  assumes "(snd port_dr)=True"
    shows "receiverTransition ((ReceiverState Rf ), (receiverElemIn_dr (Msg port_dr)))
         = (ReceiverState Rf, (receiverOut_ar_o (Msg (True)) null))"
  using assms by(auto simp add: receiverTransition_def assms)

(* Line 19:  Rf -> Rt [dr.snd=false] / {ar=false, o=dr.fst}; *)
lemma receiverTransition_0_1[simp]:
  assumes "(snd port_dr)=False"
    shows "receiverTransition ((ReceiverState Rf ), (receiverElemIn_dr (Msg port_dr)))
         = (ReceiverState Rt, (receiverOut_ar_o (Msg (False)) (Msg ((fst port_dr)))))"
  using assms by(auto simp add: receiverTransition_def assms)

(* Line 17:  Rf -> Rf {dr==null}; *)
lemma receiverTransition_1_0[simp]:
  assumes "True"
    shows "receiverTransition ((ReceiverState Rf ), (receiverElemIn_dr null))
         = (ReceiverState Rf, (receiverOut_ar_o null null))"
  using assms by(auto simp add: receiverTransition_def assms)

(* Line 14:  Rt -> Rf [dr.snd=true] / {o=dr.fst, ar=true}; *)
lemma receiverTransition_2_0[simp]:
  assumes "(snd port_dr)=True"
    shows "receiverTransition ((ReceiverState Rt ), (receiverElemIn_dr (Msg port_dr)))
         = (ReceiverState Rf, (receiverOut_ar_o (Msg (True)) (Msg ((fst port_dr)))))"
  using assms by(auto simp add: receiverTransition_def assms)

(* Line 15:  Rt -> Rt [dr.snd=false] / {ar=false}; *)
lemma receiverTransition_2_1[simp]:
  assumes "(snd port_dr)=False"
    shows "receiverTransition ((ReceiverState Rt ), (receiverElemIn_dr (Msg port_dr)))
         = (ReceiverState Rt, (receiverOut_ar_o (Msg (False)) null))"
  using assms by(auto simp add: receiverTransition_def assms)

(* Line 16:  Rt -> Rt {dr==null}; *)
lemma receiverTransition_3_0[simp]:
  assumes "True"
    shows "receiverTransition ((ReceiverState Rt ), (receiverElemIn_dr null))
         = (ReceiverState Rt, (receiverOut_ar_o null null))"
  using assms by(auto simp add: receiverTransition_def assms)


section \<open>Step-wise lemmata for the SPF\<close>

(* Convert the SPF to step notation *)
lemma receiverSpf2Step: "receiverSPF = spfConcOut (receiverOut_ar_o null null)\<cdot>(receiverStep (ReceiverState Rt ))"
  by(simp add: receiverSPF_def da_H_def receiverInitialOutput_def receiverInitialState_def receiverStep_def)

(* Line 18:  Rf -> Rf [dr.snd=true] / {ar=true}; *)
lemma receiverStep_0_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (receiverIn_dr (Msg port_dr))\<cdot>(receiverStep (ReceiverState Rf ))
         = spfConcOut (receiverOut_ar_o (Msg (True)) null)\<cdot>(receiverStep (ReceiverState Rf))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 19:  Rf -> Rt [dr.snd=false] / {ar=false, o=dr.fst}; *)
lemma receiverStep_0_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (receiverIn_dr (Msg port_dr))\<cdot>(receiverStep (ReceiverState Rf ))
         = spfConcOut (receiverOut_ar_o (Msg (False)) (Msg ((fst port_dr))))\<cdot>(receiverStep (ReceiverState Rt))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 17:  Rf -> Rf {dr==null}; *)
lemma receiverStep_1_0:
  assumes "True"
    shows "spfConcIn  (receiverIn_dr null)\<cdot>(receiverStep (ReceiverState Rf ))
         = spfConcOut (receiverOut_ar_o null null)\<cdot>(receiverStep (ReceiverState Rf))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 14:  Rt -> Rf [dr.snd=true] / {o=dr.fst, ar=true}; *)
lemma receiverStep_2_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (receiverIn_dr (Msg port_dr))\<cdot>(receiverStep (ReceiverState Rt ))
         = spfConcOut (receiverOut_ar_o (Msg (True)) (Msg ((fst port_dr))))\<cdot>(receiverStep (ReceiverState Rf))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 15:  Rt -> Rt [dr.snd=false] / {ar=false}; *)
lemma receiverStep_2_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (receiverIn_dr (Msg port_dr))\<cdot>(receiverStep (ReceiverState Rt ))
         = spfConcOut (receiverOut_ar_o (Msg (False)) null)\<cdot>(receiverStep (ReceiverState Rt))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 16:  Rt -> Rt {dr==null}; *)
lemma receiverStep_3_0:
  assumes "True"
    shows "spfConcIn  (receiverIn_dr null)\<cdot>(receiverStep (ReceiverState Rt ))
         = spfConcOut (receiverOut_ar_o null null)\<cdot>(receiverStep (ReceiverState Rt))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)


end