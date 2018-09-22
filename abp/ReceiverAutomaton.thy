(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Sep 22, 2018 1:11:51 PM by isartransformer 1.0.0
 *)
theory ReceiverAutomaton
  imports bundle.tsynBundle automat.dAutomaton

begin


(* TODO SWS: Move this to dAutomaton *)
lemma da_h_stepI:
  assumes "sbeDom sbe = daDom da"
      and "(daNextOutput da s sbe) = out"
      and "(daNextState da s sbe) = nextState"
  shows "spfConcIn (sbe2SB sbe)\<cdot>(da_h da s) = spfConcOut out\<cdot>(da_h da nextState)"
  by (metis (no_types) assms da_h_dom da_h_final_h3 spfConcIn_dom spfConcIn_step spfConcOut_dom spf_eq)

(* TODO SWS: Move this to...? *)
setup_lifting type_definition_cfun

(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"

section \<open>Datatype definition\<close>

datatype receiverMessage = ReceiverPair_ReceiverNat_ReceiverBool "(nat\<times>bool)" | ReceiverBool "bool" | ReceiverNat "nat"

instance receiverMessage :: countable
  apply(intro_classes)
  by(countable_datatype)

instantiation receiverMessage :: message
begin
  fun ctype_receiverMessage :: "channel \<Rightarrow> receiverMessage set" where
  "ctype_receiverMessage c = (
    if c = \<C> ''dr'' then range ReceiverPair_ReceiverNat_ReceiverBool else
    if c = \<C> ''ar'' then range ReceiverBool else
    if c = \<C> ''o'' then range ReceiverNat else
    undefined)"
  instance
    by(intro_classes)
end


section \<open>Helpers to create a bundle from a single raw element\<close>

lift_definition receiverElem_raw_dr :: "(nat\<times>bool) \<Rightarrow> receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''dr'' \<mapsto> Msg (ReceiverPair_ReceiverNat_ReceiverBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition receiverElem_raw_ar :: "bool \<Rightarrow> receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''ar'' \<mapsto> Msg (ReceiverBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition receiverElem_raw_o :: "nat \<Rightarrow> receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''o'' \<mapsto> Msg (ReceiverNat x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun receiverElem_dr :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"receiverElem_dr (Msg port_dr) = receiverElem_raw_dr port_dr" |
"receiverElem_dr null = sbeNull {\<C> ''dr''}"

declare receiverElem_dr.simps[simp del]

definition receiver_dr :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn SB" where
"receiver_dr port_dr = sbe2SB (receiverElem_dr port_dr)"

fun receiverElem_ar :: "bool tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"receiverElem_ar (Msg port_ar) = receiverElem_raw_ar port_ar" |
"receiverElem_ar null = sbeNull {\<C> ''ar''}"

declare receiverElem_ar.simps[simp del]

definition receiver_ar :: "bool tsyn \<Rightarrow> receiverMessage tsyn SB" where
"receiver_ar port_ar = sbe2SB (receiverElem_ar port_ar)"

fun receiverElem_o :: "nat tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"receiverElem_o (Msg port_o) = receiverElem_raw_o port_o" |
"receiverElem_o null = sbeNull {\<C> ''o''}"

declare receiverElem_o.simps[simp del]

definition receiver_o :: "nat tsyn \<Rightarrow> receiverMessage tsyn SB" where
"receiver_o port_o = sbe2SB (receiverElem_o port_o)"

(* Create one sbElem for all input channels *)
definition receiverElemIn_dr :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"receiverElemIn_dr port_dr = (receiverElem_dr port_dr)"

(* Create one sbElem for all output channels *)
definition receiverElemOut_ar_o :: "bool tsyn \<Rightarrow> nat tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"receiverElemOut_ar_o port_ar port_o = (receiverElem_ar port_ar) \<plusminus> (receiverElem_o port_o)"

(* Create one SB for all input channels *)
definition receiverIn_dr :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn SB" where
"receiverIn_dr port_dr = (sbe2SB (receiverElemIn_dr port_dr))"

(* Create one SB for all output channels *)
definition receiverOut_ar_o :: "bool tsyn \<Rightarrow> nat tsyn \<Rightarrow> receiverMessage tsyn SB" where
"receiverOut_ar_o port_ar port_o = (sbe2SB (receiverElemOut_ar_o port_ar port_o))"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

fun receiver_list_dr :: "((nat\<times>bool) tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"receiver_list_dr (x#xs) = ubConcEq (receiver_dr x)\<cdot>(receiver_list_dr xs)" |
"receiver_list_dr []     = ubLeast {\<C> ''dr''}"

fun receiver_list_ar :: "(bool tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"receiver_list_ar (x#xs) = ubConcEq (receiver_ar x)\<cdot>(receiver_list_ar xs)" |
"receiver_list_ar []     = ubLeast {\<C> ''ar''}"

fun receiver_list_o :: "(nat tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"receiver_list_o (x#xs) = ubConcEq (receiver_o x)\<cdot>(receiver_list_o xs)" |
"receiver_list_o []     = ubLeast {\<C> ''o''}"

(* Create one SB for all input channels *)
definition receiverIn_list_dr :: "(nat\<times>bool) tsyn list \<Rightarrow> receiverMessage tsyn SB" where
"receiverIn_list_dr port_dr = (receiver_list_dr port_dr)"

(* Create one SB for all output channels *)
definition receiverOut_list_ar_o :: "bool tsyn list \<Rightarrow> nat tsyn list \<Rightarrow> receiverMessage tsyn SB" where
"receiverOut_list_ar_o port_ar port_o = (receiver_list_ar port_ar) \<uplus> (receiver_list_o port_o)"


section \<open>Helpers to create a bundle from a tsyn stream of elements\<close>

lift_definition receiver_stream_dr_h :: "(nat\<times>bool) tsyn stream \<Rightarrow> receiverMessage tsyn SB" is
"\<lambda> s. [(\<C> ''dr'') \<mapsto> (tsynMap (ReceiverPair_ReceiverNat_ReceiverBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition receiver_stream_dr :: "((nat\<times>bool)) tsyn stream \<rightarrow> receiverMessage tsyn SB" is
"receiver_stream_dr_h"
  sorry

lift_definition receiver_stream_ar_h :: "bool tsyn stream \<Rightarrow> receiverMessage tsyn SB" is
"\<lambda> s. [(\<C> ''ar'') \<mapsto> (tsynMap (ReceiverBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition receiver_stream_ar :: "(bool) tsyn stream \<rightarrow> receiverMessage tsyn SB" is
"receiver_stream_ar_h"
  sorry

lift_definition receiver_stream_o_h :: "nat tsyn stream \<Rightarrow> receiverMessage tsyn SB" is
"\<lambda> s. [(\<C> ''o'') \<mapsto> (tsynMap (ReceiverNat)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition receiver_stream_o :: "(nat) tsyn stream \<rightarrow> receiverMessage tsyn SB" is
"receiver_stream_o_h"
  sorry

(* Create one SB for all input channels *)
definition receiverIn_stream_dr :: "(nat\<times>bool) tsyn stream \<rightarrow> receiverMessage tsyn SB" where
"receiverIn_stream_dr = (\<Lambda>  port_dr. (receiver_stream_dr\<cdot>port_dr))"

(* Create one SB for all output channels *)
definition receiverOut_stream_ar_o :: "bool tsyn stream \<rightarrow> nat tsyn stream \<rightarrow> receiverMessage tsyn SB" where
"receiverOut_stream_ar_o = (\<Lambda>  port_ar port_o. (receiver_stream_ar\<cdot>port_ar) \<uplus> (receiver_stream_o\<cdot>port_o))"


section \<open>Helpers to get tsyn elements and streams from sbElems and SBs\<close>

fun receiverElem_get_dr :: "receiverMessage tsyn sbElem \<Rightarrow> ((nat\<times>bool)) tsyn" where
"receiverElem_get_dr sbe = undefined"

lift_definition receiver_get_stream_dr :: "receiverMessage tsyn SB \<rightarrow> (nat\<times>bool) tsyn stream" is
"\<lambda>sb. tsynMap (inv ReceiverPair_ReceiverNat_ReceiverBool)\<cdot>(sb . (\<C> ''dr''))"
  by(simp add: cfun_def)

fun receiverElem_get_ar :: "receiverMessage tsyn sbElem \<Rightarrow> (bool) tsyn" where
"receiverElem_get_ar sbe = undefined"

lift_definition receiver_get_stream_ar :: "receiverMessage tsyn SB \<rightarrow> bool tsyn stream" is
"\<lambda>sb. tsynMap (inv ReceiverBool)\<cdot>(sb . (\<C> ''ar''))"
  by(simp add: cfun_def)

fun receiverElem_get_o :: "receiverMessage tsyn sbElem \<Rightarrow> (nat) tsyn" where
"receiverElem_get_o sbe = undefined"

lift_definition receiver_get_stream_o :: "receiverMessage tsyn SB \<rightarrow> nat tsyn stream" is
"\<lambda>sb. tsynMap (inv ReceiverNat)\<cdot>(sb . (\<C> ''o''))"
  by(simp add: cfun_def)



section \<open>Automaton definition\<close>

(* These are the actual states from MAA *)
datatype ReceiverSubstate = Rf | Rt

(* And these have also the variables *)
datatype ReceiverState = ReceiverState ReceiverSubstate 

(* Function to get the substate *)
fun getReceiverSubState :: "ReceiverState \<Rightarrow> ReceiverSubstate" where
"getReceiverSubState (ReceiverState s ) = s"

(* Helper that allows us to utilize pattern matching *)
fun receiverTransitionH :: "(ReceiverState \<times> ((nat\<times>bool) tsyn)) \<Rightarrow> (ReceiverState \<times> receiverMessage tsyn SB)" where
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

(* Domain *)
definition receiverDom :: "channel set" where
"receiverDom = {\<C> ''dr''}"

(* Range *)
definition receiverRan :: "channel set" where
"receiverRan = {\<C> ''ar'', \<C> ''o''}"

(* Transition function *)
definition receiverTransition :: "(ReceiverState \<times> receiverMessage tsyn sbElem) \<Rightarrow> (ReceiverState \<times> receiverMessage tsyn SB)" where
"receiverTransition = (\<lambda> (s,b). (if (sbeDom b) = receiverDom then receiverTransitionH (s, (receiverElem_get_dr b)) else undefined))"

(* Initial state *)
definition receiverInitialState :: "ReceiverState" where
"receiverInitialState = ReceiverState Rt "

(* Initial output *)
definition receiverInitialOutput :: "receiverMessage tsyn SB" where
"receiverInitialOutput = receiverOut_ar_o null null"

(* The final automaton *)
lift_definition receiverAutomaton :: "(ReceiverState, receiverMessage tsyn) dAutomaton" is
"(receiverTransition, receiverInitialState, receiverInitialOutput, receiverDom, receiverRan)"
  by (simp add: receiverDom_def receiverRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition receiverStep :: "(ReceiverState \<Rightarrow> (receiverMessage tsyn, receiverMessage tsyn) SPF)" where
"receiverStep = da_h receiverAutomaton"

(* The final SPF *)
definition receiverSPF :: "(receiverMessage tsyn, receiverMessage tsyn) SPF" where
"receiverSPF = da_H receiverAutomaton"


section \<open>Lemmas for automaton definition\<close>

lemma receiverautomaton_trans[simp]: "daTransition receiverAutomaton = receiverTransition"
  sorry

lemma receiverautomaton_initialstate[simp]: "daInitialState receiverAutomaton = receiverInitialState"
  sorry

lemma receiverautomaton_initialoutput[simp]: "daInitialOutput receiverAutomaton = receiverInitialOutput"
  sorry

lemma receiverautomaton_dom[simp]: "daDom receiverAutomaton = receiverDom"
  sorry

lemma receiverautomaton_ran[simp]: "daRan receiverAutomaton = receiverRan"
  sorry


section \<open>Lemmas for single tsyn setter\<close>

lemma receiverelemin_dr_dom[simp]: "sbeDom (receiverElemIn_dr port_dr) = receiverDom"
  sorry

lemma receiverelemout_ar_o_dom[simp]: "sbeDom (receiverElemOut_ar_o port_ar port_o) = receiverRan"
  sorry

lemma receiverin_dr_dom[simp]: "ubDom\<cdot>(receiverIn_dr port_dr) = receiverDom"
  sorry

lemma receiverout_ar_o_dom[simp]: "ubDom\<cdot>(receiverOut_ar_o port_ar port_o) = receiverRan"
  sorry


section \<open>Lemmas for getter\<close>

(* SWS: die getter-id-lemma auch für die multi-parameter Version *)
lemma SWSexample[simp]: "receiver_get_stream_ar\<cdot>(receiverOut_ar_o port_ar port_o) = \<up>port_ar"
  sorry
lemma SWSexample2[simp]: "receiver_get_stream_ar\<cdot>(receiverOut_stream_ar_o\<cdot>port_ar\<cdot>port_o) = port_ar"
  sorry
lemma SWSexample3[simp]: "receiver_get_stream_ar\<cdot>(receiverOut_list_ar_o port_ar port_o) = <port_ar>"
  sorry
lemma SWSexample4[simp]: "receiverElem_get_ar (receiverElemOut_ar_o port_ar port_o) = port_ar"
  sorry
(* SWS: End Example *)



lemma receiverelem_dr_id[simp]: "receiverElem_get_dr (receiverElem_dr port_dr) = port_dr"
  sorry

lemma receiver_stream_dr_id[simp]: "receiver_get_stream_dr\<cdot>(receiver_stream_dr\<cdot>port_dr) = port_dr"
  sorry

lemma receiverelem_ar_id[simp]: "receiverElem_get_ar (receiverElem_ar port_ar) = port_ar"
  sorry

lemma receiver_stream_ar_id[simp]: "receiver_get_stream_ar\<cdot>(receiver_stream_ar\<cdot>port_ar) = port_ar"
  sorry

lemma receiverelem_o_id[simp]: "receiverElem_get_o (receiverElem_o port_o) = port_o"
  sorry

lemma receiver_stream_o_id[simp]: "receiver_get_stream_o\<cdot>(receiver_stream_o\<cdot>port_o) = port_o"
  sorry


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 18:  Rf -> Rf [dr.snd=true] / {ar=true}; *)
lemma receiverTransition_0_0[simp]:
  assumes "(snd port_dr)=True"
    shows "receiverTransition ((ReceiverState Rf ), (receiverElemIn_dr (Msg port_dr)))
         = (ReceiverState Rf, (receiverOut_ar_o (Msg (True)) null))"
  apply(simp add: receiverTransition_def)
  sorry

(* Line 19:  Rf -> Rt [dr.snd=false] / {ar=false, o=dr.fst}; *)
lemma receiverTransition_0_1[simp]:
  assumes "(snd port_dr)=False"
    shows "receiverTransition ((ReceiverState Rf ), (receiverElemIn_dr (Msg port_dr)))
         = (ReceiverState Rt, (receiverOut_ar_o (Msg (False)) (Msg ((fst port_dr)))))"
  apply(simp add: receiverTransition_def)
  sorry

(* Line 17:  Rf -> Rf {dr==null}; *)
lemma receiverTransition_1_0[simp]:
  assumes "True"
    shows "receiverTransition ((ReceiverState Rf ), (receiverElemIn_dr null))
         = (ReceiverState Rf, (receiverOut_ar_o null null))"
  apply(simp add: receiverTransition_def)
  sorry

(* Line 14:  Rt -> Rf [dr.snd=true] / {o=dr.fst, ar=true}; *)
lemma receiverTransition_2_0[simp]:
  assumes "(snd port_dr)=True"
    shows "receiverTransition ((ReceiverState Rt ), (receiverElemIn_dr (Msg port_dr)))
         = (ReceiverState Rf, (receiverOut_ar_o (Msg (True)) (Msg ((fst port_dr)))))"
  apply(simp add: receiverTransition_def)
  sorry

(* Line 15:  Rt -> Rt [dr.snd=false] / {ar=false}; *)
lemma receiverTransition_2_1[simp]:
  assumes "(snd port_dr)=False"
    shows "receiverTransition ((ReceiverState Rt ), (receiverElemIn_dr (Msg port_dr)))
         = (ReceiverState Rt, (receiverOut_ar_o (Msg (False)) null))"
  apply(simp add: receiverTransition_def)
  sorry

(* Line 16:  Rt -> Rt {dr==null}; *)
lemma receiverTransition_3_0[simp]:
  assumes "True"
    shows "receiverTransition ((ReceiverState Rt ), (receiverElemIn_dr null))
         = (ReceiverState Rt, (receiverOut_ar_o null null))"
  apply(simp add: receiverTransition_def)
  sorry


section \<open>Step-wise lemmata for the SPF\<close>

(* Convert the SPF to step notation *)
lemma receiverSpf2Step: "receiverSPF = spfConcOut (receiverOut_ar_o null null)\<cdot>(ReceiverStep (ReceiverState Rt ))"
  sorry

(* Line 18:  Rf -> Rf [dr.snd=true] / {ar=true}; *)
lemma receiverStep_0_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (receiverIn_dr (Msg port_dr))\<cdot>(receiverStep (ReceiverState Rf ))
         = spfConcOut (receiverOut_ar_o (Msg (True)) null)\<cdot>(receiverStep (ReceiverState Rf))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  apply(auto simp add: daNextState_def daNextOutput_def assms)
  (* TODO SWS: Manchmal fehlt noch das hier: *)
  (*using assms by auto*)
  sorry

(* Line 19:  Rf -> Rt [dr.snd=false] / {ar=false, o=dr.fst}; *)
lemma receiverStep_0_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (receiverIn_dr (Msg port_dr))\<cdot>(receiverStep (ReceiverState Rf ))
         = spfConcOut (receiverOut_ar_o (Msg (False)) (Msg ((fst port_dr))))\<cdot>(receiverStep (ReceiverState Rt))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  apply(auto simp add: daNextState_def daNextOutput_def assms)
  (* TODO SWS: Manchmal fehlt noch das hier: *)
  (*using assms by auto*)
  sorry

(* Line 17:  Rf -> Rf {dr==null}; *)
lemma receiverStep_1_0:
  assumes "True"
    shows "spfConcIn  (receiverIn_dr null)\<cdot>(receiverStep (ReceiverState Rf ))
         = spfConcOut (receiverOut_ar_o null null)\<cdot>(receiverStep (ReceiverState Rf))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  apply(auto simp add: daNextState_def daNextOutput_def assms)
  (* TODO SWS: Manchmal fehlt noch das hier: *)
  (*using assms by auto*)
  sorry

(* Line 14:  Rt -> Rf [dr.snd=true] / {o=dr.fst, ar=true}; *)
lemma receiverStep_2_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (receiverIn_dr (Msg port_dr))\<cdot>(receiverStep (ReceiverState Rt ))
         = spfConcOut (receiverOut_ar_o (Msg (True)) (Msg ((fst port_dr))))\<cdot>(receiverStep (ReceiverState Rf))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  apply(auto simp add: daNextState_def daNextOutput_def assms)
  (* TODO SWS: Manchmal fehlt noch das hier: *)
  (*using assms by auto*)
  sorry

(* Line 15:  Rt -> Rt [dr.snd=false] / {ar=false}; *)
lemma receiverStep_2_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (receiverIn_dr (Msg port_dr))\<cdot>(receiverStep (ReceiverState Rt ))
         = spfConcOut (receiverOut_ar_o (Msg (False)) null)\<cdot>(receiverStep (ReceiverState Rt))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  apply(auto simp add: daNextState_def daNextOutput_def assms)
  (* TODO SWS: Manchmal fehlt noch das hier: *)
  (*using assms by auto*)
  sorry

(* Line 16:  Rt -> Rt {dr==null}; *)
lemma receiverStep_3_0:
  assumes "True"
    shows "spfConcIn  (receiverIn_dr null)\<cdot>(receiverStep (ReceiverState Rt ))
         = spfConcOut (receiverOut_ar_o null null)\<cdot>(receiverStep (ReceiverState Rt))"
  apply(simp add: receiverStep_def receiverIn_dr_def)
  apply(rule da_h_stepI)
  apply(auto simp add: daNextState_def daNextOutput_def assms)
  (* TODO SWS: Manchmal fehlt noch das hier: *)
  (*using assms by auto*)
  sorry


end