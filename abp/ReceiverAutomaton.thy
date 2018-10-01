(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 1, 2018 1:17:46 AM by isartransformer 1.0.0
 *)
theory ReceiverAutomaton
  imports bundle.tsynBundle automat.dAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Datatype definition\<close>

datatype ('e::countable) receiverMessage = DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverPair_E_Bool "('e\<times>bool)" | DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverBool "bool" | DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverE "'e"

instance receiverMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation receiverMessage :: (countable) message
begin
  fun ctype_receiverMessage :: "channel \<Rightarrow> ('e::countable) receiverMessage set" where
  "ctype_receiverMessage c = (
    if c = \<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_dr'' then range DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverPair_E_Bool else
    if c = \<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_ar'' then range DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverBool else
    if c = \<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_o'' then range DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverE else
    undefined)"
  instance
    by(intro_classes)
end


section \<open>Domain and range\<close>

definition receiverDom :: "channel set" where
"receiverDom = {\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_dr''}"

definition receiverRan :: "channel set" where
"receiverRan = {\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_ar'', \<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_o''}"


section \<open>Helpers to create a bundle from a single raw element\<close>

lift_definition receiverElem_raw_dr :: "('e\<times>bool) \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_dr'' \<mapsto> Msg (DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverPair_E_Bool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition receiverElem_raw_ar :: "bool \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_ar'' \<mapsto> Msg (DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition receiverElem_raw_o :: "'e \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_o'' \<mapsto> Msg (DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun receiverElem_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" where
"receiverElem_dr (Msg port_dr) = receiverElem_raw_dr port_dr" |
"receiverElem_dr null = sbeNull {\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_dr''}"

declare receiverElem_dr.simps[simp del]

definition receiver_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_dr port_dr = sbe2SB (receiverElem_dr port_dr)"

fun receiverElem_ar :: "bool tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" where
"receiverElem_ar (Msg port_ar) = receiverElem_raw_ar port_ar" |
"receiverElem_ar null = sbeNull {\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_ar''}"

declare receiverElem_ar.simps[simp del]

definition receiver_ar :: "bool tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_ar port_ar = sbe2SB (receiverElem_ar port_ar)"

fun receiverElem_o :: "'e tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" where
"receiverElem_o (Msg port_o) = receiverElem_raw_o port_o" |
"receiverElem_o null = sbeNull {\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_o''}"

declare receiverElem_o.simps[simp del]

definition receiver_o :: "'e tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_o port_o = sbe2SB (receiverElem_o port_o)"

(* Create one sbElem for all input channels *)
definition receiverElemIn_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" where
"receiverElemIn_dr port_dr = (receiverElem_dr port_dr)"

(* Create one sbElem for all output channels *)
definition receiverElemOut_ar_o :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn sbElem" where
"receiverElemOut_ar_o port_ar port_o = (receiverElem_ar port_ar) \<plusminus> (receiverElem_o port_o)"

(* Create one SB for all input channels *)
definition receiverIn_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverIn_dr port_dr = (sbe2SB (receiverElemIn_dr port_dr))"

(* Create one SB for all output channels *)
definition receiverOut_ar_o :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverOut_ar_o port_ar port_o = (sbe2SB (receiverElemOut_ar_o port_ar port_o))"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

fun receiver_list_dr :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_list_dr (x#xs) = ubConcEq (receiver_dr x)\<cdot>(receiver_list_dr xs)" |
"receiver_list_dr []     = ubLeast {\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_dr''}"

declare receiver_list_dr.simps[simp del]

fun receiver_list_ar :: "(bool tsyn) list \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_list_ar (x#xs) = ubConcEq (receiver_ar x)\<cdot>(receiver_list_ar xs)" |
"receiver_list_ar []     = ubLeast {\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_ar''}"

declare receiver_list_ar.simps[simp del]

fun receiver_list_o :: "('e tsyn) list \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiver_list_o (x#xs) = ubConcEq (receiver_o x)\<cdot>(receiver_list_o xs)" |
"receiver_list_o []     = ubLeast {\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_o''}"

declare receiver_list_o.simps[simp del]

(* Create one SB for all input channels *)
fun receiverIn_list_dr :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverIn_list_dr ((port_dr)#xs) = ubConcEq (receiverIn_dr port_dr)\<cdot>(receiverIn_list_dr xs)" |
"receiverIn_list_dr [] = ubLeast receiverDom"

(* Create one SB for all output channels *)
fun receiverOut_list_ar_o :: "(bool tsyn\<times>'e tsyn) list \<Rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverOut_list_ar_o ((port_ar,port_o)#xs) = ubConcEq (receiverOut_ar_o port_ar port_o)\<cdot>(receiverOut_list_ar_o xs)" |
"receiverOut_list_ar_o [] = ubLeast receiverRan"


section \<open>Helpers to create a bundle from a tsyn stream of elements\<close>

lift_definition DoNotUse_1c0d7c63719b48839967533f1cc69c57_receiver_stream_dr_h :: "('e\<times>bool) tsyn stream \<Rightarrow> ('e::countable) receiverMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_dr'') \<mapsto> (tsynMap (DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverPair_E_Bool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition receiver_stream_dr :: "(('e\<times>bool)) tsyn stream \<rightarrow> ('e::countable) receiverMessage tsyn SB" is
"DoNotUse_1c0d7c63719b48839967533f1cc69c57_receiver_stream_dr_h"
  sorry

lift_definition DoNotUse_1c0d7c63719b48839967533f1cc69c57_receiver_stream_ar_h :: "bool tsyn stream \<Rightarrow> ('e::countable) receiverMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_ar'') \<mapsto> (tsynMap (DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition receiver_stream_ar :: "(bool) tsyn stream \<rightarrow> ('e::countable) receiverMessage tsyn SB" is
"DoNotUse_1c0d7c63719b48839967533f1cc69c57_receiver_stream_ar_h"
  sorry

lift_definition DoNotUse_1c0d7c63719b48839967533f1cc69c57_receiver_stream_o_h :: "'e tsyn stream \<Rightarrow> ('e::countable) receiverMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_o'') \<mapsto> (tsynMap (DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition receiver_stream_o :: "('e) tsyn stream \<rightarrow> ('e::countable) receiverMessage tsyn SB" is
"DoNotUse_1c0d7c63719b48839967533f1cc69c57_receiver_stream_o_h"
  sorry

(* Create one SB for all input channels *)
definition receiverIn_stream_dr :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverIn_stream_dr = (\<Lambda>  port_dr. (receiver_stream_dr\<cdot>port_dr))"

(* Create one SB for all output channels *)
definition receiverOut_stream_ar_o :: "bool tsyn stream \<rightarrow> 'e tsyn stream \<rightarrow> ('e::countable) receiverMessage tsyn SB" where
"receiverOut_stream_ar_o = (\<Lambda>  port_ar port_o. (receiver_stream_ar\<cdot>port_ar) \<uplus> (receiver_stream_o\<cdot>port_o))"


section \<open>Helpers to get tsyn elements and streams from sbElems and SBs\<close>

fun receiverElem_get_dr :: "('e::countable) receiverMessage tsyn sbElem \<Rightarrow> (('e\<times>bool)) tsyn" where
"receiverElem_get_dr sbe = undefined"

lift_definition receiver_get_stream_dr :: "('e::countable) receiverMessage tsyn SB \<rightarrow> ('e\<times>bool) tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverPair_E_Bool)\<cdot>(sb . (\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_dr''))"
  by(simp add: cfun_def)

fun receiverElem_get_ar :: "('e::countable) receiverMessage tsyn sbElem \<Rightarrow> (bool) tsyn" where
"receiverElem_get_ar sbe = undefined"

lift_definition receiver_get_stream_ar :: "('e::countable) receiverMessage tsyn SB \<rightarrow> bool tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverBool)\<cdot>(sb . (\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_ar''))"
  by(simp add: cfun_def)

fun receiverElem_get_o :: "('e::countable) receiverMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"receiverElem_get_o sbe = undefined"

lift_definition receiver_get_stream_o :: "('e::countable) receiverMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_1c0d7c63719b48839967533f1cc69c57_ReceiverE)\<cdot>(sb . (\<C> ''DoNotUse_1c0d7c63719b48839967533f1cc69c57_o''))"
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

subsection \<open>Identity lemmas for single sbElems\<close>

lemma receiverelem_dr_id[simp]: "receiverElem_get_dr (receiverElem_dr x) = x"
  sorry

lemma receiverelem_ar_id[simp]: "receiverElem_get_ar (receiverElem_ar x) = x"
  sorry

lemma receiverelem_o_id[simp]: "receiverElem_get_o (receiverElem_o x) = x"
  sorry


subsection \<open>Identity lemmas for single SBs from streams\<close>

lemma receiver_stream_dr_id[simp]: "receiver_get_stream_dr\<cdot>(receiver_stream_dr\<cdot>x) = x"
  sorry

lemma receiver_stream_ar_id[simp]: "receiver_get_stream_ar\<cdot>(receiver_stream_ar\<cdot>x) = x"
  sorry

lemma receiver_stream_o_id[simp]: "receiver_get_stream_o\<cdot>(receiver_stream_o\<cdot>x) = x"
  sorry


subsection \<open>Identity lemmas for input sbElems\<close>

lemma receiverelemin_dr_dr_id[simp]: "receiverElem_get_dr (receiverElemIn_dr port_dr) = port_dr"
  sorry


subsection \<open>Identity lemmas for output sbElems\<close>

lemma receiverelemout_ar_o_ar_id[simp]: "receiverElem_get_ar (receiverElemOut_ar_o port_ar port_o) = port_ar"
  sorry

lemma receiverelemout_ar_o_o_id[simp]: "receiverElem_get_o (receiverElemOut_ar_o port_ar port_o) = port_o"
  sorry


subsection \<open>Identity lemmas for input SBs\<close>

lemma receiverin_dr_dr_id[simp]: "receiver_get_stream_dr\<cdot>(receiverIn_dr port_dr) = \<up>port_dr"
  sorry


subsection \<open>Identity lemmas for output SBs\<close>

lemma receiverout_ar_o_ar_id[simp]: "receiver_get_stream_ar\<cdot>(receiverOut_ar_o port_ar port_o) = \<up>port_ar"
  sorry

lemma receiverout_ar_o_o_id[simp]: "receiver_get_stream_o\<cdot>(receiverOut_ar_o port_ar port_o) = \<up>port_o"
  sorry


subsection \<open>Identity lemmas for input SBs from streams\<close>

lemma receiverin_stream_dr_dr_id[simp]: "receiver_get_stream_dr\<cdot>(receiverIn_stream_dr\<cdot>port_dr) = port_dr"
  sorry


subsection \<open>Identity lemmas for output SBs from streams\<close>

lemma receiverout_stream_ar_o_ar_id[simp]: "receiver_get_stream_ar\<cdot>(receiverOut_stream_ar_o\<cdot>port_ar\<cdot>port_o) = port_ar"
  sorry

lemma receiverout_stream_ar_o_o_id[simp]: "receiver_get_stream_o\<cdot>(receiverOut_stream_ar_o\<cdot>port_ar\<cdot>port_o) = port_o"
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
lemma receiverSpf2Step: "receiverSPF = spfConcOut (receiverOut_ar_o null null)\<cdot>(receiverStep (ReceiverState Rt ))"
  sorry

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