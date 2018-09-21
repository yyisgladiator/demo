(*
 * DO NOT MODIFY!
 * This file was generated from Receiver.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Sep 21, 2018 4:47:19 PM by isartransformer 1.0.0
 *)
theory ReceiverAutomaton
  imports bundle.tsynBundle automat.dAutomaton

begin

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
  fun ctype_receiverMessage :: "channel  \<Rightarrow> receiverMessage set" where
  "ctype_receiverMessage c = (
    if c = \<C> ''dr'' then range ReceiverPair_ReceiverNat_ReceiverBool else
    if c = \<C> ''ar'' then range ReceiverBool else
    if c = \<C> ''o'' then range ReceiverNat else
    {})"
    instance
    by(intro_classes)
end


section \<open>Helpers to create a bundle from a single raw element\<close>

lift_definition receiverElem_raw_Dr :: "(nat\<times>bool) \<Rightarrow> receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''dr'' \<mapsto> Msg (ReceiverPair_ReceiverNat_ReceiverBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition receiverElem_raw_Ar :: "bool \<Rightarrow> receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''ar'' \<mapsto> Msg (ReceiverBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition receiverElem_raw_O :: "nat \<Rightarrow> receiverMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''o'' \<mapsto> Msg (ReceiverNat x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun receiverElem_Dr :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"receiverElem_Dr (Msg port_dr) = receiverElem_raw_Dr port_dr" |
"receiverElem_Dr null = sbeNull {\<C> ''dr''}"

definition receiver_Dr :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn SB" where
"receiver_Dr port_dr = sbe2SB (receiverElem_Dr port_dr)"

fun receiverElem_Ar :: "bool tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"receiverElem_Ar (Msg port_ar) = receiverElem_raw_Ar port_ar" |
"receiverElem_Ar null = sbeNull {\<C> ''ar''}"

definition receiver_Ar :: "bool tsyn \<Rightarrow> receiverMessage tsyn SB" where
"receiver_Ar port_ar = sbe2SB (receiverElem_Ar port_ar)"

fun receiverElem_O :: "nat tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"receiverElem_O (Msg port_o) = receiverElem_raw_O port_o" |
"receiverElem_O null = sbeNull {\<C> ''o''}"

definition receiver_O :: "nat tsyn \<Rightarrow> receiverMessage tsyn SB" where
"receiver_O port_o = sbe2SB (receiverElem_O port_o)"

(* Create one sbElem for all input channels *)
fun receiverElemIn_Dr :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"receiverElemIn_Dr port_dr = (receiverElem_Dr port_dr)"

(* Create one sbElem for all output channels *)
fun receiverElemOut_Ar_O :: "bool tsyn \<Rightarrow> nat tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"receiverElemOut_Ar_O port_ar port_o = (receiverElem_Ar port_ar) \<plusminus> (receiverElem_O port_o)"

(* Create one SB for all input channels *)
fun receiverIn_Dr :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn SB" where
"receiverIn_Dr port_dr = (sbe2SB (receiverElemIn_Dr port_dr))"

(* Create one SB for all output channels *)
fun receiverOut_Ar_O :: "bool tsyn \<Rightarrow> nat tsyn \<Rightarrow> receiverMessage tsyn SB" where
"receiverOut_Ar_O port_ar port_o = (sbe2SB (receiverElemOut_Ar_O port_ar port_o))"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

fun receiver_list_Dr :: "((nat\<times>bool) tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"receiver_list_Dr (x#xs) = ubConcEq (receiver_Dr x)\<cdot>(receiver_list_Dr xs)" |
"receiver_list_Dr []     = ubLeast {\<C> ''dr''}"

fun receiver_list_Ar :: "(bool tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"receiver_list_Ar (x#xs) = ubConcEq (receiver_Ar x)\<cdot>(receiver_list_Ar xs)" |
"receiver_list_Ar []     = ubLeast {\<C> ''ar''}"

fun receiver_list_O :: "(nat tsyn) list \<Rightarrow> receiverMessage tsyn SB" where
"receiver_list_O (x#xs) = ubConcEq (receiver_O x)\<cdot>(receiver_list_O xs)" |
"receiver_list_O []     = ubLeast {\<C> ''o''}"

(* Create one SB for all input channels *)
fun receiverIn_list_Dr :: "(nat\<times>bool) tsyn list \<Rightarrow> receiverMessage tsyn SB" where
"receiverIn_list_Dr port_dr = (receiver_list_Dr port_dr)"

(* Create one SB for all output channels *)
fun receiverOut_list_Ar_O :: "bool tsyn list \<Rightarrow> nat tsyn list \<Rightarrow> receiverMessage tsyn SB" where
"receiverOut_list_Ar_O port_ar port_o = (receiver_list_Ar port_ar) \<uplus> (receiver_list_O port_o)"


section \<open>Helpers to create a bundle from a tsyn stream of elements\<close>

definition receiver_stream_Dr :: "((nat\<times>bool)) tsyn stream \<Rightarrow> receiverMessage tsyn SB" where
"receiver_stream_Dr = undefined"

definition receiver_stream_Ar :: "(bool) tsyn stream \<Rightarrow> receiverMessage tsyn SB" where
"receiver_stream_Ar = undefined"

definition receiver_stream_O :: "(nat) tsyn stream \<Rightarrow> receiverMessage tsyn SB" where
"receiver_stream_O = undefined"

(* Create one SB for all input channels *)
fun receiverIn_stream_Dr :: "(nat\<times>bool) tsyn stream \<Rightarrow> receiverMessage tsyn SB" where
"receiverIn_stream_Dr port_dr = (receiver_stream_Dr port_dr)"

(* Create one SB for all output channels *)
fun receiverOut_stream_Ar_O :: "bool tsyn stream \<Rightarrow> nat tsyn stream \<Rightarrow> receiverMessage tsyn SB" where
"receiverOut_stream_Ar_O port_ar port_o = (receiver_stream_Ar port_ar) \<uplus> (receiver_stream_O port_o)"


section \<open>Helpers to get tsyn elements and streams from sbElems and SBs\<close>

fun receiverElem_get_Dr :: "receiverMessage tsyn sbElem \<Rightarrow> ((nat\<times>bool)) tsyn" where
"receiverElem_get_Dr sbe = undefined"

fun receiverElem_get_stream_Dr :: "receiverMessage tsyn SB \<Rightarrow> ((nat\<times>bool)) tsyn stream" where
"receiverElem_get_stream_Dr sb = undefined"

fun receiverElem_get_Ar :: "receiverMessage tsyn sbElem \<Rightarrow> (bool) tsyn" where
"receiverElem_get_Ar sbe = undefined"

fun receiverElem_get_stream_Ar :: "receiverMessage tsyn SB \<Rightarrow> (bool) tsyn stream" where
"receiverElem_get_stream_Ar sb = undefined"

fun receiverElem_get_O :: "receiverMessage tsyn sbElem \<Rightarrow> (nat) tsyn" where
"receiverElem_get_O sbe = undefined"

fun receiverElem_get_stream_O :: "receiverMessage tsyn SB \<Rightarrow> (nat) tsyn stream" where
"receiverElem_get_stream_O sb = undefined"




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
  (if((snd port_dr)=True) then ((ReceiverState Rf, (receiverOut_Ar_O (Msg (True)) null)))
   else if((snd port_dr)=False) then ((ReceiverState Rt, (receiverOut_Ar_O (Msg (False)) (Msg ((fst port_dr))))))
   else (ReceiverState Rf, (receiverOut_Ar_O null null)))" |

"receiverTransitionH (ReceiverState Rf, (\<^cancel>\<open>dr\<mapsto>\<close>null)) =
  (ReceiverState Rf, (receiverOut_Ar_O null null))" |

"receiverTransitionH (ReceiverState Rt, (\<^cancel>\<open>dr\<mapsto>\<close>Msg port_dr)) =
  (if((snd port_dr)=True) then ((ReceiverState Rf, (receiverOut_Ar_O (Msg (True)) (Msg ((fst port_dr))))))
   else if((snd port_dr)=False) then ((ReceiverState Rt, (receiverOut_Ar_O (Msg (False)) null)))
   else (ReceiverState Rt, (receiverOut_Ar_O null null)))" |

"receiverTransitionH (ReceiverState Rt, (\<^cancel>\<open>dr\<mapsto>\<close>null)) =
  (ReceiverState Rt, (receiverOut_Ar_O null null))"

(* Domain *)
definition receiverDom :: "channel set" where
"receiverDom = {\<C> ''dr''}"

(* Range *)
definition receiverRan :: "channel set" where
"receiverRan = {\<C> ''ar'', \<C> ''o''}"

(* Transition function *)
fun receiverTransition :: "(ReceiverState \<times> receiverMessage tsyn sbElem) \<Rightarrow> (ReceiverState \<times> receiverMessage tsyn SB)" where
"receiverTransition (s,b) = (if (sbeDom b) = receiverDom then receiverTransitionH (s, (receiverElem_get_Dr b)) else undefined)"

(* The final automaton *)
lift_definition ReceiverAutomaton :: "(ReceiverState, receiverMessage tsyn) dAutomaton" is
"(receiverTransition, ReceiverState Rt , (receiverOut_Ar_O null null), receiverDom, receiverRan)"
  by (simp add: receiverDom_def receiverRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition ReceiverStep :: "(ReceiverState \<Rightarrow> (receiverMessage tsyn, receiverMessage tsyn) SPF)" where
"ReceiverStep = da_h ReceiverAutomaton"

(* The final SPF *)
definition ReceiverSPF :: "(receiverMessage tsyn, receiverMessage tsyn) SPF" where
"ReceiverSPF = da_H ReceiverAutomaton"


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 18:  Rf -> Rf [dr.snd=true] / {ar=true}; *)
lemma transition_0_0:
  assumes "(snd port_dr)=True"
    shows "receiverTransition ((ReceiverState Rf ), (receiverElemIn_Dr (Msg port_dr)))
         = (ReceiverState Rf, (receiverOut_Ar_O (Msg (True)) null))"
  oops

(* Line 19:  Rf -> Rt [dr.snd=false] / {ar=false, o=dr.fst}; *)
lemma transition_0_1:
  assumes "(snd port_dr)=False"
    shows "receiverTransition ((ReceiverState Rf ), (receiverElemIn_Dr (Msg port_dr)))
         = (ReceiverState Rt, (receiverOut_Ar_O (Msg (False)) (Msg ((fst port_dr)))))"
  oops

(* Line 17:  Rf -> Rf {dr==null}; *)
lemma transition_1_0:
  assumes "True"
    shows "receiverTransition ((ReceiverState Rf ), (receiverElemIn_Dr null))
         = (ReceiverState Rf, (receiverOut_Ar_O null null))"
  oops

(* Line 14:  Rt -> Rf [dr.snd=true] / {o=dr.fst, ar=true}; *)
lemma transition_2_0:
  assumes "(snd port_dr)=True"
    shows "receiverTransition ((ReceiverState Rt ), (receiverElemIn_Dr (Msg port_dr)))
         = (ReceiverState Rf, (receiverOut_Ar_O (Msg (True)) (Msg ((fst port_dr)))))"
  oops

(* Line 15:  Rt -> Rt [dr.snd=false] / {ar=false}; *)
lemma transition_2_1:
  assumes "(snd port_dr)=False"
    shows "receiverTransition ((ReceiverState Rt ), (receiverElemIn_Dr (Msg port_dr)))
         = (ReceiverState Rt, (receiverOut_Ar_O (Msg (False)) null))"
  oops

(* Line 16:  Rt -> Rt {dr==null}; *)
lemma transition_3_0:
  assumes "True"
    shows "receiverTransition ((ReceiverState Rt ), (receiverElemIn_Dr null))
         = (ReceiverState Rt, (receiverOut_Ar_O null null))"
  oops


section \<open>Step-wise lemmata for the SPF\<close>

(* Line 18:  Rf -> Rf [dr.snd=true] / {ar=true}; *)
lemma step_0_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (receiverIn_Dr (Msg port_dr))\<cdot>(ReceiverStep (ReceiverState Rf ))
         = spfConcOut (receiverOut_Ar_O (Msg (True)) null)\<cdot>(ReceiverStep (ReceiverState Rf))"
  oops

(* Line 19:  Rf -> Rt [dr.snd=false] / {ar=false, o=dr.fst}; *)
lemma step_0_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (receiverIn_Dr (Msg port_dr))\<cdot>(ReceiverStep (ReceiverState Rf ))
         = spfConcOut (receiverOut_Ar_O (Msg (False)) (Msg ((fst port_dr))))\<cdot>(ReceiverStep (ReceiverState Rt))"
  oops

(* Line 17:  Rf -> Rf {dr==null}; *)
lemma step_1_0:
  assumes "True"
    shows "spfConcIn  (receiverIn_Dr null)\<cdot>(ReceiverStep (ReceiverState Rf ))
         = spfConcOut (receiverOut_Ar_O null null)\<cdot>(ReceiverStep (ReceiverState Rf))"
  oops

(* Line 14:  Rt -> Rf [dr.snd=true] / {o=dr.fst, ar=true}; *)
lemma step_2_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (receiverIn_Dr (Msg port_dr))\<cdot>(ReceiverStep (ReceiverState Rt ))
         = spfConcOut (receiverOut_Ar_O (Msg (True)) (Msg ((fst port_dr))))\<cdot>(ReceiverStep (ReceiverState Rf))"
  oops

(* Line 15:  Rt -> Rt [dr.snd=false] / {ar=false}; *)
lemma step_2_1:
  assumes "(snd port_dr)=False"
    shows "spfConcIn  (receiverIn_Dr (Msg port_dr))\<cdot>(ReceiverStep (ReceiverState Rt ))
         = spfConcOut (receiverOut_Ar_O (Msg (False)) null)\<cdot>(ReceiverStep (ReceiverState Rt))"
  oops

(* Line 16:  Rt -> Rt {dr==null}; *)
lemma step_3_0:
  assumes "True"
    shows "spfConcIn  (receiverIn_Dr null)\<cdot>(ReceiverStep (ReceiverState Rt ))
         = spfConcOut (receiverOut_Ar_O null null)\<cdot>(ReceiverStep (ReceiverState Rt))"
  oops


end