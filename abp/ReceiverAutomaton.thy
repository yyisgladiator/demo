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
    undefined)" (* SWS: undefined is better, otherwise "time" is allowed on the other channels *)
    instance
    by(intro_classes)
end


section \<open>Helpers to create a bundle from a single raw element\<close>

(* SWS: I think it is better to write the channel-name excatly like in the MAA-Model, so "dr" instead of "Dr" *)
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
(* SWS: Remove from simps *)

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

(* SWS: use "definition" as default instead of "fun". Because "fun" adds the stuff to the simplifier.
      If you need rekursion still fun *)
definition receiverElemIn_Dr :: "(nat\<times>bool) tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
"receiverElemIn_Dr port_dr = (receiverElem_Dr port_dr)"

(* Create one sbElem for all output channels *)
definition receiverElemOut_Ar_O :: "bool tsyn \<Rightarrow> nat tsyn \<Rightarrow> receiverMessage tsyn sbElem" where
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
(* "definition" instead of "fun" *)
fun receiverIn_list_Dr :: "(nat\<times>bool) tsyn list \<Rightarrow> receiverMessage tsyn SB" where
"receiverIn_list_Dr port_dr = (receiver_list_Dr port_dr)"

(* Create one SB for all output channels *)
fun receiverOut_list_Ar_O :: "bool tsyn list \<Rightarrow> nat tsyn list \<Rightarrow> receiverMessage tsyn SB" where
"receiverOut_list_Ar_O port_ar port_o = (receiver_list_Ar port_ar) \<uplus> (receiver_list_O port_o)"


section \<open>Helpers to create a bundle from a tsyn stream of elements\<close>

(* SWS: Setter-helper. should be invisible. Could also be done in one definition but then we cannot use lift_definition *)
lift_definition receiver_stream_Dr_h :: "((nat\<times>bool)) tsyn stream \<Rightarrow> receiverMessage tsyn SB" is
"\<lambda> s. [(\<C> ''dr'') \<mapsto> (tsynMap (ReceiverPair_ReceiverNat_ReceiverBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry 
(* SWS: letzter Teil des Beweises braucht einen allgemeinen Beweis damit das autogenerieren nicht zu komplex wird. 
     Kommt später, erstmal sorry *)

(* SWS: this is a general stuff, should go to prelude / not autogenerated *)
setup_lifting type_definition_cfun

lift_definition receiver_stream_Dr :: "((nat\<times>bool)) tsyn stream \<rightarrow> receiverMessage tsyn SB" is
"receiver_stream_Dr_h"
  sorry (* SWS: No fucking clue how to proof this ... *)


definition receiver_stream_Ar :: "(bool) tsyn stream \<rightarrow> receiverMessage tsyn SB" where
"receiver_stream_Ar = undefined"  (* SWS: Analog zu oben, habs schonmal cont gemacht um die multi-parameter zu testen *)

definition receiver_stream_O :: "(nat) tsyn stream \<rightarrow> receiverMessage tsyn SB" where
"receiver_stream_O = undefined"

(* Create one SB for all input channels *)
definition receiverIn_stream_Dr :: "(nat\<times>bool) tsyn stream \<rightarrow> receiverMessage tsyn SB" where
"receiverIn_stream_Dr = (\<Lambda> port_dr. receiver_stream_Dr\<cdot>port_dr)"
  
(* Create one SB for all output channels *)
(* SWS: Ich würde hier gerne lift_definition verewnden, aber das erzeugt RICHTIG hässliche beweise bei mehreren parametern *)
(* SWS: vllt muss man dafür noch extra cont-lemma generieren :/ *)
definition receiverOut_stream_Ar_O :: "bool tsyn stream \<rightarrow> nat tsyn stream \<rightarrow> receiverMessage tsyn SB" where
"receiverOut_stream_Ar_O  = (\<Lambda> port_ar port_o. (receiver_stream_Ar\<cdot>port_ar) \<uplus> (receiver_stream_O\<cdot>port_o))"


section \<open>Helpers to get tsyn elements and streams from sbElems and SBs\<close>


fun receiverElem_get_Dr :: "receiverMessage tsyn sbElem \<Rightarrow> ((nat\<times>bool)) tsyn" where
"receiverElem_get_Dr sbe = undefined" (* SWS: das braucht noch eine allgemein definition über "tsyn" *)

(* SWS: Das ist kein Elem, renaming zu "receiver_get_stream_Dr" *)
lift_definition receiverElem_get_stream_Dr :: "receiverMessage tsyn SB \<rightarrow> ((nat\<times>bool)) tsyn stream" is
"\<lambda>sb. tsynMap (inv ReceiverPair_ReceiverNat_ReceiverBool)\<cdot>(sb . (\<C> ''dr''))"
  by(simp add: cfun_def)  (* SWS: das lief doch schön! *)

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
definition receiverTransition :: "(ReceiverState \<times> receiverMessage tsyn sbElem) \<Rightarrow> (ReceiverState \<times> receiverMessage tsyn SB)" where
"receiverTransition  = (\<lambda> (s,b). (if (sbeDom b) = receiverDom then receiverTransitionH (s, (receiverElem_get_Dr b)) else undefined))"

(* The final automaton *)
(* SWS: kleiner Anfangsbuchstabe wie überall sonst auch *)
lift_definition ReceiverAutomaton :: "(ReceiverState, receiverMessage tsyn) dAutomaton" is
"(receiverTransition, ReceiverState Rt , (receiverOut_Ar_O null null), receiverDom, receiverRan)"
  by (simp add: receiverDom_def receiverRan_def)

(* SWS: kleiner Anfangsbuchstabe wie überall sonst auch *)
(* Stream processing function for each state (handy for step lemmata) *)
definition ReceiverStep :: "(ReceiverState \<Rightarrow> (receiverMessage tsyn, receiverMessage tsyn) SPF)" where
"ReceiverStep = da_h ReceiverAutomaton"

(* The final SPF *)
(* SWS: kleiner Anfangsbuchstabe wie überall sonst auch *)
definition ReceiverSPF :: "(receiverMessage tsyn, receiverMessage tsyn) SPF" where
"ReceiverSPF = da_H ReceiverAutomaton"



(* SWS: this is unrelated from the automaton. Can be before the entire automaton definition *)
section \<open>Lemma over the Datatype-Definitions\<close>

lemma receiverelemin_dom[simp]: "sbeDom (receiverElemIn_Dr port_dr) = receiverDom"
  sorry (* SWS: Analog für ran *)

lemma receiverin_dom[simp]: "ubDom\<cdot>(receiverIn_Dr port_dr) = receiverDom"
  sorry (* SWS: Analog für ran *)

lemma receiverelem_dr_id[simp]: "receiverElem_get_Dr (receiverElem_Dr port_dr) = port_dr"
  sorry (* SWS: Analog die gleichen "get von set" lemma über Bundle *)

lemma receiverelemin_dr_id[simp]: "receiverElem_get_Dr (receiverElemIn_Dr port_dr) = port_dr"
  sorry (* SWS: Analog die gleichen "get von set" lemma über Bundle *)



(* SWS: Very general lemma over the definition *)

lemma receiveraut_trans[simp]: "daTransition ReceiverAutomaton = receiverTransition"
  sorry
lemma receiveraut_dom [simp]: "daDom ReceiverAutomaton = receiverDom"
  sorry
(* SWS: Das gleiche für alle Elemente des Tupels/für alle "daXXXX" definitionen *)


section \<open>Step-wise lemmata for the transition function\<close>

(* SWS: automaton-name in die lemma *)
(* Line 18:  Rf -> Rf [dr.snd=true] / {ar=true}; *)
lemma transition_0_0 [simp]:
  assumes "(snd port_dr)=True"
    shows "receiverTransition ((ReceiverState Rf ), (receiverElemIn_Dr (Msg port_dr)))
         = (ReceiverState Rf, (receiverOut_Ar_O (Msg (True)) null))"
  apply(simp add: receiverTransition_def) (* SWS: i will continue to proof this after more lemma/definitions are there *)
  sorry

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

(* SWS: I am moving this to dAutomaton *)
lemma da_h_stepI: assumes "sbeDom sbe = daDom da"
  assumes "(daNextOutput da s sbe)  = out"
      and "(daNextState da s sbe) = nextState"
  shows "spfConcIn (sbe2SB sbe)\<cdot>(da_h da s) = spfConcOut out\<cdot>((da_h da nextState))"
  by (metis (no_types) assms da_h_dom da_h_final_h3 spfConcIn_dom spfConcIn_step spfConcOut_dom spf_eq)



(* Line 18:  Rf -> Rf [dr.snd=true] / {ar=true}; *)
lemma step_0_0:
  assumes "(snd port_dr)=True"
    shows "spfConcIn  (receiverIn_Dr (Msg port_dr))\<cdot>(ReceiverStep (ReceiverState Rf ))
         = spfConcOut (receiverOut_Ar_O (Msg (True)) null)\<cdot>(ReceiverStep (ReceiverState Rf))"
  apply(simp add: ReceiverStep_def)
  apply(rule da_h_stepI)
  by(auto simp add: daNextState_def daNextOutput_def assms)
  (* SWS: Bäm! *)

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



(* SWS: one more lemma :D *)
lemma "ReceiverSPF = spfConcOut (receiverOut_Ar_O null null)\<cdot>(ReceiverStep (ReceiverState Rt))"
  sorry

end