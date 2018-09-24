(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Sep 24, 2018 5:01:53 PM by isartransformer 1.0.0
 *)
theory SenderAutomaton
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

datatype ('e::countable) senderMessage = DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderBool "bool" | DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderE "'e" | DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderPair_SenderE_SenderBool "('e\<times>bool)"

instance senderMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation senderMessage :: (countable) message
begin
  fun ctype_senderMessage :: "channel \<Rightarrow> ('e::countable) senderMessage set" where
  "ctype_senderMessage c = (
    if c = \<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_as'' then range DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderBool else
    if c = \<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_i'' then range DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderE else
    if c = \<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_ds'' then range DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderPair_SenderE_SenderBool else
    undefined)"
  instance
    by(intro_classes)
end


section \<open>Helpers to create a bundle from a single raw element\<close>

lift_definition senderElem_raw_as :: "bool \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_as'' \<mapsto> Msg (DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition senderElem_raw_i :: "'e \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_i'' \<mapsto> Msg (DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition senderElem_raw_ds :: "('e\<times>bool) \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_ds'' \<mapsto> Msg (DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderPair_SenderE_SenderBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun senderElem_as :: "bool tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElem_as (Msg port_as) = senderElem_raw_as port_as" |
"senderElem_as null = sbeNull {\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_as''}"

declare senderElem_as.simps[simp del]

definition sender_as :: "bool tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_as port_as = sbe2SB (senderElem_as port_as)"

fun senderElem_i :: "'e tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElem_i (Msg port_i) = senderElem_raw_i port_i" |
"senderElem_i null = sbeNull {\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_i''}"

declare senderElem_i.simps[simp del]

definition sender_i :: "'e tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_i port_i = sbe2SB (senderElem_i port_i)"

fun senderElem_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElem_ds (Msg port_ds) = senderElem_raw_ds port_ds" |
"senderElem_ds null = sbeNull {\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_ds''}"

declare senderElem_ds.simps[simp del]

definition sender_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_ds port_ds = sbe2SB (senderElem_ds port_ds)"

(* Create one sbElem for all input channels *)
definition senderElemIn_as_i :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElemIn_as_i port_as port_i = (senderElem_as port_as) \<plusminus> (senderElem_i port_i)"

(* Create one sbElem for all output channels *)
definition senderElemOut_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElemOut_ds port_ds = (senderElem_ds port_ds)"

(* Create one SB for all input channels *)
definition senderIn_as_i :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderIn_as_i port_as port_i = (sbe2SB (senderElemIn_as_i port_as port_i))"

(* Create one SB for all output channels *)
definition senderOut_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderOut_ds port_ds = (sbe2SB (senderElemOut_ds port_ds))"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

fun sender_list_as :: "(bool tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_list_as (x#xs) = ubConcEq (sender_as x)\<cdot>(sender_list_as xs)" |
"sender_list_as []     = ubLeast {\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_as''}"

fun sender_list_i :: "('e tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_list_i (x#xs) = ubConcEq (sender_i x)\<cdot>(sender_list_i xs)" |
"sender_list_i []     = ubLeast {\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_i''}"

fun sender_list_ds :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_list_ds (x#xs) = ubConcEq (sender_ds x)\<cdot>(sender_list_ds xs)" |
"sender_list_ds []     = ubLeast {\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_ds''}"

(* Create one SB for all input channels *)
definition senderIn_list_as_i :: "bool tsyn list \<Rightarrow> 'e tsyn list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderIn_list_as_i port_as port_i = (sender_list_as port_as) \<uplus> (sender_list_i port_i)"

(* Create one SB for all output channels *)
definition senderOut_list_ds :: "('e\<times>bool) tsyn list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderOut_list_ds port_ds = (sender_list_ds port_ds)"


section \<open>Helpers to create a bundle from a tsyn stream of elements\<close>

lift_definition DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_sender_stream_as_h :: "bool tsyn stream \<Rightarrow> ('e::countable) senderMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_as'') \<mapsto> (tsynMap (DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition sender_stream_as :: "(bool) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" is
"DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_sender_stream_as_h"
  sorry

lift_definition DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_sender_stream_i_h :: "'e tsyn stream \<Rightarrow> ('e::countable) senderMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_i'') \<mapsto> (tsynMap (DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition sender_stream_i :: "('e) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" is
"DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_sender_stream_i_h"
  sorry

lift_definition DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_sender_stream_ds_h :: "('e\<times>bool) tsyn stream \<Rightarrow> ('e::countable) senderMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_ds'') \<mapsto> (tsynMap (DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderPair_SenderE_SenderBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  apply auto
  sorry

lift_definition sender_stream_ds :: "(('e\<times>bool)) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" is
"DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_sender_stream_ds_h"
  sorry

(* Create one SB for all input channels *)
definition senderIn_stream_as_i :: "bool tsyn stream \<rightarrow> 'e tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderIn_stream_as_i = (\<Lambda>  port_as port_i. (sender_stream_as\<cdot>port_as) \<uplus> (sender_stream_i\<cdot>port_i))"

(* Create one SB for all output channels *)
definition senderOut_stream_ds :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderOut_stream_ds = (\<Lambda>  port_ds. (sender_stream_ds\<cdot>port_ds))"


section \<open>Helpers to get tsyn elements and streams from sbElems and SBs\<close>

fun senderElem_get_as :: "('e::countable) senderMessage tsyn sbElem \<Rightarrow> (bool) tsyn" where
"senderElem_get_as sbe = undefined"

lift_definition sender_get_stream_as :: "('e::countable) senderMessage tsyn SB \<rightarrow> bool tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderBool)\<cdot>(sb . (\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_as''))"
  by(simp add: cfun_def)

fun senderElem_get_i :: "('e::countable) senderMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"senderElem_get_i sbe = undefined"

lift_definition sender_get_stream_i :: "('e::countable) senderMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderE)\<cdot>(sb . (\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_i''))"
  by(simp add: cfun_def)

fun senderElem_get_ds :: "('e::countable) senderMessage tsyn sbElem \<Rightarrow> (('e\<times>bool)) tsyn" where
"senderElem_get_ds sbe = undefined"

lift_definition sender_get_stream_ds :: "('e::countable) senderMessage tsyn SB \<rightarrow> ('e\<times>bool) tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_SenderPair_SenderE_SenderBool)\<cdot>(sb . (\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_ds''))"
  by(simp add: cfun_def)



section \<open>Automaton definition\<close>

(* These are the actual states from MAA *)
datatype SenderSubstate = Sf | St

(* And these have also the variables *)
datatype 'e SenderState = SenderState SenderSubstate (* buffer = *) "'e list" (* c = *) "nat"

(* Function to get the substate *)
fun getSenderSubState :: "'e SenderState \<Rightarrow> SenderSubstate" where
"getSenderSubState (SenderState s _ _) = s"

(* Functions to get the variables *)
fun getBuffer :: "'e SenderState \<Rightarrow> 'e list" where
"getBuffer (SenderState _ var_buffer var_c) = var_buffer"

fun getC :: "'e SenderState \<Rightarrow> nat" where
"getC (SenderState _ var_buffer var_c) = var_c"

(* Helper that allows us to utilize pattern matching *)
fun senderTransitionH :: "('e SenderState \<times> (bool tsyn \<times> 'e tsyn)) \<Rightarrow> ('e SenderState \<times> ('e::countable) senderMessage tsyn SB)" where
"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)>1 \<and> port_as=False) then ((SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True)))))
   else if((size var_buffer)=1 \<and> port_as=False) then ((SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair port_i True)))))
   else if((size var_buffer)=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=True) then ((SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=True) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)>1 \<and> port_as=False) then ((SenderState St (butlast var_buffer) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True)))))
   else if((size var_buffer)=1 \<and> port_as=False) then ((SenderState St (butlast var_buffer) var_c, (senderOut_ds null)))
   else if((size var_buffer)=0) then ((SenderState Sf var_buffer var_c, (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=True) then ((SenderState Sf var_buffer (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=True) then ((SenderState Sf var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i False)))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState Sf var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState Sf var_buffer var_c, (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState Sf var_buffer var_c, (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState Sf var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) False)))))
   else (SenderState Sf var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)=0) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i True)))))
   else if((size var_buffer)>1 \<and> port_as=True) then ((SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=False) then ((SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=False) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) True)))))
   else if((size var_buffer)=1 \<and> port_as=True) then ((SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair port_i False)))))
   else (SenderState St var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>Msg port_as, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState St var_buffer var_c, (senderOut_ds null)))
   else if((size var_buffer)>1 \<and> port_as=True) then ((SenderState Sf (butlast var_buffer) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False)))))
   else if((size var_buffer)>0 \<and> var_c>0 \<and> port_as=False) then ((SenderState St var_buffer (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0 \<and> port_as=False) then ((SenderState St var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) True)))))
   else if((size var_buffer)=1 \<and> port_as=True) then ((SenderState Sf (butlast var_buffer) var_c, (senderOut_ds null)))
   else (SenderState St var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>Msg port_i)) =
  (if((size var_buffer)=0) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i True)))))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) True)))))
   else (SenderState St var_buffer var_c, (senderOut_ds null)))" |

"senderTransitionH (SenderState St var_buffer var_c, (\<^cancel>\<open>as\<mapsto>\<close>null, \<^cancel>\<open>i\<mapsto>\<close>null)) =
  (if((size var_buffer)=0) then ((SenderState St var_buffer var_c, (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c>0) then ((SenderState St var_buffer (var_c-1), (senderOut_ds null)))
   else if((size var_buffer)>0 \<and> var_c=0) then ((SenderState St var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) True)))))
   else (SenderState St var_buffer var_c, (senderOut_ds null)))"

(* Domain *)
definition senderDom :: "channel set" where
"senderDom = {\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_as'', \<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_i''}"

(* Range *)
definition senderRan :: "channel set" where
"senderRan = {\<C> ''DoNotUse_2ab8d3f31b8b462b9c9e2aac99cd809b_ds''}"

(* Transition function *)
definition senderTransition :: "('e SenderState \<times> ('e::countable) senderMessage tsyn sbElem) \<Rightarrow> ('e SenderState \<times> ('e::countable) senderMessage tsyn SB)" where
"senderTransition = (\<lambda> (s,b). (if (sbeDom b) = senderDom then senderTransitionH (s, (senderElem_get_as b, senderElem_get_i b)) else undefined))"

(* Initial state *)
definition senderInitialState :: "'e SenderState" where
"senderInitialState = SenderState St ([] ::'e list) (0::nat)"

(* Initial output *)
definition senderInitialOutput :: "('e::countable) senderMessage tsyn SB" where
"senderInitialOutput = senderOut_ds null"

(* The final automaton *)
lift_definition senderAutomaton :: "('e SenderState, ('e::countable) senderMessage tsyn) dAutomaton" is
"(senderTransition, senderInitialState, senderInitialOutput, senderDom, senderRan)"
  by (simp add: senderDom_def senderRan_def)

(* Stream processing function for each state (handy for step lemmata) *)
definition senderStep :: "('e SenderState \<Rightarrow> (('e::countable) senderMessage tsyn, ('e::countable) senderMessage tsyn) SPF)" where
"senderStep = da_h senderAutomaton"

(* The final SPF *)
definition senderSPF :: "(('e::countable) senderMessage tsyn, ('e::countable) senderMessage tsyn) SPF" where
"senderSPF = da_H (senderAutomaton::('e SenderState, ('e::countable) senderMessage tsyn) dAutomaton)"


section \<open>Lemmas for automaton definition\<close>

lemma senderautomaton_trans[simp]: "daTransition senderAutomaton = senderTransition"
  unfolding daTransition_def
  by(simp add: senderAutomaton.rep_eq)

lemma senderautomaton_initialstate[simp]: "daInitialState senderAutomaton = senderInitialState"
  unfolding daInitialState_def
  by(simp add: senderAutomaton.rep_eq)

lemma senderautomaton_initialoutput[simp]: "daInitialOutput senderAutomaton = senderInitialOutput"
  unfolding daInitialOutput_def
  by(simp add: senderAutomaton.rep_eq)

lemma senderautomaton_dom[simp]: "daDom senderAutomaton = senderDom"
  unfolding daDom_def
  by(simp add: senderAutomaton.rep_eq)

lemma senderautomaton_ran[simp]: "daRan senderAutomaton = senderRan"
  unfolding daRan_def
  by(simp add: senderAutomaton.rep_eq)


section \<open>Lemmas for single tsyn setter\<close>

lemma senderelemin_as_i_dom[simp]: "sbeDom (senderElemIn_as_i port_as port_i) = senderDom"
  sorry

lemma senderelemout_ds_dom[simp]: "sbeDom (senderElemOut_ds port_ds) = senderRan"
  sorry

lemma senderin_as_i_dom[simp]: "ubDom\<cdot>(senderIn_as_i port_as port_i) = senderDom"
  sorry

lemma senderout_ds_dom[simp]: "ubDom\<cdot>(senderOut_ds port_ds) = senderRan"
  sorry


section \<open>Lemmas for getter\<close>

subsection \<open>Identity lemmas for single sbElems\<close>

lemma senderelem_as_id[simp]: "senderElem_get_as (senderElem_as port_as) = port_as"
  sorry

lemma senderelem_i_id[simp]: "senderElem_get_i (senderElem_i port_i) = port_i"
  sorry

lemma senderelem_ds_id[simp]: "senderElem_get_ds (senderElem_ds port_ds) = port_ds"
  sorry


subsection \<open>Identity lemmas for single SBs from streams\<close>

lemma sender_stream_as_id[simp]: "sender_get_stream_as\<cdot>(sender_stream_as\<cdot>port_as) = port_as"
  sorry

lemma sender_stream_i_id[simp]: "sender_get_stream_i\<cdot>(sender_stream_i\<cdot>port_i) = port_i"
  sorry

lemma sender_stream_ds_id[simp]: "sender_get_stream_ds\<cdot>(sender_stream_ds\<cdot>port_ds) = port_ds"
  sorry


subsection \<open>Identity lemmas for input sbElems\<close>

lemma senderelemin_as_i_as_id[simp]: "senderElem_get_as (senderElemIn_as_i port_as port_i) = port_as"
  sorry

lemma senderelemin_as_i_i_id[simp]: "senderElem_get_i (senderElemIn_as_i port_as port_i) = port_i"
  sorry


subsection \<open>Identity lemmas for output sbElems\<close>

lemma senderelemout_ds_ds_id[simp]: "senderElem_get_ds (senderElemOut_ds port_ds) = port_ds"
  sorry


subsection \<open>Identity lemmas for input SBs\<close>

lemma senderin_as_i_as_id[simp]: "sender_get_stream_as\<cdot>(senderIn_as_i port_as port_i) = \<up>port_as"
  sorry

lemma senderin_as_i_i_id[simp]: "sender_get_stream_i\<cdot>(senderIn_as_i port_as port_i) = \<up>port_i"
  sorry


subsection \<open>Identity lemmas for output SBs\<close>

lemma senderout_ds_ds_id[simp]: "sender_get_stream_ds\<cdot>(senderOut_ds port_ds) = \<up>port_ds"
  sorry


subsection \<open>Identity lemmas for input SBs from lists\<close>

lemma senderin_list_as_i_as_id[simp]: "sender_get_stream_as\<cdot>(senderIn_list_as_i port_as port_i) = <port_as>"
  sorry

lemma senderin_list_as_i_i_id[simp]: "sender_get_stream_i\<cdot>(senderIn_list_as_i port_as port_i) = <port_i>"
  sorry


subsection \<open>Identity lemmas for output SBs from lists\<close>

lemma senderout_list_ds_ds_id[simp]: "sender_get_stream_ds\<cdot>(senderOut_list_ds port_ds) = <port_ds>"
  sorry


subsection \<open>Identity lemmas for input SBs from streams\<close>

lemma senderin_stream_as_i_as_id[simp]: "sender_get_stream_as\<cdot>(senderIn_stream_as_i\<cdot>port_as\<cdot>port_i) = port_as"
  sorry

lemma senderin_stream_as_i_i_id[simp]: "sender_get_stream_i\<cdot>(senderIn_stream_as_i\<cdot>port_as\<cdot>port_i) = port_i"
  sorry


subsection \<open>Identity lemmas for output SBs from streams\<close>

lemma senderout_stream_ds_ds_id[simp]: "sender_get_stream_ds\<cdot>(senderOut_stream_ds\<cdot>port_ds) = port_ds"
  sorry


section \<open>Step-wise lemmata for the transition function\<close>

(* Line 33:  Sf -> St [buffer.size()>1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma senderTransition_0_0[simp]:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 35:  Sf -> St [buffer.size()=1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderTransition_0_1[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair port_i True))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 43:  Sf -> Sf [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderTransition_0_2[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i False))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 45:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_0_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 47:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_0_4[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 34:  Sf -> St [buffer.size()>1] {as==false, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma senderTransition_1_0[simp]:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St (butlast var_buffer) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 36:  Sf -> St [buffer.size()=1] {as==false, i==null} / {buffer=buffer.butlast()}; *)
lemma senderTransition_1_1[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St (butlast var_buffer) var_c, (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 38:  Sf -> Sf [buffer.size()=0 && as!=null] {i==null}; *)
lemma senderTransition_1_2[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf var_buffer var_c, (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 40:  Sf -> Sf [buffer.size()>0 && c>0] {as==true, i==null} / {c=c-1}; *)
lemma senderTransition_1_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf var_buffer (var_c-1), (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 41:  Sf -> Sf [buffer.size()>0 && c=0] {as==true, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_1_4[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 44:  Sf -> Sf [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderTransition_2_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i False))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 46:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_2_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 48:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_2_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 37:  Sf -> Sf [buffer.size()=0] {as==null, i==null}; *)
lemma senderTransition_3_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState Sf var_buffer var_c, (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 39:  Sf -> Sf [buffer.size()>0 && c>0] {as==null, i==null}; *)
lemma senderTransition_3_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState Sf var_buffer var_c, (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 42:  Sf -> Sf [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_3_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState Sf var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 25:  St -> St [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderTransition_4_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i True))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 27:  St -> Sf [buffer.size()>1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma senderTransition_4_1[simp]:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 28:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_4_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 30:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_4_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 32:  St -> Sf [buffer.size()=1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderTransition_4_4[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair port_i False))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 17:  St -> St [buffer.size()=0 && as!=null] {i==null}; *)
lemma senderTransition_5_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St var_buffer var_c, (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 18:  St -> Sf [buffer.size()>1] {as==true, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma senderTransition_5_1[simp]:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf (butlast var_buffer) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 20:  St -> St [buffer.size()>0 && c>0] {as==false, i==null} / {c=c-1}; *)
lemma senderTransition_5_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St var_buffer (var_c-1), (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 22:  St -> St [buffer.size()>0 && c=0] {as==false, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_5_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 24:  St -> Sf [buffer.size()=1] {as==true, i==null} / {buffer=buffer.butlast()}; *)
lemma senderTransition_5_4[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf (butlast var_buffer) var_c, (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 26:  St -> St [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderTransition_6_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i True))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 29:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_6_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 31:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_6_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 19:  St -> St [buffer.size()=0] {as==null, i==null}; *)
lemma senderTransition_7_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState St var_buffer var_c, (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 21:  St -> St [buffer.size()>0 && c>0] {as==null, i==null} / {c=c-1}; *)
lemma senderTransition_7_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState St var_buffer (var_c-1), (senderOut_ds null))"
  apply(simp add: senderTransition_def)
  sorry

(* Line 23:  St -> St [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_7_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState St var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  apply(simp add: senderTransition_def)
  sorry


section \<open>Step-wise lemmata for the SPF\<close>

(* Convert the SPF to step notation *)
lemma senderSpf2Step: "senderSPF = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St ([] ::'e::countable list) (0::nat)))"
  sorry

(* Line 33:  Sf -> St [buffer.size()>1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma senderStep_0_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True)))\<cdot>(senderStep (SenderState St (prepend (butlast var_buffer) port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 35:  Sf -> St [buffer.size()=1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderStep_0_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i True)))\<cdot>(senderStep (SenderState St (prepend (butlast var_buffer) port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 43:  Sf -> Sf [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderStep_0_2:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i False)))\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 45:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderStep_0_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 47:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderStep_0_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) False)))\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 34:  Sf -> St [buffer.size()>1] {as==false, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma senderStep_1_0:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True)))\<cdot>(senderStep (SenderState St (butlast var_buffer) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 36:  Sf -> St [buffer.size()=1] {as==false, i==null} / {buffer=buffer.butlast()}; *)
lemma senderStep_1_1:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St (butlast var_buffer) var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 38:  Sf -> Sf [buffer.size()=0 && as!=null] {i==null}; *)
lemma senderStep_1_2:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 40:  Sf -> Sf [buffer.size()>0 && c>0] {as==true, i==null} / {c=c-1}; *)
lemma senderStep_1_3:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf var_buffer (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 41:  Sf -> Sf [buffer.size()>0 && c=0] {as==true, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderStep_1_4:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) False)))\<cdot>(senderStep (SenderState Sf var_buffer 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 44:  Sf -> Sf [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderStep_2_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i False)))\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 46:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderStep_2_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 48:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderStep_2_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) False)))\<cdot>(senderStep (SenderState Sf (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 37:  Sf -> Sf [buffer.size()=0] {as==null, i==null}; *)
lemma senderStep_3_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 39:  Sf -> Sf [buffer.size()>0 && c>0] {as==null, i==null}; *)
lemma senderStep_3_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 42:  Sf -> Sf [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderStep_3_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState Sf var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) False)))\<cdot>(senderStep (SenderState Sf var_buffer 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 25:  St -> St [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderStep_4_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i True)))\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 27:  St -> Sf [buffer.size()>1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma senderStep_4_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False)))\<cdot>(senderStep (SenderState Sf (prepend (butlast var_buffer) port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 28:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderStep_4_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 30:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderStep_4_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) True)))\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 32:  St -> Sf [buffer.size()=1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderStep_4_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i False)))\<cdot>(senderStep (SenderState Sf (prepend (butlast var_buffer) port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 17:  St -> St [buffer.size()=0 && as!=null] {i==null}; *)
lemma senderStep_5_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St var_buffer var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 18:  St -> Sf [buffer.size()>1] {as==true, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma senderStep_5_1:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False)))\<cdot>(senderStep (SenderState Sf (butlast var_buffer) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 20:  St -> St [buffer.size()>0 && c>0] {as==false, i==null} / {c=c-1}; *)
lemma senderStep_5_2:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St var_buffer (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 22:  St -> St [buffer.size()>0 && c=0] {as==false, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderStep_5_3:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) True)))\<cdot>(senderStep (SenderState St var_buffer 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 24:  St -> Sf [buffer.size()=1] {as==true, i==null} / {buffer=buffer.butlast()}; *)
lemma senderStep_5_4:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "spfConcIn  (senderIn_as_i (Msg port_as) null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState Sf (butlast var_buffer) var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 26:  St -> St [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderStep_6_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair port_i True)))\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 29:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderStep_6_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 31:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderStep_6_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_as_i null (Msg port_i))\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) True)))\<cdot>(senderStep (SenderState St (prepend var_buffer port_i) 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 19:  St -> St [buffer.size()=0] {as==null, i==null}; *)
lemma senderStep_7_0:
  assumes "(size var_buffer)=0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St var_buffer var_c))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 21:  St -> St [buffer.size()>0 && c>0] {as==null, i==null} / {c=c-1}; *)
lemma senderStep_7_1:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St var_buffer (var_c-1)))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)

(* Line 23:  St -> St [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderStep_7_2:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "spfConcIn  (senderIn_as_i null null)\<cdot>(senderStep (SenderState St var_buffer var_c))
         = spfConcOut (senderOut_ds (Msg (Pair (last var_buffer) True)))\<cdot>(senderStep (SenderState St var_buffer 3))"
  apply(simp add: senderStep_def senderIn_as_i_def)
  apply(rule da_h_stepI)
  using assms by(auto simp add: daNextState_def daNextOutput_def assms)


end