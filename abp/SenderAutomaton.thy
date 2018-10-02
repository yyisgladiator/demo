(*
 * DO NOT MODIFY!
 * This file was generated from Sender.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 1.0.0
 *)
theory SenderAutomaton
  imports bundle.tsynBundle automat.dAutomaton

begin


(* Helper for easier generation *)
fun prepend :: "'a::type list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"prepend xs x = x#xs"


section \<open>Datatype definition\<close>

datatype ('e::countable) senderMessage = DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderBool "bool" | DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderE "'e" | DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderPair_E_Bool "('e\<times>bool)"

instance senderMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation senderMessage :: (countable) message
begin
  fun ctype_senderMessage :: "channel \<Rightarrow> ('e::countable) senderMessage set" where
  "ctype_senderMessage c = (
    if c = \<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_as'' then range DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderBool else
    if c = \<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_i'' then range DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderE else
    if c = \<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_ds'' then range DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderPair_E_Bool else
    undefined)"
  instance
    by(intro_classes)
end


section \<open>Domain and range\<close>

definition senderDom :: "channel set" where
"senderDom = {\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_as'', \<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_i''}"

definition senderRan :: "channel set" where
"senderRan = {\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_ds''}"


section \<open>Helpers to create a bundle from a single raw element\<close>

lift_definition senderElem_raw_as :: "bool \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_as'' \<mapsto> Msg (DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition senderElem_raw_i :: "'e \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_i'' \<mapsto> Msg (DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition senderElem_raw_ds :: "('e\<times>bool) \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_ds'' \<mapsto> Msg (DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderPair_E_Bool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

fun senderElem_as :: "bool tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElem_as (Msg port_as) = senderElem_raw_as port_as" |
"senderElem_as null = sbeNull {\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_as''}"

declare senderElem_as.simps[simp del]

definition sender_as :: "bool tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_as port_as = sbe2SB (senderElem_as port_as)"

fun senderElem_i :: "'e tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElem_i (Msg port_i) = senderElem_raw_i port_i" |
"senderElem_i null = sbeNull {\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_i''}"

declare senderElem_i.simps[simp del]

definition sender_i :: "'e tsyn \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_i port_i = sbe2SB (senderElem_i port_i)"

fun senderElem_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) senderMessage tsyn sbElem" where
"senderElem_ds (Msg port_ds) = senderElem_raw_ds port_ds" |
"senderElem_ds null = sbeNull {\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_ds''}"

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
"sender_list_as []     = ubLeast {\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_as''}"

declare sender_list_as.simps[simp del]

fun sender_list_i :: "('e tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_list_i (x#xs) = ubConcEq (sender_i x)\<cdot>(sender_list_i xs)" |
"sender_list_i []     = ubLeast {\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_i''}"

declare sender_list_i.simps[simp del]

fun sender_list_ds :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"sender_list_ds (x#xs) = ubConcEq (sender_ds x)\<cdot>(sender_list_ds xs)" |
"sender_list_ds []     = ubLeast {\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_ds''}"

declare sender_list_ds.simps[simp del]

(* Create one SB for all input channels *)
fun senderIn_list_as_i :: "(bool tsyn\<times>'e tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderIn_list_as_i ((port_as,port_i)#xs) = ubConcEq (senderIn_as_i port_as port_i)\<cdot>(senderIn_list_as_i xs)" |
"senderIn_list_as_i [] = ubLeast senderDom"

(* Create one SB for all output channels *)
fun senderOut_list_ds :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderOut_list_ds ((port_ds)#xs) = ubConcEq (senderOut_ds port_ds)\<cdot>(senderOut_list_ds xs)" |
"senderOut_list_ds [] = ubLeast senderRan"


section \<open>Helpers to create a bundle from a tsyn stream of elements\<close>

lift_definition DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_as_h :: "bool tsyn stream \<Rightarrow> ('e::countable) senderMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_as'') \<mapsto> (tsynMap (DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

lift_definition sender_stream_as :: "(bool) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" is
"DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_as_h"
  apply(auto simp add: cfun_def DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_as_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_as_h.rep_eq ubrep_well)

lift_definition DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_i_h :: "'e tsyn stream \<Rightarrow> ('e::countable) senderMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_i'') \<mapsto> (tsynMap (DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

lift_definition sender_stream_i :: "('e) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" is
"DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_i_h"
  apply(auto simp add: cfun_def DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_i_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_i_h.rep_eq ubrep_well)

lift_definition DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_ds_h :: "('e\<times>bool) tsyn stream \<Rightarrow> ('e::countable) senderMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_ds'') \<mapsto> (tsynMap (DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderPair_E_Bool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

lift_definition sender_stream_ds :: "(('e\<times>bool)) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" is
"DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_ds_h"
  apply(auto simp add: cfun_def DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_ds_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_d60d54060b9d448ea60e06d4478b7275_sender_stream_ds_h.rep_eq ubrep_well)

(* Create one SB for all input channels *)
definition senderIn_stream_as_i :: "bool tsyn stream \<rightarrow> 'e tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderIn_stream_as_i = (\<Lambda>  port_as port_i. (sender_stream_as\<cdot>port_as) \<uplus> (sender_stream_i\<cdot>port_i))"

(* Create one SB for all output channels *)
definition senderOut_stream_ds :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) senderMessage tsyn SB" where
"senderOut_stream_ds = (\<Lambda>  port_ds. (sender_stream_ds\<cdot>port_ds))"


section \<open>Helpers to get tsyn elements and streams from sbElems and SBs\<close>

definition senderElem_get_as :: "('e::countable) senderMessage tsyn sbElem \<Rightarrow> (bool) tsyn" where
"senderElem_get_as sbe = tsynApplyElem (inv DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderBool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_as''))"

lift_definition sender_get_stream_as :: "('e::countable) senderMessage tsyn SB \<rightarrow> bool tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderBool)\<cdot>(sb . (\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_as''))"
  by(simp add: cfun_def)

definition senderElem_get_i :: "('e::countable) senderMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"senderElem_get_i sbe = tsynApplyElem (inv DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_i''))"

lift_definition sender_get_stream_i :: "('e::countable) senderMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderE)\<cdot>(sb . (\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_i''))"
  by(simp add: cfun_def)

definition senderElem_get_ds :: "('e::countable) senderMessage tsyn sbElem \<Rightarrow> (('e\<times>bool)) tsyn" where
"senderElem_get_ds sbe = tsynApplyElem (inv DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderPair_E_Bool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_ds''))"

lift_definition sender_get_stream_ds :: "('e::countable) senderMessage tsyn SB \<rightarrow> ('e\<times>bool) tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_d60d54060b9d448ea60e06d4478b7275_SenderPair_E_Bool)\<cdot>(sb . (\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_ds''))"
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

lemma senderelem_as_dom[simp]: "sbeDom (senderElem_as x) = {\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_as''}"
  apply(cases x)
  apply(simp add: senderElem_as.simps sbeDom_def senderElem_raw_as.rep_eq)
  by(simp add: senderElem_as.simps)

lemma senderelem_i_dom[simp]: "sbeDom (senderElem_i x) = {\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_i''}"
  apply(cases x)
  apply(simp add: senderElem_i.simps sbeDom_def senderElem_raw_i.rep_eq)
  by(simp add: senderElem_i.simps)

lemma senderelem_ds_dom[simp]: "sbeDom (senderElem_ds x) = {\<C> ''DoNotUse_d60d54060b9d448ea60e06d4478b7275_ds''}"
  apply(cases x)
  apply(simp add: senderElem_ds.simps sbeDom_def senderElem_raw_ds.rep_eq)
  by(simp add: senderElem_ds.simps)

lemma senderelemin_as_i_dom[simp]: "sbeDom (senderElemIn_as_i port_as port_i) = senderDom"
  by(auto simp add: senderElemIn_as_i_def senderDom_def)

lemma senderelemout_ds_dom[simp]: "sbeDom (senderElemOut_ds port_ds) = senderRan"
  by(auto simp add: senderElemOut_ds_def senderRan_def)

lemma senderin_as_i_dom[simp]: "ubDom\<cdot>(senderIn_as_i port_as port_i) = senderDom"
  by(simp add: senderIn_as_i_def)

lemma senderout_ds_dom[simp]: "ubDom\<cdot>(senderOut_ds port_ds) = senderRan"
  by(simp add: senderOut_ds_def)


section \<open>Lemmas for getter\<close>

subsection \<open>Identity lemmas for single sbElems\<close>

lemma senderelem_as_id[simp]: "senderElem_get_as (senderElem_as x) = x"
  apply(cases x)
  apply(auto simp add: senderElem_as.simps)
  unfolding senderElem_get_as_def senderElem_raw_as.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI senderMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma senderelem_i_id[simp]: "senderElem_get_i (senderElem_i x) = x"
  apply(cases x)
  apply(auto simp add: senderElem_i.simps)
  unfolding senderElem_get_i_def senderElem_raw_i.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI senderMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma senderelem_ds_id[simp]: "senderElem_get_ds (senderElem_ds x) = x"
  apply(cases x)
  apply(auto simp add: senderElem_ds.simps)
  unfolding senderElem_get_ds_def senderElem_raw_ds.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI senderMessage.inject)
  by(simp add: sbeNull.rep_eq)


subsection \<open>Identity lemmas for single SBs from streams\<close>

lemma sender_stream_as_id[simp]: "sender_get_stream_as\<cdot>(sender_stream_as\<cdot>x) = x"
  sorry

lemma sender_stream_i_id[simp]: "sender_get_stream_i\<cdot>(sender_stream_i\<cdot>x) = x"
  sorry

lemma sender_stream_ds_id[simp]: "sender_get_stream_ds\<cdot>(sender_stream_ds\<cdot>x) = x"
  sorry


subsection \<open>Identity lemmas for input sbElems\<close>

lemma senderelemin_as_i_as_id[simp]: "senderElem_get_as (senderElemIn_as_i port_as port_i) = port_as"
  apply(simp add: senderElemIn_as_i_def senderElem_get_as_def)
  by(metis senderElem_get_as_def senderelem_as_id)

lemma senderelemin_as_i_i_id[simp]: "senderElem_get_i (senderElemIn_as_i port_as port_i) = port_i"
  apply(simp add: senderElemIn_as_i_def senderElem_get_i_def)
  by(metis senderElem_get_i_def senderelem_i_id)


subsection \<open>Identity lemmas for output sbElems\<close>

lemma senderelemout_ds_ds_id[simp]: "senderElem_get_ds (senderElemOut_ds port_ds) = port_ds"
  apply(simp add: senderElemOut_ds_def senderElem_get_ds_def)
  by(metis senderElem_get_ds_def senderelem_ds_id)


subsection \<open>Identity lemmas for input SBs\<close>

lemma senderin_as_i_as_id[simp]: "sender_get_stream_as\<cdot>(senderIn_as_i port_as port_i) = \<up>port_as"
  apply(simp add: sender_get_stream_as_def senderIn_as_i_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: senderDom_def senderElemIn_as_i_def)
  apply(cases port_as)
  apply(auto simp add: senderElem_as.simps)
  unfolding senderElem_get_as_def senderElem_raw_as.rep_eq
  apply auto
  (* TODO not working for SenderAutomaton *)
  (*apply (meson f_inv_into_f rangeI senderMessage.inject(1))
  by(simp add: sbeNull.rep_eq)*)
  sorry

lemma senderin_as_i_i_id[simp]: "sender_get_stream_i\<cdot>(senderIn_as_i port_as port_i) = \<up>port_i"
  apply(simp add: sender_get_stream_i_def senderIn_as_i_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: senderDom_def senderElemIn_as_i_def)
  apply(cases port_i)
  apply(auto simp add: senderElem_i.simps)
  unfolding senderElem_get_i_def senderElem_raw_i.rep_eq
  apply auto
  (* TODO not working for SenderAutomaton *)
  (*apply (meson f_inv_into_f rangeI senderMessage.inject(1))
  by(simp add: sbeNull.rep_eq)*)
  sorry


subsection \<open>Identity lemmas for output SBs\<close>

lemma senderout_ds_ds_id[simp]: "sender_get_stream_ds\<cdot>(senderOut_ds port_ds) = \<up>port_ds"
  apply(simp add: sender_get_stream_ds_def senderOut_ds_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: senderDom_def senderElemOut_ds_def)
  apply(cases port_ds)
  apply(auto simp add: senderElem_ds.simps)
  unfolding senderElem_get_ds_def senderElem_raw_ds.rep_eq
  apply auto
  (* TODO not working for SenderAutomaton *)
  (*apply (meson f_inv_into_f rangeI senderMessage.inject(1))
  by(simp add: sbeNull.rep_eq)*)
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
  using assms by(auto simp add: senderTransition_def assms)

(* Line 35:  Sf -> St [buffer.size()=1 && i!=null] {as==false} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderTransition_0_1[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair port_i True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 43:  Sf -> Sf [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderTransition_0_2[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 45:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_0_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 47:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==true} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_0_4[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 34:  Sf -> St [buffer.size()>1] {as==false, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),true)}; *)
lemma senderTransition_1_0[simp]:
  assumes "(size var_buffer)>1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St (butlast var_buffer) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 36:  Sf -> St [buffer.size()=1] {as==false, i==null} / {buffer=buffer.butlast()}; *)
lemma senderTransition_1_1[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=False"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St (butlast var_buffer) var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 38:  Sf -> Sf [buffer.size()=0 && as!=null] {i==null}; *)
lemma senderTransition_1_2[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf var_buffer var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 40:  Sf -> Sf [buffer.size()>0 && c>0] {as==true, i==null} / {c=c-1}; *)
lemma senderTransition_1_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf var_buffer (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 41:  Sf -> Sf [buffer.size()>0 && c=0] {as==true, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_1_4[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=True"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 44:  Sf -> Sf [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderTransition_2_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 46:  Sf -> Sf [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_2_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 48:  Sf -> Sf [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_2_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState Sf (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 37:  Sf -> Sf [buffer.size()=0] {as==null, i==null}; *)
lemma senderTransition_3_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState Sf var_buffer var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 39:  Sf -> Sf [buffer.size()>0 && c>0] {as==null, i==null}; *)
lemma senderTransition_3_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState Sf var_buffer var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 42:  Sf -> Sf [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),false)}; *)
lemma senderTransition_3_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState Sf var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState Sf var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 25:  St -> St [buffer.size()=0 && as!=null && i!=null] / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderTransition_4_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 27:  St -> Sf [buffer.size()>1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma senderTransition_4_1[simp]:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 28:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_4_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 30:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==false} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_4_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 32:  St -> Sf [buffer.size()=1 && i!=null] {as==true} / {buffer=buffer.butlast().prepend(i), c=3, ds=new Pair<>(i,false)}; *)
lemma senderTransition_4_4[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) (Msg port_i)))
         = (SenderState Sf (prepend (butlast var_buffer) port_i) 3, (senderOut_ds (Msg (Pair port_i False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 17:  St -> St [buffer.size()=0 && as!=null] {i==null}; *)
lemma senderTransition_5_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St var_buffer var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 18:  St -> Sf [buffer.size()>1] {as==true, i==null} / {buffer=buffer.butlast(), c=3, ds=new Pair<>(buffer.butlast().last(),false)}; *)
lemma senderTransition_5_1[simp]:
  assumes "(size var_buffer)>1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf (butlast var_buffer) 3, (senderOut_ds (Msg (Pair (last (butlast var_buffer)) False))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 20:  St -> St [buffer.size()>0 && c>0] {as==false, i==null} / {c=c-1}; *)
lemma senderTransition_5_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St var_buffer (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 22:  St -> St [buffer.size()>0 && c=0] {as==false, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_5_3[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0 \<and> port_as=False"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState St var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 24:  St -> Sf [buffer.size()=1] {as==true, i==null} / {buffer=buffer.butlast()}; *)
lemma senderTransition_5_4[simp]:
  assumes "(size var_buffer)=1 \<and> port_as=True"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i (Msg port_as) null))
         = (SenderState Sf (butlast var_buffer) var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 26:  St -> St [buffer.size()=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(i,true)}; *)
lemma senderTransition_6_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair port_i True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 29:  St -> St [buffer.size()>0 && c>0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=c-1}; *)
lemma senderTransition_6_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 31:  St -> St [buffer.size()>0 && c=0 && i!=null] {as==null} / {buffer=buffer.prepend(i), c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_6_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null (Msg port_i)))
         = (SenderState St (prepend var_buffer port_i) 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 19:  St -> St [buffer.size()=0] {as==null, i==null}; *)
lemma senderTransition_7_0[simp]:
  assumes "(size var_buffer)=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState St var_buffer var_c, (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 21:  St -> St [buffer.size()>0 && c>0] {as==null, i==null} / {c=c-1}; *)
lemma senderTransition_7_1[simp]:
  assumes "(size var_buffer)>0 \<and> var_c>0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState St var_buffer (var_c-1), (senderOut_ds null))"
  using assms by(auto simp add: senderTransition_def assms)

(* Line 23:  St -> St [buffer.size()>0 && c=0] {as==null, i==null} / {c=3, ds=new Pair<>(buffer.last(),true)}; *)
lemma senderTransition_7_2[simp]:
  assumes "(size var_buffer)>0 \<and> var_c=0"
    shows "senderTransition ((SenderState St var_buffer var_c), (senderElemIn_as_i null null))
         = (SenderState St var_buffer 3, (senderOut_ds (Msg (Pair (last var_buffer) True))))"
  using assms by(auto simp add: senderTransition_def assms)


section \<open>Step-wise lemmata for the SPF\<close>

(* Convert the SPF to step notation *)
lemma senderSpf2Step: "senderSPF = spfConcOut (senderOut_ds null)\<cdot>(senderStep (SenderState St ([] ::'e::countable list) (0::nat)))"
  by(simp add: senderSPF_def da_H_def senderInitialOutput_def senderInitialState_def senderStep_def)

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