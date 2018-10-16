(*
 * DO NOT MODIFY!
 * This file was generated from NoMediumABP.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 16, 2018 10:17:27 PM by isartransformer 3.1.0
 *)
theory NoMediumABPDatatype
  imports bundle.SBElem

begin


default_sort type


section \<open>Datatype\<close>

subsection \<open>Definition\<close>

datatype ('e::countable) noMediumABPMessage = DoNotUse_555251_NoMediumABPE "'e" | DoNotUse_555251_NoMediumABPBool "bool" | DoNotUse_555251_NoMediumABPPair_E_Bool "('e\<times>bool)"

instance noMediumABPMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation noMediumABPMessage :: (countable) message
begin
  fun ctype_noMediumABPMessage :: "channel \<Rightarrow> ('e::countable) noMediumABPMessage set" where
  "ctype_noMediumABPMessage c = (
    if c = \<C> ''DoNotUse_555251_receiver_o__o'' then range DoNotUse_555251_NoMediumABPE else
    if c = \<C> ''DoNotUse_555251_i__sender_i'' then range DoNotUse_555251_NoMediumABPE else
    if c = \<C> ''DoNotUse_555251_sender_ds__receiver_dr'' then range DoNotUse_555251_NoMediumABPPair_E_Bool else
    if c = \<C> ''DoNotUse_555251_receiver_ar__sender_as'' then range DoNotUse_555251_NoMediumABPBool else
    undefined)"
  instance
    by(intro_classes)
end


subsection \<open>Domain and Range\<close>

definition noMediumABPDom :: "channel set" where
"noMediumABPDom = {\<C> ''DoNotUse_555251_i__sender_i''}"

definition noMediumABPRan :: "channel set" where
"noMediumABPRan = {\<C> ''DoNotUse_555251_receiver_o__o''}"

(* sender *)
definition noMediumABPSenderDom :: "channel set" where
"noMediumABPSenderDom = {\<C> ''DoNotUse_555251_receiver_ar__sender_as'', \<C> ''DoNotUse_555251_i__sender_i''}"

definition noMediumABPSenderRan :: "channel set" where
"noMediumABPSenderRan = {\<C> ''DoNotUse_555251_sender_ds__receiver_dr''}"

(* receiver *)
definition noMediumABPReceiverDom :: "channel set" where
"noMediumABPReceiverDom = {\<C> ''DoNotUse_555251_sender_ds__receiver_dr''}"

definition noMediumABPReceiverRan :: "channel set" where
"noMediumABPReceiverRan = {\<C> ''DoNotUse_555251_receiver_ar__sender_as'', \<C> ''DoNotUse_555251_receiver_o__o''}"


section \<open>Setter\<close>

subsection \<open>type to sbElem\<close>

(* Do not use this, use noMediumABPReceiverElemOut_ar_o or noMediumABPElemOut_o instead *)
lift_definition noMediumABPElem_raw_receiver_o__o :: "'e \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_555251_receiver_o__o'' \<mapsto> Msg (DoNotUse_555251_NoMediumABPE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use noMediumABPElemIn_i or noMediumABPSenderElemIn_as_i instead *)
lift_definition noMediumABPElem_raw_i__sender_i :: "'e \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_555251_i__sender_i'' \<mapsto> Msg (DoNotUse_555251_NoMediumABPE x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use noMediumABPSenderElemOut_ds or noMediumABPReceiverElemIn_dr instead *)
lift_definition noMediumABPElem_raw_sender_ds__receiver_dr :: "('e\<times>bool) \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_555251_sender_ds__receiver_dr'' \<mapsto> Msg (DoNotUse_555251_NoMediumABPPair_E_Bool x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp

(* Do not use this, use noMediumABPReceiverElemOut_ar_o or noMediumABPSenderElemIn_as_i instead *)
lift_definition noMediumABPElem_raw_receiver_ar__sender_as :: "bool \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_555251_receiver_ar__sender_as'' \<mapsto> Msg (DoNotUse_555251_NoMediumABPBool x)]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by simp


subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use noMediumABPReceiverElemOut_ar_o or noMediumABPElemOut_o instead *)
fun noMediumABPElem_receiver_o__o :: "'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" where
"noMediumABPElem_receiver_o__o (Msg receiver_port_o__port_o) = noMediumABPElem_raw_receiver_o__o receiver_port_o__port_o" |
"noMediumABPElem_receiver_o__o null = sbeNull {\<C> ''DoNotUse_555251_receiver_o__o''}"

(* Do not use this, use noMediumABPElemIn_i or noMediumABPSenderElemIn_as_i instead *)
fun noMediumABPElem_i__sender_i :: "'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" where
"noMediumABPElem_i__sender_i (Msg port_i__sender_port_i) = noMediumABPElem_raw_i__sender_i port_i__sender_port_i" |
"noMediumABPElem_i__sender_i null = sbeNull {\<C> ''DoNotUse_555251_i__sender_i''}"

(* Do not use this, use noMediumABPSenderElemOut_ds or noMediumABPReceiverElemIn_dr instead *)
fun noMediumABPElem_sender_ds__receiver_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" where
"noMediumABPElem_sender_ds__receiver_dr (Msg sender_port_ds__receiver_port_dr) = noMediumABPElem_raw_sender_ds__receiver_dr sender_port_ds__receiver_port_dr" |
"noMediumABPElem_sender_ds__receiver_dr null = sbeNull {\<C> ''DoNotUse_555251_sender_ds__receiver_dr''}"

(* Do not use this, use noMediumABPReceiverElemOut_ar_o or noMediumABPSenderElemIn_as_i instead *)
fun noMediumABPElem_receiver_ar__sender_as :: "bool tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" where
"noMediumABPElem_receiver_ar__sender_as (Msg receiver_port_ar__sender_port_as) = noMediumABPElem_raw_receiver_ar__sender_as receiver_port_ar__sender_port_as" |
"noMediumABPElem_receiver_ar__sender_as null = sbeNull {\<C> ''DoNotUse_555251_receiver_ar__sender_as''}"

declare noMediumABPElem_receiver_o__o.simps[simp del]

declare noMediumABPElem_i__sender_i.simps[simp del]

declare noMediumABPElem_sender_ds__receiver_dr.simps[simp del]

declare noMediumABPElem_receiver_ar__sender_as.simps[simp del]

(* Do not use this, use noMediumABPReceiverOut_ar_o or noMediumABPOut_o instead *)
definition noMediumABP_receiver_o__o :: "'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABP_receiver_o__o receiver_port_o__port_o = sbe2SB (noMediumABPElem_receiver_o__o receiver_port_o__port_o)"

(* Do not use this, use noMediumABPIn_i or noMediumABPSenderIn_as_i instead *)
definition noMediumABP_i__sender_i :: "'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABP_i__sender_i port_i__sender_port_i = sbe2SB (noMediumABPElem_i__sender_i port_i__sender_port_i)"

(* Do not use this, use noMediumABPSenderOut_ds or noMediumABPReceiverIn_dr instead *)
definition noMediumABP_sender_ds__receiver_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABP_sender_ds__receiver_dr sender_port_ds__receiver_port_dr = sbe2SB (noMediumABPElem_sender_ds__receiver_dr sender_port_ds__receiver_port_dr)"

(* Do not use this, use noMediumABPReceiverOut_ar_o or noMediumABPSenderIn_as_i instead *)
definition noMediumABP_receiver_ar__sender_as :: "bool tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABP_receiver_ar__sender_as receiver_port_ar__sender_port_as = sbe2SB (noMediumABPElem_receiver_ar__sender_as receiver_port_ar__sender_port_as)"


subsubsection \<open>In/Out\<close>

(* Create one sbElem for all input channels *)
definition noMediumABPElemIn_i :: "'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" where
"noMediumABPElemIn_i port_i = (noMediumABPElem_i__sender_i port_i)"

(* Create one sbElem for all output channels *)
definition noMediumABPElemOut_o :: "'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" where
"noMediumABPElemOut_o port_o = (noMediumABPElem_receiver_o__o port_o)"

(* Create one SB for all input channels *)
definition noMediumABPIn_i :: "'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPIn_i port_i = (sbe2SB (noMediumABPElemIn_i port_i))"

(* Create one SB for all output channels *)
definition noMediumABPOut_o :: "'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPOut_o port_o = (sbe2SB (noMediumABPElemOut_o port_o))"


subsubsection \<open>sender In/Out\<close>

(* Create one sbElem for all input channels *)
definition noMediumABPSenderElemIn_as_i :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" where
"noMediumABPSenderElemIn_as_i port_as port_i = (noMediumABPElem_receiver_ar__sender_as port_as) \<plusminus> (noMediumABPElem_i__sender_i port_i)"

(* Create one sbElem for all output channels *)
definition noMediumABPSenderElemOut_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" where
"noMediumABPSenderElemOut_ds port_ds = (noMediumABPElem_sender_ds__receiver_dr port_ds)"

(* Create one SB for all input channels *)
definition noMediumABPSenderIn_as_i :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPSenderIn_as_i port_as port_i = (sbe2SB (noMediumABPSenderElemIn_as_i port_as port_i))"

(* Create one SB for all output channels *)
definition noMediumABPSenderOut_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPSenderOut_ds port_ds = (sbe2SB (noMediumABPSenderElemOut_ds port_ds))"


subsubsection \<open>receiver In/Out\<close>

(* Create one sbElem for all input channels *)
definition noMediumABPReceiverElemIn_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" where
"noMediumABPReceiverElemIn_dr port_dr = (noMediumABPElem_sender_ds__receiver_dr port_dr)"

(* Create one sbElem for all output channels *)
definition noMediumABPReceiverElemOut_ar_o :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn sbElem" where
"noMediumABPReceiverElemOut_ar_o port_ar port_o = (noMediumABPElem_receiver_ar__sender_as port_ar) \<plusminus> (noMediumABPElem_receiver_o__o port_o)"

(* Create one SB for all input channels *)
definition noMediumABPReceiverIn_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPReceiverIn_dr port_dr = (sbe2SB (noMediumABPReceiverElemIn_dr port_dr))"

(* Create one SB for all output channels *)
definition noMediumABPReceiverOut_ar_o :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPReceiverOut_ar_o port_ar port_o = (sbe2SB (noMediumABPReceiverElemOut_ar_o port_ar port_o))"


subsection \<open>list to SB\<close>

subsubsection \<open>Intern\<close>

(* Do not use this, use noMediumABPReceiverOut_list_ar_o or noMediumABPOut_list_o instead *)
fun noMediumABP_list_receiver_o__o :: "('e tsyn) list \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABP_list_receiver_o__o (x#xs) = ubConcEq (noMediumABP_receiver_o__o x)\<cdot>(noMediumABP_list_receiver_o__o xs)" |
"noMediumABP_list_receiver_o__o []     = ubLeast {\<C> ''DoNotUse_555251_receiver_o__o''}"

declare noMediumABP_list_receiver_o__o.simps[simp del]

(* Do not use this, use noMediumABPIn_list_i or noMediumABPSenderIn_list_as_i instead *)
fun noMediumABP_list_i__sender_i :: "('e tsyn) list \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABP_list_i__sender_i (x#xs) = ubConcEq (noMediumABP_i__sender_i x)\<cdot>(noMediumABP_list_i__sender_i xs)" |
"noMediumABP_list_i__sender_i []     = ubLeast {\<C> ''DoNotUse_555251_i__sender_i''}"

declare noMediumABP_list_i__sender_i.simps[simp del]

(* Do not use this, use noMediumABPSenderOut_list_ds or noMediumABPReceiverIn_list_dr instead *)
fun noMediumABP_list_sender_ds__receiver_dr :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABP_list_sender_ds__receiver_dr (x#xs) = ubConcEq (noMediumABP_sender_ds__receiver_dr x)\<cdot>(noMediumABP_list_sender_ds__receiver_dr xs)" |
"noMediumABP_list_sender_ds__receiver_dr []     = ubLeast {\<C> ''DoNotUse_555251_sender_ds__receiver_dr''}"

declare noMediumABP_list_sender_ds__receiver_dr.simps[simp del]

(* Do not use this, use noMediumABPReceiverOut_list_ar_o or noMediumABPSenderIn_list_as_i instead *)
fun noMediumABP_list_receiver_ar__sender_as :: "(bool tsyn) list \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABP_list_receiver_ar__sender_as (x#xs) = ubConcEq (noMediumABP_receiver_ar__sender_as x)\<cdot>(noMediumABP_list_receiver_ar__sender_as xs)" |
"noMediumABP_list_receiver_ar__sender_as []     = ubLeast {\<C> ''DoNotUse_555251_receiver_ar__sender_as''}"

declare noMediumABP_list_receiver_ar__sender_as.simps[simp del]


subsubsection \<open>In/Out\<close>

(* Create one SB for all input channels *)
fun noMediumABPIn_list_i :: "('e tsyn) list \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPIn_list_i ((port_i)#xs) = ubConcEq (noMediumABPIn_i port_i)\<cdot>(noMediumABPIn_list_i xs)" |
"noMediumABPIn_list_i [] = ubLeast noMediumABPDom"

(* Create one SB for all output channels *)
fun noMediumABPOut_list_o :: "('e tsyn) list \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPOut_list_o ((port_o)#xs) = ubConcEq (noMediumABPOut_o port_o)\<cdot>(noMediumABPOut_list_o xs)" |
"noMediumABPOut_list_o [] = ubLeast noMediumABPRan"


subsubsection \<open>sender In/Out\<close>

(* Create one SB for all input channels *)
fun noMediumABPSenderIn_list_as_i :: "(bool tsyn\<times>'e tsyn) list \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPSenderIn_list_as_i ((port_as,port_i)#xs) = ubConcEq (noMediumABPSenderIn_as_i port_as port_i)\<cdot>(noMediumABPSenderIn_list_as_i xs)" |
"noMediumABPSenderIn_list_as_i [] = ubLeast noMediumABPSenderDom"

(* Create one SB for all output channels *)
fun noMediumABPSenderOut_list_ds :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPSenderOut_list_ds ((port_ds)#xs) = ubConcEq (noMediumABPSenderOut_ds port_ds)\<cdot>(noMediumABPSenderOut_list_ds xs)" |
"noMediumABPSenderOut_list_ds [] = ubLeast noMediumABPSenderRan"


subsubsection \<open>receiver In/Out\<close>

(* Create one SB for all input channels *)
fun noMediumABPReceiverIn_list_dr :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPReceiverIn_list_dr ((port_dr)#xs) = ubConcEq (noMediumABPReceiverIn_dr port_dr)\<cdot>(noMediumABPReceiverIn_list_dr xs)" |
"noMediumABPReceiverIn_list_dr [] = ubLeast noMediumABPReceiverDom"

(* Create one SB for all output channels *)
fun noMediumABPReceiverOut_list_ar_o :: "(bool tsyn\<times>'e tsyn) list \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPReceiverOut_list_ar_o ((port_ar,port_o)#xs) = ubConcEq (noMediumABPReceiverOut_ar_o port_ar port_o)\<cdot>(noMediumABPReceiverOut_list_ar_o xs)" |
"noMediumABPReceiverOut_list_ar_o [] = ubLeast noMediumABPReceiverRan"


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lift_definition DoNotUse_555251_noMediumABP_stream_receiver_o__o_h :: "'e tsyn stream \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_555251_receiver_o__o'') \<mapsto> (tsynMap (DoNotUse_555251_NoMediumABPE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use noMediumABPReceiverOut_stream_ar_o or noMediumABPOut_stream_o instead *)
lift_definition noMediumABP_stream_receiver_o__o :: "('e) tsyn stream \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" is
"DoNotUse_555251_noMediumABP_stream_receiver_o__o_h"
  apply(auto simp add: cfun_def DoNotUse_555251_noMediumABP_stream_receiver_o__o_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_555251_noMediumABP_stream_receiver_o__o_h.rep_eq ubrep_well)

lift_definition DoNotUse_555251_noMediumABP_stream_i__sender_i_h :: "'e tsyn stream \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_555251_i__sender_i'') \<mapsto> (tsynMap (DoNotUse_555251_NoMediumABPE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use noMediumABPIn_stream_i or noMediumABPSenderIn_stream_as_i instead *)
lift_definition noMediumABP_stream_i__sender_i :: "('e) tsyn stream \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" is
"DoNotUse_555251_noMediumABP_stream_i__sender_i_h"
  apply(auto simp add: cfun_def DoNotUse_555251_noMediumABP_stream_i__sender_i_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_555251_noMediumABP_stream_i__sender_i_h.rep_eq ubrep_well)

lift_definition DoNotUse_555251_noMediumABP_stream_sender_ds__receiver_dr_h :: "('e\<times>bool) tsyn stream \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_555251_sender_ds__receiver_dr'') \<mapsto> (tsynMap (DoNotUse_555251_NoMediumABPPair_E_Bool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use noMediumABPSenderOut_stream_ds or noMediumABPReceiverIn_stream_dr instead *)
lift_definition noMediumABP_stream_sender_ds__receiver_dr :: "(('e\<times>bool)) tsyn stream \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" is
"DoNotUse_555251_noMediumABP_stream_sender_ds__receiver_dr_h"
  apply(auto simp add: cfun_def DoNotUse_555251_noMediumABP_stream_sender_ds__receiver_dr_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_555251_noMediumABP_stream_sender_ds__receiver_dr_h.rep_eq ubrep_well)

lift_definition DoNotUse_555251_noMediumABP_stream_receiver_ar__sender_as_h :: "bool tsyn stream \<Rightarrow> ('e::countable) noMediumABPMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_555251_receiver_ar__sender_as'') \<mapsto> (tsynMap (DoNotUse_555251_NoMediumABPBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use noMediumABPReceiverOut_stream_ar_o or noMediumABPSenderIn_stream_as_i instead *)
lift_definition noMediumABP_stream_receiver_ar__sender_as :: "(bool) tsyn stream \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" is
"DoNotUse_555251_noMediumABP_stream_receiver_ar__sender_as_h"
  apply(auto simp add: cfun_def DoNotUse_555251_noMediumABP_stream_receiver_ar__sender_as_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_555251_noMediumABP_stream_receiver_ar__sender_as_h.rep_eq ubrep_well)


subsubsection \<open>In/Out\<close>
(* Create one SB for all input channels *)
definition noMediumABPIn_stream_i :: "'e tsyn stream \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPIn_stream_i = (\<Lambda>  port_i. (noMediumABP_stream_i__sender_i\<cdot>port_i))"

(* Create one SB for all output channels *)
definition noMediumABPOut_stream_o :: "'e tsyn stream \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPOut_stream_o = (\<Lambda>  port_o. (noMediumABP_stream_receiver_o__o\<cdot>port_o))"


subsubsection \<open>sender In/Out\<close>

(* Create one SB for all input channels *)
definition noMediumABPSenderIn_stream_as_i :: "bool tsyn stream \<rightarrow> 'e tsyn stream \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPSenderIn_stream_as_i = (\<Lambda>  port_as port_i. (noMediumABP_stream_receiver_ar__sender_as\<cdot>port_as) \<uplus> (noMediumABP_stream_i__sender_i\<cdot>port_i))"

(* Create one SB for all output channels *)
definition noMediumABPSenderOut_stream_ds :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPSenderOut_stream_ds = (\<Lambda>  port_ds. (noMediumABP_stream_sender_ds__receiver_dr\<cdot>port_ds))"


subsubsection \<open>receiver In/Out\<close>

(* Create one SB for all input channels *)
definition noMediumABPReceiverIn_stream_dr :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPReceiverIn_stream_dr = (\<Lambda>  port_dr. (noMediumABP_stream_sender_ds__receiver_dr\<cdot>port_dr))"

(* Create one SB for all output channels *)
definition noMediumABPReceiverOut_stream_ar_o :: "bool tsyn stream \<rightarrow> 'e tsyn stream \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"noMediumABPReceiverOut_stream_ar_o = (\<Lambda>  port_ar port_o. (noMediumABP_stream_receiver_ar__sender_as\<cdot>port_ar) \<uplus> (noMediumABP_stream_receiver_o__o\<cdot>port_o))"


section \<open>Getter\<close>

subsection \<open>sbElem to tsyn\<close>

definition noMediumABPElem_get_receiver_o__o :: "('e::countable) noMediumABPMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"noMediumABPElem_get_receiver_o__o sbe = tsynApplyElem (inv DoNotUse_555251_NoMediumABPE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_555251_receiver_o__o''))"

definition noMediumABPElem_get_i__sender_i :: "('e::countable) noMediumABPMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"noMediumABPElem_get_i__sender_i sbe = tsynApplyElem (inv DoNotUse_555251_NoMediumABPE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_555251_i__sender_i''))"

definition noMediumABPElem_get_sender_ds__receiver_dr :: "('e::countable) noMediumABPMessage tsyn sbElem \<Rightarrow> (('e\<times>bool)) tsyn" where
"noMediumABPElem_get_sender_ds__receiver_dr sbe = tsynApplyElem (inv DoNotUse_555251_NoMediumABPPair_E_Bool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_555251_sender_ds__receiver_dr''))"

definition noMediumABPElem_get_receiver_ar__sender_as :: "('e::countable) noMediumABPMessage tsyn sbElem \<Rightarrow> (bool) tsyn" where
"noMediumABPElem_get_receiver_ar__sender_as sbe = tsynApplyElem (inv DoNotUse_555251_NoMediumABPBool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_555251_receiver_ar__sender_as''))"


subsection \<open>SB to stream\<close>

lift_definition noMediumABP_get_stream_receiver_o__o :: "('e::countable) noMediumABPMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_555251_NoMediumABPE)\<cdot>(sb . (\<C> ''DoNotUse_555251_receiver_o__o''))"
  by(simp add: cfun_def)

lift_definition noMediumABP_get_stream_i__sender_i :: "('e::countable) noMediumABPMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_555251_NoMediumABPE)\<cdot>(sb . (\<C> ''DoNotUse_555251_i__sender_i''))"
  by(simp add: cfun_def)

lift_definition noMediumABP_get_stream_sender_ds__receiver_dr :: "('e::countable) noMediumABPMessage tsyn SB \<rightarrow> ('e\<times>bool) tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_555251_NoMediumABPPair_E_Bool)\<cdot>(sb . (\<C> ''DoNotUse_555251_sender_ds__receiver_dr''))"
  by(simp add: cfun_def)

lift_definition noMediumABP_get_stream_receiver_ar__sender_as :: "('e::countable) noMediumABPMessage tsyn SB \<rightarrow> bool tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_555251_NoMediumABPBool)\<cdot>(sb . (\<C> ''DoNotUse_555251_receiver_ar__sender_as''))"
  by(simp add: cfun_def)


section \<open>Setter-Lemmas\<close>

subsection \<open>tsyn to sbElem/SB\<close>

subsubsection \<open>Intern\<close>

lemma nomediumabpelem_receiver_o__o_dom[simp]: "sbeDom (noMediumABPElem_receiver_o__o x) = {\<C> ''DoNotUse_555251_receiver_o__o''}"
  apply(cases x)
  apply(simp add: noMediumABPElem_receiver_o__o.simps sbeDom_def noMediumABPElem_raw_receiver_o__o.rep_eq)
  by(simp add: noMediumABPElem_receiver_o__o.simps)

lemma nomediumabpelem_i__sender_i_dom[simp]: "sbeDom (noMediumABPElem_i__sender_i x) = {\<C> ''DoNotUse_555251_i__sender_i''}"
  apply(cases x)
  apply(simp add: noMediumABPElem_i__sender_i.simps sbeDom_def noMediumABPElem_raw_i__sender_i.rep_eq)
  by(simp add: noMediumABPElem_i__sender_i.simps)

lemma nomediumabpelem_sender_ds__receiver_dr_dom[simp]: "sbeDom (noMediumABPElem_sender_ds__receiver_dr x) = {\<C> ''DoNotUse_555251_sender_ds__receiver_dr''}"
  apply(cases x)
  apply(simp add: noMediumABPElem_sender_ds__receiver_dr.simps sbeDom_def noMediumABPElem_raw_sender_ds__receiver_dr.rep_eq)
  by(simp add: noMediumABPElem_sender_ds__receiver_dr.simps)

lemma nomediumabpelem_receiver_ar__sender_as_dom[simp]: "sbeDom (noMediumABPElem_receiver_ar__sender_as x) = {\<C> ''DoNotUse_555251_receiver_ar__sender_as''}"
  apply(cases x)
  apply(simp add: noMediumABPElem_receiver_ar__sender_as.simps sbeDom_def noMediumABPElem_raw_receiver_ar__sender_as.rep_eq)
  by(simp add: noMediumABPElem_receiver_ar__sender_as.simps)

lemma nomediumabp_receiver_o__o_dom[simp]: "ubDom\<cdot>(noMediumABP_receiver_o__o x) = {\<C> ''DoNotUse_555251_receiver_o__o''}"
  by(simp add: noMediumABP_receiver_o__o_def)

lemma nomediumabp_receiver_o__o_len[simp]: "ubLen (noMediumABP_receiver_o__o x) = 1"
  by(simp add: noMediumABP_receiver_o__o_def)

lemma nomediumabp_i__sender_i_dom[simp]: "ubDom\<cdot>(noMediumABP_i__sender_i x) = {\<C> ''DoNotUse_555251_i__sender_i''}"
  by(simp add: noMediumABP_i__sender_i_def)

lemma nomediumabp_i__sender_i_len[simp]: "ubLen (noMediumABP_i__sender_i x) = 1"
  by(simp add: noMediumABP_i__sender_i_def)

lemma nomediumabp_sender_ds__receiver_dr_dom[simp]: "ubDom\<cdot>(noMediumABP_sender_ds__receiver_dr x) = {\<C> ''DoNotUse_555251_sender_ds__receiver_dr''}"
  by(simp add: noMediumABP_sender_ds__receiver_dr_def)

lemma nomediumabp_sender_ds__receiver_dr_len[simp]: "ubLen (noMediumABP_sender_ds__receiver_dr x) = 1"
  by(simp add: noMediumABP_sender_ds__receiver_dr_def)

lemma nomediumabp_receiver_ar__sender_as_dom[simp]: "ubDom\<cdot>(noMediumABP_receiver_ar__sender_as x) = {\<C> ''DoNotUse_555251_receiver_ar__sender_as''}"
  by(simp add: noMediumABP_receiver_ar__sender_as_def)

lemma nomediumabp_receiver_ar__sender_as_len[simp]: "ubLen (noMediumABP_receiver_ar__sender_as x) = 1"
  by(simp add: noMediumABP_receiver_ar__sender_as_def)


subsubsection \<open>In/Out\<close>

lemma nomediumabpelemin_i_dom[simp]: "sbeDom (noMediumABPElemIn_i port_i) = noMediumABPDom"
  by(auto simp add: noMediumABPElemIn_i_def noMediumABPDom_def)

lemma nomediumabpelemout_o_dom[simp]: "sbeDom (noMediumABPElemOut_o port_o) = noMediumABPRan"
  by(auto simp add: noMediumABPElemOut_o_def noMediumABPRan_def)

lemma nomediumabpin_i_dom[simp]: "ubDom\<cdot>(noMediumABPIn_i port_i) = noMediumABPDom"
  by(simp add: noMediumABPIn_i_def)

lemma nomediumabpin_i_len[simp]: "ubLen (noMediumABPIn_i port_i) = 1"
  by(simp add: noMediumABPIn_i_def noMediumABPDom_def)

lemma nomediumabpout_o_dom[simp]: "ubDom\<cdot>(noMediumABPOut_o port_o) = noMediumABPRan"
  by(simp add: noMediumABPOut_o_def)

lemma nomediumabpout_o_len[simp]: "ubLen (noMediumABPOut_o port_o) = 1"
  by(simp add: noMediumABPOut_o_def noMediumABPRan_def)


subsubsection \<open>sender In/Out\<close>

lemma nomediumabpsenderelemin_as_i_dom[simp]: "sbeDom (noMediumABPSenderElemIn_as_i port_as port_i) = noMediumABPSenderDom"
  by(auto simp add: noMediumABPSenderElemIn_as_i_def noMediumABPSenderDom_def)

lemma nomediumabpsenderelemout_ds_dom[simp]: "sbeDom (noMediumABPSenderElemOut_ds port_ds) = noMediumABPSenderRan"
  by(auto simp add: noMediumABPSenderElemOut_ds_def noMediumABPSenderRan_def)

lemma nomediumabpsenderin_as_i_dom[simp]: "ubDom\<cdot>(noMediumABPSenderIn_as_i port_as port_i) = noMediumABPSenderDom"
  by(auto simp add: noMediumABPSenderIn_as_i_def noMediumABPSenderDom_def)

lemma nomediumabpsenderout_ds_dom[simp]: "ubDom\<cdot>(noMediumABPSenderOut_ds port_ds) = noMediumABPSenderRan"
  by(auto simp add: noMediumABPSenderOut_ds_def noMediumABPSenderRan_def)


subsubsection \<open>receiver In/Out\<close>

lemma nomediumabpreceiverelemin_dr_dom[simp]: "sbeDom (noMediumABPReceiverElemIn_dr port_dr) = noMediumABPReceiverDom"
  by(auto simp add: noMediumABPReceiverElemIn_dr_def noMediumABPReceiverDom_def)

lemma nomediumabpreceiverelemout_ar_o_dom[simp]: "sbeDom (noMediumABPReceiverElemOut_ar_o port_ar port_o) = noMediumABPReceiverRan"
  by(auto simp add: noMediumABPReceiverElemOut_ar_o_def noMediumABPReceiverRan_def)

lemma nomediumabpreceiverin_dr_dom[simp]: "ubDom\<cdot>(noMediumABPReceiverIn_dr port_dr) = noMediumABPReceiverDom"
  by(auto simp add: noMediumABPReceiverIn_dr_def noMediumABPReceiverDom_def)

lemma nomediumabpreceiverout_ar_o_dom[simp]: "ubDom\<cdot>(noMediumABPReceiverOut_ar_o port_ar port_o) = noMediumABPReceiverRan"
  by(auto simp add: noMediumABPReceiverOut_ar_o_def noMediumABPReceiverRan_def)


subsection \<open>stream to SB\<close>

subsubsection \<open>Intern\<close>

lemma nomediumabp_stream_receiver_o__o_dom[simp]: "ubDom\<cdot>(noMediumABP_stream_receiver_o__o\<cdot>x) = {\<C> ''DoNotUse_555251_receiver_o__o''}"
  by(simp add: noMediumABP_stream_receiver_o__o.rep_eq ubdom_insert DoNotUse_555251_noMediumABP_stream_receiver_o__o_h.rep_eq)

lemma nomediumabp_stream_receiver_o__o_len[simp]: "ubLen (noMediumABP_stream_receiver_o__o\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: noMediumABP_stream_receiver_o__o.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_555251_noMediumABP_stream_receiver_o__o_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma nomediumabp_stream_receiver_o__o_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_555251_receiver_o__o''} "
    shows "noMediumABP_stream_receiver_o__o\<cdot>(noMediumABP_get_stream_receiver_o__o\<cdot>ub) = ub"
  apply(simp add: noMediumABP_stream_receiver_o__o.rep_eq noMediumABP_get_stream_receiver_o__o.rep_eq)
  apply(simp add: DoNotUse_555251_noMediumABP_stream_receiver_o__o_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma nomediumabp_stream_i__sender_i_dom[simp]: "ubDom\<cdot>(noMediumABP_stream_i__sender_i\<cdot>x) = {\<C> ''DoNotUse_555251_i__sender_i''}"
  by(simp add: noMediumABP_stream_i__sender_i.rep_eq ubdom_insert DoNotUse_555251_noMediumABP_stream_i__sender_i_h.rep_eq)

lemma nomediumabp_stream_i__sender_i_len[simp]: "ubLen (noMediumABP_stream_i__sender_i\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: noMediumABP_stream_i__sender_i.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_555251_noMediumABP_stream_i__sender_i_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma nomediumabp_stream_i__sender_i_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_555251_i__sender_i''} "
    shows "noMediumABP_stream_i__sender_i\<cdot>(noMediumABP_get_stream_i__sender_i\<cdot>ub) = ub"
  apply(simp add: noMediumABP_stream_i__sender_i.rep_eq noMediumABP_get_stream_i__sender_i.rep_eq)
  apply(simp add: DoNotUse_555251_noMediumABP_stream_i__sender_i_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma nomediumabp_stream_sender_ds__receiver_dr_dom[simp]: "ubDom\<cdot>(noMediumABP_stream_sender_ds__receiver_dr\<cdot>x) = {\<C> ''DoNotUse_555251_sender_ds__receiver_dr''}"
  by(simp add: noMediumABP_stream_sender_ds__receiver_dr.rep_eq ubdom_insert DoNotUse_555251_noMediumABP_stream_sender_ds__receiver_dr_h.rep_eq)

lemma nomediumabp_stream_sender_ds__receiver_dr_len[simp]: "ubLen (noMediumABP_stream_sender_ds__receiver_dr\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: noMediumABP_stream_sender_ds__receiver_dr.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_555251_noMediumABP_stream_sender_ds__receiver_dr_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma nomediumabp_stream_sender_ds__receiver_dr_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_555251_sender_ds__receiver_dr''} "
    shows "noMediumABP_stream_sender_ds__receiver_dr\<cdot>(noMediumABP_get_stream_sender_ds__receiver_dr\<cdot>ub) = ub"
  apply(simp add: noMediumABP_stream_sender_ds__receiver_dr.rep_eq noMediumABP_get_stream_sender_ds__receiver_dr.rep_eq)
  apply(simp add: DoNotUse_555251_noMediumABP_stream_sender_ds__receiver_dr_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast

lemma nomediumabp_stream_receiver_ar__sender_as_dom[simp]: "ubDom\<cdot>(noMediumABP_stream_receiver_ar__sender_as\<cdot>x) = {\<C> ''DoNotUse_555251_receiver_ar__sender_as''}"
  by(simp add: noMediumABP_stream_receiver_ar__sender_as.rep_eq ubdom_insert DoNotUse_555251_noMediumABP_stream_receiver_ar__sender_as_h.rep_eq)

lemma nomediumabp_stream_receiver_ar__sender_as_len[simp]: "ubLen (noMediumABP_stream_receiver_ar__sender_as\<cdot>x) = #x"
  apply(subst uslen_ubLen_ch3)
  apply simp
  apply(simp add: noMediumABP_stream_receiver_ar__sender_as.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_555251_noMediumABP_stream_receiver_ar__sender_as_h.rep_eq)
  by (simp add: tsynmap_slen usclLen_stream_def)

lemma nomediumabp_stream_receiver_ar__sender_as_id[simp]:
  assumes "ubDom\<cdot>ub = {\<C> ''DoNotUse_555251_receiver_ar__sender_as''} "
    shows "noMediumABP_stream_receiver_ar__sender_as\<cdot>(noMediumABP_get_stream_receiver_ar__sender_as\<cdot>ub) = ub"
  apply(simp add: noMediumABP_stream_receiver_ar__sender_as.rep_eq noMediumABP_get_stream_receiver_ar__sender_as.rep_eq)
  apply(simp add: DoNotUse_555251_noMediumABP_stream_receiver_ar__sender_as_h_def)
  apply(subst tsynmap_inv_id)
  using assms tsynbundle_ctype apply fastforce
  using assms ub_id_single by blast


subsubsection \<open>In/Out\<close>

lemma nomediumabpin_stream_i_dom[simp]: "ubDom\<cdot>(noMediumABPIn_stream_i\<cdot>port_i__sender_port_i) = noMediumABPDom"
  apply(simp add: noMediumABPIn_stream_i_def ubclUnion_ubundle_def)
  by(auto simp add: noMediumABPDom_def)

lemma nomediumabpout_stream_o_dom[simp]: "ubDom\<cdot>(noMediumABPOut_stream_o\<cdot>receiver_port_o__port_o) = noMediumABPRan"
  apply(simp add: noMediumABPOut_stream_o_def ubclUnion_ubundle_def)
  by(auto simp add: noMediumABPRan_def)


subsubsection \<open>sender In/Out\<close>

lemma nomediumabpsenderin_stream_as_i_dom[simp]: "ubDom\<cdot>(noMediumABPSenderIn_stream_as_i\<cdot>receiver_port_ar__sender_port_as\<cdot>port_i__sender_port_i) = noMediumABPSenderDom"
  apply(simp add: noMediumABPSenderIn_stream_as_i_def ubclUnion_ubundle_def)
  by(auto simp add: noMediumABPSenderDom_def)

lemma nomediumabpsenderout_stream_ds_dom[simp]: "ubDom\<cdot>(noMediumABPSenderOut_stream_ds\<cdot>sender_port_ds__receiver_port_dr) = noMediumABPSenderRan"
  apply(simp add: noMediumABPSenderOut_stream_ds_def ubclUnion_ubundle_def)
  by(auto simp add: noMediumABPSenderRan_def)


subsubsection \<open>receiver In/Out\<close>

lemma nomediumabpreceiverin_stream_dr_dom[simp]: "ubDom\<cdot>(noMediumABPReceiverIn_stream_dr\<cdot>sender_port_ds__receiver_port_dr) = noMediumABPReceiverDom"
  apply(simp add: noMediumABPReceiverIn_stream_dr_def ubclUnion_ubundle_def)
  by(auto simp add: noMediumABPReceiverDom_def)

lemma nomediumabpreceiverout_stream_ar_o_dom[simp]: "ubDom\<cdot>(noMediumABPReceiverOut_stream_ar_o\<cdot>receiver_port_ar__sender_port_as\<cdot>receiver_port_o__port_o) = noMediumABPReceiverRan"
  apply(simp add: noMediumABPReceiverOut_stream_ar_o_def ubclUnion_ubundle_def)
  by(auto simp add: noMediumABPReceiverRan_def)


section \<open>Getter-Lemmas\<close>

subsection \<open>sbElem to tsyn\<close>

subsubsection \<open>Intern\<close>

lemma nomediumabpelem_get_receiver_o__o_id[simp]: "noMediumABPElem_get_receiver_o__o (noMediumABPElem_receiver_o__o x) = x"
  apply(cases x)
  apply(auto simp add: noMediumABPElem_receiver_o__o.simps)
  unfolding noMediumABPElem_get_receiver_o__o_def noMediumABPElem_raw_receiver_o__o.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI noMediumABPMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma nomediumabpelem_get_i__sender_i_id[simp]: "noMediumABPElem_get_i__sender_i (noMediumABPElem_i__sender_i x) = x"
  apply(cases x)
  apply(auto simp add: noMediumABPElem_i__sender_i.simps)
  unfolding noMediumABPElem_get_i__sender_i_def noMediumABPElem_raw_i__sender_i.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI noMediumABPMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma nomediumabpelem_get_sender_ds__receiver_dr_id[simp]: "noMediumABPElem_get_sender_ds__receiver_dr (noMediumABPElem_sender_ds__receiver_dr x) = x"
  apply(cases x)
  apply(auto simp add: noMediumABPElem_sender_ds__receiver_dr.simps)
  unfolding noMediumABPElem_get_sender_ds__receiver_dr_def noMediumABPElem_raw_sender_ds__receiver_dr.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI noMediumABPMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma nomediumabpelem_get_receiver_ar__sender_as_id[simp]: "noMediumABPElem_get_receiver_ar__sender_as (noMediumABPElem_receiver_ar__sender_as x) = x"
  apply(cases x)
  apply(auto simp add: noMediumABPElem_receiver_ar__sender_as.simps)
  unfolding noMediumABPElem_get_receiver_ar__sender_as_def noMediumABPElem_raw_receiver_ar__sender_as.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI noMediumABPMessage.inject)
  by(simp add: sbeNull.rep_eq)


subsubsection \<open>In/Out\<close>

lemma nomediumabpelem_get_i__sender_i_in_i__sender_i_id[simp]: "noMediumABPElem_get_i__sender_i (noMediumABPElemIn_i port_i__sender_port_i) = port_i__sender_port_i"
  apply(simp add: noMediumABPElemIn_i_def noMediumABPElem_get_i__sender_i_def)
  by(metis noMediumABPElem_get_i__sender_i_def nomediumabpelem_get_i__sender_i_id)

lemma nomediumabpelem_get_receiver_o__o_out_receiver_o__o_id[simp]: "noMediumABPElem_get_receiver_o__o (noMediumABPElemOut_o receiver_port_o__port_o) = receiver_port_o__port_o"
  apply(simp add: noMediumABPElemOut_o_def noMediumABPElem_get_receiver_o__o_def)
  by(metis noMediumABPElem_get_receiver_o__o_def nomediumabpelem_get_receiver_o__o_id)


subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma nomediumabp_get_stream_receiver_o__o_id[simp]: "noMediumABP_get_stream_receiver_o__o\<cdot>(noMediumABP_stream_receiver_o__o\<cdot>x) = x"
  apply(simp add: noMediumABP_get_stream_receiver_o__o.rep_eq noMediumABP_stream_receiver_o__o.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_555251_noMediumABP_stream_receiver_o__o_h.rep_eq)
  by (simp add: inj_def)

lemma nomediumabp_get_stream_receiver_o__o_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_555251_receiver_o__o''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_555251_receiver_o__o''}"
      and "noMediumABP_get_stream_receiver_o__o\<cdot>ub1 = noMediumABP_get_stream_receiver_o__o\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) nomediumabp_stream_receiver_o__o_id by metis

lemma nomediumabp_get_stream_receiver_o__o_conc[simp]:
  assumes "\<C> ''DoNotUse_555251_receiver_o__o'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_555251_receiver_o__o'' \<in> ubDom\<cdot>ub2"
    shows "noMediumABP_get_stream_receiver_o__o\<cdot>(ubConc ub1\<cdot>ub2) = (noMediumABP_get_stream_receiver_o__o\<cdot>ub1) \<bullet> (noMediumABP_get_stream_receiver_o__o\<cdot>ub2)"
  apply(simp add: noMediumABP_get_stream_receiver_o__o.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma nomediumabp_get_stream_i__sender_i_id[simp]: "noMediumABP_get_stream_i__sender_i\<cdot>(noMediumABP_stream_i__sender_i\<cdot>x) = x"
  apply(simp add: noMediumABP_get_stream_i__sender_i.rep_eq noMediumABP_stream_i__sender_i.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_555251_noMediumABP_stream_i__sender_i_h.rep_eq)
  by (simp add: inj_def)

lemma nomediumabp_get_stream_i__sender_i_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_555251_i__sender_i''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_555251_i__sender_i''}"
      and "noMediumABP_get_stream_i__sender_i\<cdot>ub1 = noMediumABP_get_stream_i__sender_i\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) nomediumabp_stream_i__sender_i_id by metis

lemma nomediumabp_get_stream_i__sender_i_conc[simp]:
  assumes "\<C> ''DoNotUse_555251_i__sender_i'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_555251_i__sender_i'' \<in> ubDom\<cdot>ub2"
    shows "noMediumABP_get_stream_i__sender_i\<cdot>(ubConc ub1\<cdot>ub2) = (noMediumABP_get_stream_i__sender_i\<cdot>ub1) \<bullet> (noMediumABP_get_stream_i__sender_i\<cdot>ub2)"
  apply(simp add: noMediumABP_get_stream_i__sender_i.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma nomediumabp_get_stream_sender_ds__receiver_dr_id[simp]: "noMediumABP_get_stream_sender_ds__receiver_dr\<cdot>(noMediumABP_stream_sender_ds__receiver_dr\<cdot>x) = x"
  apply(simp add: noMediumABP_get_stream_sender_ds__receiver_dr.rep_eq noMediumABP_stream_sender_ds__receiver_dr.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_555251_noMediumABP_stream_sender_ds__receiver_dr_h.rep_eq)
  by (simp add: inj_def)

lemma nomediumabp_get_stream_sender_ds__receiver_dr_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_555251_sender_ds__receiver_dr''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_555251_sender_ds__receiver_dr''}"
      and "noMediumABP_get_stream_sender_ds__receiver_dr\<cdot>ub1 = noMediumABP_get_stream_sender_ds__receiver_dr\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) nomediumabp_stream_sender_ds__receiver_dr_id by metis

lemma nomediumabp_get_stream_sender_ds__receiver_dr_conc[simp]:
  assumes "\<C> ''DoNotUse_555251_sender_ds__receiver_dr'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_555251_sender_ds__receiver_dr'' \<in> ubDom\<cdot>ub2"
    shows "noMediumABP_get_stream_sender_ds__receiver_dr\<cdot>(ubConc ub1\<cdot>ub2) = (noMediumABP_get_stream_sender_ds__receiver_dr\<cdot>ub1) \<bullet> (noMediumABP_get_stream_sender_ds__receiver_dr\<cdot>ub2)"
  apply(simp add: noMediumABP_get_stream_sender_ds__receiver_dr.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)

lemma nomediumabp_get_stream_receiver_ar__sender_as_id[simp]: "noMediumABP_get_stream_receiver_ar__sender_as\<cdot>(noMediumABP_stream_receiver_ar__sender_as\<cdot>x) = x"
  apply(simp add: noMediumABP_get_stream_receiver_ar__sender_as.rep_eq noMediumABP_stream_receiver_ar__sender_as.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_555251_noMediumABP_stream_receiver_ar__sender_as_h.rep_eq)
  by (simp add: inj_def)

lemma nomediumabp_get_stream_receiver_ar__sender_as_eq:
  assumes "ubDom\<cdot>ub1 = {\<C> ''DoNotUse_555251_receiver_ar__sender_as''}"
      and "ubDom\<cdot>ub2 = {\<C> ''DoNotUse_555251_receiver_ar__sender_as''}"
      and "noMediumABP_get_stream_receiver_ar__sender_as\<cdot>ub1 = noMediumABP_get_stream_receiver_ar__sender_as\<cdot>ub2"
    shows "ub1 = ub2"
  using assms(1) assms(2) assms(3) nomediumabp_stream_receiver_ar__sender_as_id by metis

lemma nomediumabp_get_stream_receiver_ar__sender_as_conc[simp]:
  assumes "\<C> ''DoNotUse_555251_receiver_ar__sender_as'' \<in> ubDom\<cdot>ub1"
      and "\<C> ''DoNotUse_555251_receiver_ar__sender_as'' \<in> ubDom\<cdot>ub2"
    shows "noMediumABP_get_stream_receiver_ar__sender_as\<cdot>(ubConc ub1\<cdot>ub2) = (noMediumABP_get_stream_receiver_ar__sender_as\<cdot>ub1) \<bullet> (noMediumABP_get_stream_receiver_ar__sender_as\<cdot>ub2)"
  apply(simp add: noMediumABP_get_stream_receiver_ar__sender_as.rep_eq)
  apply (subst ubConc_usclConc_eq)
  using assms(1) apply blast
  using assms(2) apply blast
  by (simp add: tsynmap_sconc usclConc_stream_def)


subsubsection \<open>In/Out\<close>

lemma nomediumabp_get_stream_i__sender_i_in_i__sender_i_id[simp]: "noMediumABP_get_stream_i__sender_i\<cdot>(noMediumABPIn_stream_i\<cdot>port_i__sender_port_i) = port_i__sender_port_i"
  apply(auto simp add: noMediumABP_get_stream_i__sender_i.rep_eq noMediumABPIn_stream_i_def ubclUnion_ubundle_def)
  by (metis noMediumABP_get_stream_i__sender_i.rep_eq nomediumabp_get_stream_i__sender_i_id)

lemma nomediumabp_get_stream_receiver_o__o_out_receiver_o__o_id[simp]: "noMediumABP_get_stream_receiver_o__o\<cdot>(noMediumABPOut_stream_o\<cdot>receiver_port_o__port_o) = receiver_port_o__port_o"
  apply(auto simp add: noMediumABP_get_stream_receiver_o__o.rep_eq noMediumABPOut_stream_o_def ubclUnion_ubundle_def)
  by (metis noMediumABP_get_stream_receiver_o__o.rep_eq nomediumabp_get_stream_receiver_o__o_id)


subsection \<open>tsyn to SB to one-element stream\<close>

subsubsection \<open>Intern\<close>

lemma nomediumabp_get_stream_receiver_o__o_single[simp]: "noMediumABP_get_stream_receiver_o__o\<cdot>(noMediumABP_receiver_o__o x) = \<up>x"
  apply(simp add: noMediumABP_get_stream_receiver_o__o.rep_eq noMediumABP_receiver_o__o_def)
  by (metis noMediumABPElem_get_receiver_o__o_def nomediumabpelem_get_receiver_o__o_id)

lemma nomediumabp_get_stream_i__sender_i_single[simp]: "noMediumABP_get_stream_i__sender_i\<cdot>(noMediumABP_i__sender_i x) = \<up>x"
  apply(simp add: noMediumABP_get_stream_i__sender_i.rep_eq noMediumABP_i__sender_i_def)
  by (metis noMediumABPElem_get_i__sender_i_def nomediumabpelem_get_i__sender_i_id)

lemma nomediumabp_get_stream_sender_ds__receiver_dr_single[simp]: "noMediumABP_get_stream_sender_ds__receiver_dr\<cdot>(noMediumABP_sender_ds__receiver_dr x) = \<up>x"
  apply(simp add: noMediumABP_get_stream_sender_ds__receiver_dr.rep_eq noMediumABP_sender_ds__receiver_dr_def)
  by (metis noMediumABPElem_get_sender_ds__receiver_dr_def nomediumabpelem_get_sender_ds__receiver_dr_id)

lemma nomediumabp_get_stream_receiver_ar__sender_as_single[simp]: "noMediumABP_get_stream_receiver_ar__sender_as\<cdot>(noMediumABP_receiver_ar__sender_as x) = \<up>x"
  apply(simp add: noMediumABP_get_stream_receiver_ar__sender_as.rep_eq noMediumABP_receiver_ar__sender_as_def)
  by (metis noMediumABPElem_get_receiver_ar__sender_as_def nomediumabpelem_get_receiver_ar__sender_as_id)


subsubsection \<open>In/Out\<close>

lemma nomediumabp_get_stream_i__sender_i_single_in_i__sender_i_id[simp]: "noMediumABP_get_stream_i__sender_i\<cdot>(noMediumABPIn_i port_i__sender_port_i) = \<up>port_i__sender_port_i"
  apply(simp add: noMediumABP_get_stream_i__sender_i_def noMediumABPIn_i_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: noMediumABPDom_def noMediumABPElemIn_i_def)
  apply(cases port_i__sender_port_i)
  apply(auto simp add: noMediumABPElem_i__sender_i.simps)
  unfolding noMediumABPElem_get_i__sender_i_def noMediumABPElem_raw_i__sender_i.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)

lemma nomediumabp_get_stream_receiver_o__o_single_out_receiver_o__o_id[simp]: "noMediumABP_get_stream_receiver_o__o\<cdot>(noMediumABPOut_o receiver_port_o__port_o) = \<up>receiver_port_o__port_o"
  apply(simp add: noMediumABP_get_stream_receiver_o__o_def noMediumABPOut_o_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: noMediumABPDom_def noMediumABPElemOut_o_def)
  apply(cases receiver_port_o__port_o)
  apply(auto simp add: noMediumABPElem_receiver_o__o.simps)
  unfolding noMediumABPElem_get_receiver_o__o_def noMediumABPElem_raw_receiver_o__o.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)


section \<open>More Setter-Lemmas\<close>

subsection \<open>SB to stream\<close>

subsubsection \<open>Intern\<close>

lemma nomediumabp_stream_receiver_o__o_conc:
  "noMediumABP_stream_receiver_o__o\<cdot>(\<up>elem \<bullet> s) = ubConc (noMediumABP_receiver_o__o elem)\<cdot>(noMediumABP_stream_receiver_o__o\<cdot>s)"
  apply (rule nomediumabp_get_stream_receiver_o__o_eq)
  by simp_all

lemma nomediumabp_stream_i__sender_i_conc:
  "noMediumABP_stream_i__sender_i\<cdot>(\<up>elem \<bullet> s) = ubConc (noMediumABP_i__sender_i elem)\<cdot>(noMediumABP_stream_i__sender_i\<cdot>s)"
  apply (rule nomediumabp_get_stream_i__sender_i_eq)
  by simp_all

lemma nomediumabp_stream_sender_ds__receiver_dr_conc:
  "noMediumABP_stream_sender_ds__receiver_dr\<cdot>(\<up>elem \<bullet> s) = ubConc (noMediumABP_sender_ds__receiver_dr elem)\<cdot>(noMediumABP_stream_sender_ds__receiver_dr\<cdot>s)"
  apply (rule nomediumabp_get_stream_sender_ds__receiver_dr_eq)
  by simp_all

lemma nomediumabp_stream_receiver_ar__sender_as_conc:
  "noMediumABP_stream_receiver_ar__sender_as\<cdot>(\<up>elem \<bullet> s) = ubConc (noMediumABP_receiver_ar__sender_as elem)\<cdot>(noMediumABP_stream_receiver_ar__sender_as\<cdot>s)"
  apply (rule nomediumabp_get_stream_receiver_ar__sender_as_eq)
  by simp_all


end