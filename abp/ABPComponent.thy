(*
 * DO NOT MODIFY!
 * This file was generated from ABP.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 2, 2018 7:58:20 PM by isartransformer 1.0.0
 *)
theory ABPComponent
  imports SenderAutomaton MediumAutomaton ReceiverAutomaton spec.SPS spec.USpec_UFunComp

begin


section \<open>Datatype definition\<close>

datatype ('e::countable) abpMessage = DoNotUse_4ea8f2_ABPE "'e" | DoNotUse_4ea8f2_ABPBool "bool" | DoNotUse_4ea8f2_ABPPair_E_Bool "('e\<times>bool)"

instance abpMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation abpMessage :: (countable) message
begin
  fun ctype_abpMessage :: "channel \<Rightarrow> ('e::countable) abpMessage set" where
  "ctype_abpMessage c = (
    if c = \<C> ''DoNotUse_4ea8f2_receiver_o__o'' then range DoNotUse_4ea8f2_ABPE else
    if c = \<C> ''DoNotUse_4ea8f2_i__sender_i'' then range DoNotUse_4ea8f2_ABPE else
    if c = \<C> ''DoNotUse_4ea8f2_sender_ds__mediumSr_ar'' then range DoNotUse_4ea8f2_ABPPair_E_Bool else
    if c = \<C> ''DoNotUse_4ea8f2_mediumSr_as__receiver_dr'' then range DoNotUse_4ea8f2_ABPPair_E_Bool else
    if c = \<C> ''DoNotUse_4ea8f2_receiver_ar__mediumRs_ar'' then range DoNotUse_4ea8f2_ABPBool else
    if c = \<C> ''DoNotUse_4ea8f2_mediumRs_as__sender_as'' then range DoNotUse_4ea8f2_ABPBool else
    undefined)"
  instance
    by(intro_classes)
end


section \<open>Domain and range\<close>

definition aBPDom :: "channel set" where
"aBPDom = {\<C> ''DoNotUse_4ea8f2_i__sender_i''}"

definition aBPRan :: "channel set" where
"aBPRan = {\<C> ''DoNotUse_4ea8f2_receiver_o__o''}"


subsection \<open>sender\<close>

definition aBPSenderDom :: "channel set" where
"aBPSenderDom = {\<C> ''DoNotUse_4ea8f2_mediumRs_as__sender_as'', \<C> ''DoNotUse_4ea8f2_i__sender_i''}"

definition aBPSenderRan :: "channel set" where
"aBPSenderRan = {\<C> ''DoNotUse_4ea8f2_sender_ds__mediumSr_ar''}"


subsection \<open>mediumSr\<close>

definition aBPMediumSrDom :: "channel set" where
"aBPMediumSrDom = {\<C> ''DoNotUse_4ea8f2_sender_ds__mediumSr_ar''}"

definition aBPMediumSrRan :: "channel set" where
"aBPMediumSrRan = {\<C> ''DoNotUse_4ea8f2_mediumSr_as__receiver_dr''}"


subsection \<open>receiver\<close>

definition aBPReceiverDom :: "channel set" where
"aBPReceiverDom = {\<C> ''DoNotUse_4ea8f2_mediumSr_as__receiver_dr''}"

definition aBPReceiverRan :: "channel set" where
"aBPReceiverRan = {\<C> ''DoNotUse_4ea8f2_receiver_ar__mediumRs_ar'', \<C> ''DoNotUse_4ea8f2_receiver_o__o''}"


subsection \<open>mediumRs\<close>

definition aBPMediumRsDom :: "channel set" where
"aBPMediumRsDom = {\<C> ''DoNotUse_4ea8f2_receiver_ar__mediumRs_ar''}"

definition aBPMediumRsRan :: "channel set" where
"aBPMediumRsRan = {\<C> ''DoNotUse_4ea8f2_mediumRs_as__sender_as''}"


section \<open>Helpers to create a bundle from a single raw element\<close>

(* Do not use this, use aBPReceiverElemOut_ar_o or aBPElemOut_o instead *)
lift_definition aBPElem_raw_receiver_o__o :: "'e \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_4ea8f2_receiver_o__o'' \<mapsto> Msg (DoNotUse_4ea8f2_ABPE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

(* Do not use this, use aBPElemIn_i or aBPSenderElemIn_as_i instead *)
lift_definition aBPElem_raw_i__sender_i :: "'e \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_4ea8f2_i__sender_i'' \<mapsto> Msg (DoNotUse_4ea8f2_ABPE x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

(* Do not use this, use aBPSenderElemOut_ds or aBPMediumSrElemIn_ar instead *)
lift_definition aBPElem_raw_sender_ds__mediumSr_ar :: "('e\<times>bool) \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_4ea8f2_sender_ds__mediumSr_ar'' \<mapsto> Msg (DoNotUse_4ea8f2_ABPPair_E_Bool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

(* Do not use this, use aBPMediumSrElemOut_as or aBPReceiverElemIn_dr instead *)
lift_definition aBPElem_raw_mediumSr_as__receiver_dr :: "('e\<times>bool) \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_4ea8f2_mediumSr_as__receiver_dr'' \<mapsto> Msg (DoNotUse_4ea8f2_ABPPair_E_Bool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

(* Do not use this, use aBPReceiverElemOut_ar_o or aBPMediumRsElemIn_ar instead *)
lift_definition aBPElem_raw_receiver_ar__mediumRs_ar :: "bool \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_4ea8f2_receiver_ar__mediumRs_ar'' \<mapsto> Msg (DoNotUse_4ea8f2_ABPBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

(* Do not use this, use aBPMediumRsElemOut_as or aBPSenderElemIn_as_i instead *)
lift_definition aBPElem_raw_mediumRs_as__sender_as :: "bool \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" is
"\<lambda>x. [\<C> ''DoNotUse_4ea8f2_mediumRs_as__sender_as'' \<mapsto> Msg (DoNotUse_4ea8f2_ABPBool x)]"
  unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp


section \<open>Helpers to create a bundle from a single tsyn element\<close>

(* Do not use this, use aBPReceiverElemOut_ar_o or aBPElemOut_o instead *)
fun aBPElem_receiver_o__o :: "'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_receiver_o__o (Msg receiver_port_o__port_o) = aBPElem_raw_receiver_o__o receiver_port_o__port_o" |
"aBPElem_receiver_o__o null = sbeNull {\<C> ''DoNotUse_4ea8f2_receiver_o__o''}"

declare aBPElem_receiver_o__o.simps[simp del]

(* Do not use this, use aBPReceiverOut_ar_o or aBPOut_o instead *)
definition aBP_receiver_o__o :: "'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_receiver_o__o receiver_port_o__port_o = sbe2SB (aBPElem_receiver_o__o receiver_port_o__port_o)"

(* Do not use this, use aBPElemIn_i or aBPSenderElemIn_as_i instead *)
fun aBPElem_i__sender_i :: "'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_i__sender_i (Msg port_i__sender_port_i) = aBPElem_raw_i__sender_i port_i__sender_port_i" |
"aBPElem_i__sender_i null = sbeNull {\<C> ''DoNotUse_4ea8f2_i__sender_i''}"

declare aBPElem_i__sender_i.simps[simp del]

(* Do not use this, use aBPIn_i or aBPSenderIn_as_i instead *)
definition aBP_i__sender_i :: "'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_i__sender_i port_i__sender_port_i = sbe2SB (aBPElem_i__sender_i port_i__sender_port_i)"

(* Do not use this, use aBPSenderElemOut_ds or aBPMediumSrElemIn_ar instead *)
fun aBPElem_sender_ds__mediumSr_ar :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_sender_ds__mediumSr_ar (Msg sender_port_ds__mediumSr_port_ar) = aBPElem_raw_sender_ds__mediumSr_ar sender_port_ds__mediumSr_port_ar" |
"aBPElem_sender_ds__mediumSr_ar null = sbeNull {\<C> ''DoNotUse_4ea8f2_sender_ds__mediumSr_ar''}"

declare aBPElem_sender_ds__mediumSr_ar.simps[simp del]

(* Do not use this, use aBPSenderOut_ds or aBPMediumSrIn_ar instead *)
definition aBP_sender_ds__mediumSr_ar :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_sender_ds__mediumSr_ar sender_port_ds__mediumSr_port_ar = sbe2SB (aBPElem_sender_ds__mediumSr_ar sender_port_ds__mediumSr_port_ar)"

(* Do not use this, use aBPMediumSrElemOut_as or aBPReceiverElemIn_dr instead *)
fun aBPElem_mediumSr_as__receiver_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_mediumSr_as__receiver_dr (Msg mediumSr_port_as__receiver_port_dr) = aBPElem_raw_mediumSr_as__receiver_dr mediumSr_port_as__receiver_port_dr" |
"aBPElem_mediumSr_as__receiver_dr null = sbeNull {\<C> ''DoNotUse_4ea8f2_mediumSr_as__receiver_dr''}"

declare aBPElem_mediumSr_as__receiver_dr.simps[simp del]

(* Do not use this, use aBPMediumSrOut_as or aBPReceiverIn_dr instead *)
definition aBP_mediumSr_as__receiver_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_mediumSr_as__receiver_dr mediumSr_port_as__receiver_port_dr = sbe2SB (aBPElem_mediumSr_as__receiver_dr mediumSr_port_as__receiver_port_dr)"

(* Do not use this, use aBPReceiverElemOut_ar_o or aBPMediumRsElemIn_ar instead *)
fun aBPElem_receiver_ar__mediumRs_ar :: "bool tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_receiver_ar__mediumRs_ar (Msg receiver_port_ar__mediumRs_port_ar) = aBPElem_raw_receiver_ar__mediumRs_ar receiver_port_ar__mediumRs_port_ar" |
"aBPElem_receiver_ar__mediumRs_ar null = sbeNull {\<C> ''DoNotUse_4ea8f2_receiver_ar__mediumRs_ar''}"

declare aBPElem_receiver_ar__mediumRs_ar.simps[simp del]

(* Do not use this, use aBPReceiverOut_ar_o or aBPMediumRsIn_ar instead *)
definition aBP_receiver_ar__mediumRs_ar :: "bool tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_receiver_ar__mediumRs_ar receiver_port_ar__mediumRs_port_ar = sbe2SB (aBPElem_receiver_ar__mediumRs_ar receiver_port_ar__mediumRs_port_ar)"

(* Do not use this, use aBPMediumRsElemOut_as or aBPSenderElemIn_as_i instead *)
fun aBPElem_mediumRs_as__sender_as :: "bool tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPElem_mediumRs_as__sender_as (Msg mediumRs_port_as__sender_port_as) = aBPElem_raw_mediumRs_as__sender_as mediumRs_port_as__sender_port_as" |
"aBPElem_mediumRs_as__sender_as null = sbeNull {\<C> ''DoNotUse_4ea8f2_mediumRs_as__sender_as''}"

declare aBPElem_mediumRs_as__sender_as.simps[simp del]

(* Do not use this, use aBPMediumRsOut_as or aBPSenderIn_as_i instead *)
definition aBP_mediumRs_as__sender_as :: "bool tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_mediumRs_as__sender_as mediumRs_port_as__sender_port_as = sbe2SB (aBPElem_mediumRs_as__sender_as mediumRs_port_as__sender_port_as)"

(* Create one sbElem for all input channels *)
definition aBPElemIn_i :: "'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPElemIn_i port_i = (aBPElem_i__sender_i port_i)"

(* Create one sbElem for all output channels *)
definition aBPElemOut_o :: "'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPElemOut_o port_o = (aBPElem_receiver_o__o port_o)"

(* Create one SB for all input channels *)
definition aBPIn_i :: "'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPIn_i port_i = (sbe2SB (aBPElemIn_i port_i))"

(* Create one SB for all output channels *)
definition aBPOut_o :: "'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPOut_o port_o = (sbe2SB (aBPElemOut_o port_o))"


subsection \<open>sender\<close>

(* Create one sbElem for all input channels *)
definition aBPSenderElemIn_as_i :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPSenderElemIn_as_i port_as port_i = (aBPElem_mediumRs_as__sender_as port_as) \<plusminus> (aBPElem_i__sender_i port_i)"

(* Create one sbElem for all output channels *)
definition aBPSenderElemOut_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPSenderElemOut_ds port_ds = (aBPElem_sender_ds__mediumSr_ar port_ds)"

(* Create one SB for all input channels *)
definition aBPSenderIn_as_i :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPSenderIn_as_i port_as port_i = (sbe2SB (aBPSenderElemIn_as_i port_as port_i))"

(* Create one SB for all output channels *)
definition aBPSenderOut_ds :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPSenderOut_ds port_ds = (sbe2SB (aBPSenderElemOut_ds port_ds))"


subsection \<open>mediumSr\<close>

(* Create one sbElem for all input channels *)
definition aBPMediumSrElemIn_ar :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPMediumSrElemIn_ar port_ar = (aBPElem_sender_ds__mediumSr_ar port_ar)"

(* Create one sbElem for all output channels *)
definition aBPMediumSrElemOut_as :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPMediumSrElemOut_as port_as = (aBPElem_mediumSr_as__receiver_dr port_as)"

(* Create one SB for all input channels *)
definition aBPMediumSrIn_ar :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrIn_ar port_ar = (sbe2SB (aBPMediumSrElemIn_ar port_ar))"

(* Create one SB for all output channels *)
definition aBPMediumSrOut_as :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrOut_as port_as = (sbe2SB (aBPMediumSrElemOut_as port_as))"


subsection \<open>receiver\<close>

(* Create one sbElem for all input channels *)
definition aBPReceiverElemIn_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPReceiverElemIn_dr port_dr = (aBPElem_mediumSr_as__receiver_dr port_dr)"

(* Create one sbElem for all output channels *)
definition aBPReceiverElemOut_ar_o :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPReceiverElemOut_ar_o port_ar port_o = (aBPElem_receiver_ar__mediumRs_ar port_ar) \<plusminus> (aBPElem_receiver_o__o port_o)"

(* Create one SB for all input channels *)
definition aBPReceiverIn_dr :: "('e\<times>bool) tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPReceiverIn_dr port_dr = (sbe2SB (aBPReceiverElemIn_dr port_dr))"

(* Create one SB for all output channels *)
definition aBPReceiverOut_ar_o :: "bool tsyn \<Rightarrow> 'e tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPReceiverOut_ar_o port_ar port_o = (sbe2SB (aBPReceiverElemOut_ar_o port_ar port_o))"


subsection \<open>mediumRs\<close>

(* Create one sbElem for all input channels *)
definition aBPMediumRsElemIn_ar :: "bool tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPMediumRsElemIn_ar port_ar = (aBPElem_receiver_ar__mediumRs_ar port_ar)"

(* Create one sbElem for all output channels *)
definition aBPMediumRsElemOut_as :: "bool tsyn \<Rightarrow> ('e::countable) abpMessage tsyn sbElem" where
"aBPMediumRsElemOut_as port_as = (aBPElem_mediumRs_as__sender_as port_as)"

(* Create one SB for all input channels *)
definition aBPMediumRsIn_ar :: "bool tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsIn_ar port_ar = (sbe2SB (aBPMediumRsElemIn_ar port_ar))"

(* Create one SB for all output channels *)
definition aBPMediumRsOut_as :: "bool tsyn \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsOut_as port_as = (sbe2SB (aBPMediumRsElemOut_as port_as))"


section \<open>Helpers to create a bundle from a tsyn list of elements\<close>

(* Do not use this, use aBPReceiverOut_list_ar_o or aBPOut_list_o instead *)
fun aBP_list_receiver_o__o :: "('e tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_list_receiver_o__o (x#xs) = ubConcEq (aBP_receiver_o__o x)\<cdot>(aBP_list_receiver_o__o xs)" |
"aBP_list_receiver_o__o []     = ubLeast {\<C> ''DoNotUse_4ea8f2_receiver_o__o''}"

declare aBP_list_receiver_o__o.simps[simp del]

(* Do not use this, use aBPIn_list_i or aBPSenderIn_list_as_i instead *)
fun aBP_list_i__sender_i :: "('e tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_list_i__sender_i (x#xs) = ubConcEq (aBP_i__sender_i x)\<cdot>(aBP_list_i__sender_i xs)" |
"aBP_list_i__sender_i []     = ubLeast {\<C> ''DoNotUse_4ea8f2_i__sender_i''}"

declare aBP_list_i__sender_i.simps[simp del]

(* Do not use this, use aBPSenderOut_list_ds or aBPMediumSrIn_list_ar instead *)
fun aBP_list_sender_ds__mediumSr_ar :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_list_sender_ds__mediumSr_ar (x#xs) = ubConcEq (aBP_sender_ds__mediumSr_ar x)\<cdot>(aBP_list_sender_ds__mediumSr_ar xs)" |
"aBP_list_sender_ds__mediumSr_ar []     = ubLeast {\<C> ''DoNotUse_4ea8f2_sender_ds__mediumSr_ar''}"

declare aBP_list_sender_ds__mediumSr_ar.simps[simp del]

(* Do not use this, use aBPMediumSrOut_list_as or aBPReceiverIn_list_dr instead *)
fun aBP_list_mediumSr_as__receiver_dr :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_list_mediumSr_as__receiver_dr (x#xs) = ubConcEq (aBP_mediumSr_as__receiver_dr x)\<cdot>(aBP_list_mediumSr_as__receiver_dr xs)" |
"aBP_list_mediumSr_as__receiver_dr []     = ubLeast {\<C> ''DoNotUse_4ea8f2_mediumSr_as__receiver_dr''}"

declare aBP_list_mediumSr_as__receiver_dr.simps[simp del]

(* Do not use this, use aBPReceiverOut_list_ar_o or aBPMediumRsIn_list_ar instead *)
fun aBP_list_receiver_ar__mediumRs_ar :: "(bool tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_list_receiver_ar__mediumRs_ar (x#xs) = ubConcEq (aBP_receiver_ar__mediumRs_ar x)\<cdot>(aBP_list_receiver_ar__mediumRs_ar xs)" |
"aBP_list_receiver_ar__mediumRs_ar []     = ubLeast {\<C> ''DoNotUse_4ea8f2_receiver_ar__mediumRs_ar''}"

declare aBP_list_receiver_ar__mediumRs_ar.simps[simp del]

(* Do not use this, use aBPMediumRsOut_list_as or aBPSenderIn_list_as_i instead *)
fun aBP_list_mediumRs_as__sender_as :: "(bool tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBP_list_mediumRs_as__sender_as (x#xs) = ubConcEq (aBP_mediumRs_as__sender_as x)\<cdot>(aBP_list_mediumRs_as__sender_as xs)" |
"aBP_list_mediumRs_as__sender_as []     = ubLeast {\<C> ''DoNotUse_4ea8f2_mediumRs_as__sender_as''}"

declare aBP_list_mediumRs_as__sender_as.simps[simp del]

(* Create one SB for all input channels *)
fun aBPIn_list_i :: "('e tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPIn_list_i ((port_i)#xs) = ubConcEq (aBPIn_i port_i)\<cdot>(aBPIn_list_i xs)" |
"aBPIn_list_i [] = ubLeast aBPDom"

(* Create one SB for all output channels *)
fun aBPOut_list_o :: "('e tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPOut_list_o ((port_o)#xs) = ubConcEq (aBPOut_o port_o)\<cdot>(aBPOut_list_o xs)" |
"aBPOut_list_o [] = ubLeast aBPRan"


subsection \<open>sender\<close>

(* Create one SB for all input channels *)
fun aBPSenderIn_list_as_i :: "(bool tsyn\<times>'e tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPSenderIn_list_as_i ((port_as,port_i)#xs) = ubConcEq (aBPSenderIn_as_i port_as port_i)\<cdot>(aBPSenderIn_list_as_i xs)" |
"aBPSenderIn_list_as_i [] = ubLeast aBPSenderDom"

(* Create one SB for all output channels *)
fun aBPSenderOut_list_ds :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPSenderOut_list_ds ((port_ds)#xs) = ubConcEq (aBPSenderOut_ds port_ds)\<cdot>(aBPSenderOut_list_ds xs)" |
"aBPSenderOut_list_ds [] = ubLeast aBPSenderRan"


subsection \<open>mediumSr\<close>

(* Create one SB for all input channels *)
fun aBPMediumSrIn_list_ar :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrIn_list_ar ((port_ar)#xs) = ubConcEq (aBPMediumSrIn_ar port_ar)\<cdot>(aBPMediumSrIn_list_ar xs)" |
"aBPMediumSrIn_list_ar [] = ubLeast aBPMediumSrDom"

(* Create one SB for all output channels *)
fun aBPMediumSrOut_list_as :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrOut_list_as ((port_as)#xs) = ubConcEq (aBPMediumSrOut_as port_as)\<cdot>(aBPMediumSrOut_list_as xs)" |
"aBPMediumSrOut_list_as [] = ubLeast aBPMediumSrRan"


subsection \<open>receiver\<close>

(* Create one SB for all input channels *)
fun aBPReceiverIn_list_dr :: "(('e\<times>bool) tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPReceiverIn_list_dr ((port_dr)#xs) = ubConcEq (aBPReceiverIn_dr port_dr)\<cdot>(aBPReceiverIn_list_dr xs)" |
"aBPReceiverIn_list_dr [] = ubLeast aBPReceiverDom"

(* Create one SB for all output channels *)
fun aBPReceiverOut_list_ar_o :: "(bool tsyn\<times>'e tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPReceiverOut_list_ar_o ((port_ar,port_o)#xs) = ubConcEq (aBPReceiverOut_ar_o port_ar port_o)\<cdot>(aBPReceiverOut_list_ar_o xs)" |
"aBPReceiverOut_list_ar_o [] = ubLeast aBPReceiverRan"


subsection \<open>mediumRs\<close>

(* Create one SB for all input channels *)
fun aBPMediumRsIn_list_ar :: "(bool tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsIn_list_ar ((port_ar)#xs) = ubConcEq (aBPMediumRsIn_ar port_ar)\<cdot>(aBPMediumRsIn_list_ar xs)" |
"aBPMediumRsIn_list_ar [] = ubLeast aBPMediumRsDom"

(* Create one SB for all output channels *)
fun aBPMediumRsOut_list_as :: "(bool tsyn) list \<Rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsOut_list_as ((port_as)#xs) = ubConcEq (aBPMediumRsOut_as port_as)\<cdot>(aBPMediumRsOut_list_as xs)" |
"aBPMediumRsOut_list_as [] = ubLeast aBPMediumRsRan"


section \<open>Helpers to create a bundle from a tsyn stream of elements\<close>

lift_definition DoNotUse_4ea8f2_aBP_stream_receiver_o__o_h :: "'e tsyn stream \<Rightarrow> ('e::countable) abpMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_4ea8f2_receiver_o__o'') \<mapsto> (tsynMap (DoNotUse_4ea8f2_ABPE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use aBPReceiverOut_stream_ar_o or aBPOut_stream_o instead *)
lift_definition aBP_stream_receiver_o__o :: "('e) tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" is
"DoNotUse_4ea8f2_aBP_stream_receiver_o__o_h"
  apply(auto simp add: cfun_def DoNotUse_4ea8f2_aBP_stream_receiver_o__o_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_4ea8f2_aBP_stream_receiver_o__o_h.rep_eq ubrep_well)

lift_definition DoNotUse_4ea8f2_aBP_stream_i__sender_i_h :: "'e tsyn stream \<Rightarrow> ('e::countable) abpMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_4ea8f2_i__sender_i'') \<mapsto> (tsynMap (DoNotUse_4ea8f2_ABPE)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use aBPIn_stream_i or aBPSenderIn_stream_as_i instead *)
lift_definition aBP_stream_i__sender_i :: "('e) tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" is
"DoNotUse_4ea8f2_aBP_stream_i__sender_i_h"
  apply(auto simp add: cfun_def DoNotUse_4ea8f2_aBP_stream_i__sender_i_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_4ea8f2_aBP_stream_i__sender_i_h.rep_eq ubrep_well)

lift_definition DoNotUse_4ea8f2_aBP_stream_sender_ds__mediumSr_ar_h :: "('e\<times>bool) tsyn stream \<Rightarrow> ('e::countable) abpMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_4ea8f2_sender_ds__mediumSr_ar'') \<mapsto> (tsynMap (DoNotUse_4ea8f2_ABPPair_E_Bool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use aBPSenderOut_stream_ds or aBPMediumSrIn_stream_ar instead *)
lift_definition aBP_stream_sender_ds__mediumSr_ar :: "(('e\<times>bool)) tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" is
"DoNotUse_4ea8f2_aBP_stream_sender_ds__mediumSr_ar_h"
  apply(auto simp add: cfun_def DoNotUse_4ea8f2_aBP_stream_sender_ds__mediumSr_ar_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_4ea8f2_aBP_stream_sender_ds__mediumSr_ar_h.rep_eq ubrep_well)

lift_definition DoNotUse_4ea8f2_aBP_stream_mediumSr_as__receiver_dr_h :: "('e\<times>bool) tsyn stream \<Rightarrow> ('e::countable) abpMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_4ea8f2_mediumSr_as__receiver_dr'') \<mapsto> (tsynMap (DoNotUse_4ea8f2_ABPPair_E_Bool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use aBPMediumSrOut_stream_as or aBPReceiverIn_stream_dr instead *)
lift_definition aBP_stream_mediumSr_as__receiver_dr :: "(('e\<times>bool)) tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" is
"DoNotUse_4ea8f2_aBP_stream_mediumSr_as__receiver_dr_h"
  apply(auto simp add: cfun_def DoNotUse_4ea8f2_aBP_stream_mediumSr_as__receiver_dr_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_4ea8f2_aBP_stream_mediumSr_as__receiver_dr_h.rep_eq ubrep_well)

lift_definition DoNotUse_4ea8f2_aBP_stream_receiver_ar__mediumRs_ar_h :: "bool tsyn stream \<Rightarrow> ('e::countable) abpMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_4ea8f2_receiver_ar__mediumRs_ar'') \<mapsto> (tsynMap (DoNotUse_4ea8f2_ABPBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use aBPReceiverOut_stream_ar_o or aBPMediumRsIn_stream_ar instead *)
lift_definition aBP_stream_receiver_ar__mediumRs_ar :: "(bool) tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" is
"DoNotUse_4ea8f2_aBP_stream_receiver_ar__mediumRs_ar_h"
  apply(auto simp add: cfun_def DoNotUse_4ea8f2_aBP_stream_receiver_ar__mediumRs_ar_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_4ea8f2_aBP_stream_receiver_ar__mediumRs_ar_h.rep_eq ubrep_well)

lift_definition DoNotUse_4ea8f2_aBP_stream_mediumRs_as__sender_as_h :: "bool tsyn stream \<Rightarrow> ('e::countable) abpMessage tsyn SB" is
"\<lambda> s. [(\<C> ''DoNotUse_4ea8f2_mediumRs_as__sender_as'') \<mapsto> (tsynMap (DoNotUse_4ea8f2_ABPBool)\<cdot>s)]"
  unfolding ubWell_def usclOkay_stream_def ctype_tsyn_def
  by auto

(* Do not use this, use aBPMediumRsOut_stream_as or aBPSenderIn_stream_as_i instead *)
lift_definition aBP_stream_mediumRs_as__sender_as :: "(bool) tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" is
"DoNotUse_4ea8f2_aBP_stream_mediumRs_as__sender_as_h"
  apply(auto simp add: cfun_def DoNotUse_4ea8f2_aBP_stream_mediumRs_as__sender_as_h_def map_fun_def comp_def)
  apply(rule cont_Abs_UB)
  apply(simp add: option_one_cont)
  by (metis DoNotUse_4ea8f2_aBP_stream_mediumRs_as__sender_as_h.rep_eq ubrep_well)

(* Create one SB for all input channels *)
definition aBPIn_stream_i :: "'e tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPIn_stream_i = (\<Lambda>  port_i. (aBP_stream_i__sender_i\<cdot>port_i))"

(* Create one SB for all output channels *)
definition aBPOut_stream_o :: "'e tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPOut_stream_o = (\<Lambda>  port_o. (aBP_stream_receiver_o__o\<cdot>port_o))"


subsection \<open>sender\<close>

(* Create one SB for all input channels *)
definition aBPSenderIn_stream_as_i :: "bool tsyn stream \<rightarrow> 'e tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPSenderIn_stream_as_i = (\<Lambda>  port_as port_i. (aBP_stream_mediumRs_as__sender_as\<cdot>port_as) \<uplus> (aBP_stream_i__sender_i\<cdot>port_i))"

(* Create one SB for all output channels *)
definition aBPSenderOut_stream_ds :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPSenderOut_stream_ds = (\<Lambda>  port_ds. (aBP_stream_sender_ds__mediumSr_ar\<cdot>port_ds))"


subsection \<open>mediumSr\<close>

(* Create one SB for all input channels *)
definition aBPMediumSrIn_stream_ar :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrIn_stream_ar = (\<Lambda>  port_ar. (aBP_stream_sender_ds__mediumSr_ar\<cdot>port_ar))"

(* Create one SB for all output channels *)
definition aBPMediumSrOut_stream_as :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumSrOut_stream_as = (\<Lambda>  port_as. (aBP_stream_mediumSr_as__receiver_dr\<cdot>port_as))"


subsection \<open>receiver\<close>

(* Create one SB for all input channels *)
definition aBPReceiverIn_stream_dr :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPReceiverIn_stream_dr = (\<Lambda>  port_dr. (aBP_stream_mediumSr_as__receiver_dr\<cdot>port_dr))"

(* Create one SB for all output channels *)
definition aBPReceiverOut_stream_ar_o :: "bool tsyn stream \<rightarrow> 'e tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPReceiverOut_stream_ar_o = (\<Lambda>  port_ar port_o. (aBP_stream_receiver_ar__mediumRs_ar\<cdot>port_ar) \<uplus> (aBP_stream_receiver_o__o\<cdot>port_o))"


subsection \<open>mediumRs\<close>

(* Create one SB for all input channels *)
definition aBPMediumRsIn_stream_ar :: "bool tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsIn_stream_ar = (\<Lambda>  port_ar. (aBP_stream_receiver_ar__mediumRs_ar\<cdot>port_ar))"

(* Create one SB for all output channels *)
definition aBPMediumRsOut_stream_as :: "bool tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"aBPMediumRsOut_stream_as = (\<Lambda>  port_as. (aBP_stream_mediumRs_as__sender_as\<cdot>port_as))"


section \<open>Helpers to get tsyn elements and streams from sbElems and SBs\<close>

definition aBPElem_get_receiver_o__o :: "('e::countable) abpMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"aBPElem_get_receiver_o__o sbe = tsynApplyElem (inv DoNotUse_4ea8f2_ABPE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_4ea8f2_receiver_o__o''))"

lift_definition aBP_get_stream_receiver_o__o :: "('e::countable) abpMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_4ea8f2_ABPE)\<cdot>(sb . (\<C> ''DoNotUse_4ea8f2_receiver_o__o''))"
  by(simp add: cfun_def)

definition aBPElem_get_i__sender_i :: "('e::countable) abpMessage tsyn sbElem \<Rightarrow> ('e) tsyn" where
"aBPElem_get_i__sender_i sbe = tsynApplyElem (inv DoNotUse_4ea8f2_ABPE) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_4ea8f2_i__sender_i''))"

lift_definition aBP_get_stream_i__sender_i :: "('e::countable) abpMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_4ea8f2_ABPE)\<cdot>(sb . (\<C> ''DoNotUse_4ea8f2_i__sender_i''))"
  by(simp add: cfun_def)

definition aBPElem_get_sender_ds__mediumSr_ar :: "('e::countable) abpMessage tsyn sbElem \<Rightarrow> (('e\<times>bool)) tsyn" where
"aBPElem_get_sender_ds__mediumSr_ar sbe = tsynApplyElem (inv DoNotUse_4ea8f2_ABPPair_E_Bool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_4ea8f2_sender_ds__mediumSr_ar''))"

lift_definition aBP_get_stream_sender_ds__mediumSr_ar :: "('e::countable) abpMessage tsyn SB \<rightarrow> ('e\<times>bool) tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_4ea8f2_ABPPair_E_Bool)\<cdot>(sb . (\<C> ''DoNotUse_4ea8f2_sender_ds__mediumSr_ar''))"
  by(simp add: cfun_def)

definition aBPElem_get_mediumSr_as__receiver_dr :: "('e::countable) abpMessage tsyn sbElem \<Rightarrow> (('e\<times>bool)) tsyn" where
"aBPElem_get_mediumSr_as__receiver_dr sbe = tsynApplyElem (inv DoNotUse_4ea8f2_ABPPair_E_Bool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_4ea8f2_mediumSr_as__receiver_dr''))"

lift_definition aBP_get_stream_mediumSr_as__receiver_dr :: "('e::countable) abpMessage tsyn SB \<rightarrow> ('e\<times>bool) tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_4ea8f2_ABPPair_E_Bool)\<cdot>(sb . (\<C> ''DoNotUse_4ea8f2_mediumSr_as__receiver_dr''))"
  by(simp add: cfun_def)

definition aBPElem_get_receiver_ar__mediumRs_ar :: "('e::countable) abpMessage tsyn sbElem \<Rightarrow> (bool) tsyn" where
"aBPElem_get_receiver_ar__mediumRs_ar sbe = tsynApplyElem (inv DoNotUse_4ea8f2_ABPBool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_4ea8f2_receiver_ar__mediumRs_ar''))"

lift_definition aBP_get_stream_receiver_ar__mediumRs_ar :: "('e::countable) abpMessage tsyn SB \<rightarrow> bool tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_4ea8f2_ABPBool)\<cdot>(sb . (\<C> ''DoNotUse_4ea8f2_receiver_ar__mediumRs_ar''))"
  by(simp add: cfun_def)

definition aBPElem_get_mediumRs_as__sender_as :: "('e::countable) abpMessage tsyn sbElem \<Rightarrow> (bool) tsyn" where
"aBPElem_get_mediumRs_as__sender_as sbe = tsynApplyElem (inv DoNotUse_4ea8f2_ABPBool) ((Rep_sbElem sbe) \<rightharpoonup> (\<C> ''DoNotUse_4ea8f2_mediumRs_as__sender_as''))"

lift_definition aBP_get_stream_mediumRs_as__sender_as :: "('e::countable) abpMessage tsyn SB \<rightarrow> bool tsyn stream" is
"\<lambda>sb. tsynMap (inv DoNotUse_4ea8f2_ABPBool)\<cdot>(sb . (\<C> ''DoNotUse_4ea8f2_mediumRs_as__sender_as''))"
  by(simp add: cfun_def)


section \<open>Converter\<close>


subsection \<open>sender\<close>

lift_definition senderInConvert :: "('e::countable) abpMessage tsyn SB \<rightarrow> ('e) senderMessage tsyn SB" is
"\<lambda>sb. senderIn_stream_as_i\<cdot>(aBP_get_stream_mediumRs_as__sender_as\<cdot>sb)\<cdot>(aBP_get_stream_i__sender_i\<cdot>sb)"
  by (simp add: cfun_def)

lift_definition senderOutConvert :: "('e) senderMessage tsyn SB \<rightarrow> ('e::countable) abpMessage tsyn SB" is
"\<lambda>sb. aBPSenderOut_stream_ds\<cdot>(sender_get_stream_ds\<cdot>sb)"
  by (simp add: cfun_def)

definition senderInConverterSPF :: "('e::countable) abpMessage tsyn SB \<Rrightarrow> ('e) senderMessage tsyn SB" where
"senderInConverterSPF = ufLift aBPSenderDom senderInConvert"

definition senderOutConverterSPF :: "('e) senderMessage tsyn SB \<Rrightarrow> ('e::countable) abpMessage tsyn SB" where
"senderOutConverterSPF = ufLift aBPSenderRan senderOutConvert"


subsection \<open>mediumSr\<close>

lift_definition mediumSrInConvert :: "('e::countable) abpMessage tsyn SB \<rightarrow> (('e\<times>bool)) mediumMessage tsyn SB" is
"\<lambda>sb. mediumIn_stream_ar\<cdot>(aBP_get_stream_sender_ds__mediumSr_ar\<cdot>sb)"
  by (simp add: cfun_def)

lift_definition mediumSrOutConvert :: "(('e\<times>bool)) mediumMessage tsyn SB \<rightarrow> ('e::countable) abpMessage tsyn SB" is
"\<lambda>sb. aBPMediumSrOut_stream_as\<cdot>(medium_get_stream_as\<cdot>sb)"
  by (simp add: cfun_def)

definition mediumSrInConverterSPF :: "('e::countable) abpMessage tsyn SB \<Rrightarrow> (('e\<times>bool)) mediumMessage tsyn SB" where
"mediumSrInConverterSPF = ufLift aBPMediumSrDom mediumSrInConvert"

definition mediumSrOutConverterSPF :: "(('e\<times>bool)) mediumMessage tsyn SB \<Rrightarrow> ('e::countable) abpMessage tsyn SB" where
"mediumSrOutConverterSPF = ufLift aBPMediumSrRan mediumSrOutConvert"


subsection \<open>receiver\<close>

lift_definition receiverInConvert :: "('e::countable) abpMessage tsyn SB \<rightarrow> ('e) receiverMessage tsyn SB" is
"\<lambda>sb. receiverIn_stream_dr\<cdot>(aBP_get_stream_mediumSr_as__receiver_dr\<cdot>sb)"
  by (simp add: cfun_def)

lift_definition receiverOutConvert :: "('e) receiverMessage tsyn SB \<rightarrow> ('e::countable) abpMessage tsyn SB" is
"\<lambda>sb. aBPReceiverOut_stream_ar_o\<cdot>(receiver_get_stream_ar\<cdot>sb)\<cdot>(receiver_get_stream_o\<cdot>sb)"
  by (simp add: cfun_def)

definition receiverInConverterSPF :: "('e::countable) abpMessage tsyn SB \<Rrightarrow> ('e) receiverMessage tsyn SB" where
"receiverInConverterSPF = ufLift aBPReceiverDom receiverInConvert"

definition receiverOutConverterSPF :: "('e) receiverMessage tsyn SB \<Rrightarrow> ('e::countable) abpMessage tsyn SB" where
"receiverOutConverterSPF = ufLift aBPReceiverRan receiverOutConvert"


subsection \<open>mediumRs\<close>

lift_definition mediumRsInConvert :: "('e::countable) abpMessage tsyn SB \<rightarrow> (bool) mediumMessage tsyn SB" is
"\<lambda>sb. mediumIn_stream_ar\<cdot>(aBP_get_stream_receiver_ar__mediumRs_ar\<cdot>sb)"
  by (simp add: cfun_def)

lift_definition mediumRsOutConvert :: "(bool) mediumMessage tsyn SB \<rightarrow> ('e::countable) abpMessage tsyn SB" is
"\<lambda>sb. aBPMediumRsOut_stream_as\<cdot>(medium_get_stream_as\<cdot>sb)"
  by (simp add: cfun_def)

definition mediumRsInConverterSPF :: "('e::countable) abpMessage tsyn SB \<Rrightarrow> (bool) mediumMessage tsyn SB" where
"mediumRsInConverterSPF = ufLift aBPMediumRsDom mediumRsInConvert"

definition mediumRsOutConverterSPF :: "(bool) mediumMessage tsyn SB \<Rrightarrow> ('e::countable) abpMessage tsyn SB" where
"mediumRsOutConverterSPF = ufLift aBPMediumRsRan mediumRsOutConvert"


section \<open>Instances\<close>

definition aBPSender :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"aBPSender = (senderInConverterSPF\<circ>senderSPF\<circ>senderOutConverterSPF)"

definition aBPMediumSr :: "('e::countable) abpMessage tsyn SPS" where
"aBPMediumSr = ((uspecConst mediumSrInConverterSPF)\<circle>mediumSPS\<circle>(uspecConst mediumSrOutConverterSPF))"

definition aBPReceiver :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"aBPReceiver = (receiverInConverterSPF\<circ>receiverSPF\<circ>receiverOutConverterSPF)"

definition aBPMediumRs :: "('e::countable) abpMessage tsyn SPS" where
"aBPMediumRs = ((uspecConst mediumRsInConverterSPF)\<circle>mediumSPS\<circle>(uspecConst mediumRsOutConverterSPF))"


section \<open>Final definition\<close>

definition aBPSPS :: "('e::countable) abpMessage tsyn SPS" where
"aBPSPS = ((uspecConst aBPSender)\<Otimes>aBPMediumSr\<Otimes>(uspecConst aBPReceiver)\<Otimes>aBPMediumRs)"


section \<open>Lemmas for single tsyn setter\<close>

lemma abpelem_receiver_o__o_dom[simp]: "sbeDom (aBPElem_receiver_o__o x) = {\<C> ''DoNotUse_4ea8f2_receiver_o__o''}"
  apply(cases x)
  apply(simp add: aBPElem_receiver_o__o.simps sbeDom_def aBPElem_raw_receiver_o__o.rep_eq)
  by(simp add: aBPElem_receiver_o__o.simps)

lemma abpelem_i__sender_i_dom[simp]: "sbeDom (aBPElem_i__sender_i x) = {\<C> ''DoNotUse_4ea8f2_i__sender_i''}"
  apply(cases x)
  apply(simp add: aBPElem_i__sender_i.simps sbeDom_def aBPElem_raw_i__sender_i.rep_eq)
  by(simp add: aBPElem_i__sender_i.simps)

lemma abpelem_sender_ds__mediumsr_ar_dom[simp]: "sbeDom (aBPElem_sender_ds__mediumSr_ar x) = {\<C> ''DoNotUse_4ea8f2_sender_ds__mediumSr_ar''}"
  apply(cases x)
  apply(simp add: aBPElem_sender_ds__mediumSr_ar.simps sbeDom_def aBPElem_raw_sender_ds__mediumSr_ar.rep_eq)
  by(simp add: aBPElem_sender_ds__mediumSr_ar.simps)

lemma abpelem_mediumsr_as__receiver_dr_dom[simp]: "sbeDom (aBPElem_mediumSr_as__receiver_dr x) = {\<C> ''DoNotUse_4ea8f2_mediumSr_as__receiver_dr''}"
  apply(cases x)
  apply(simp add: aBPElem_mediumSr_as__receiver_dr.simps sbeDom_def aBPElem_raw_mediumSr_as__receiver_dr.rep_eq)
  by(simp add: aBPElem_mediumSr_as__receiver_dr.simps)

lemma abpelem_receiver_ar__mediumrs_ar_dom[simp]: "sbeDom (aBPElem_receiver_ar__mediumRs_ar x) = {\<C> ''DoNotUse_4ea8f2_receiver_ar__mediumRs_ar''}"
  apply(cases x)
  apply(simp add: aBPElem_receiver_ar__mediumRs_ar.simps sbeDom_def aBPElem_raw_receiver_ar__mediumRs_ar.rep_eq)
  by(simp add: aBPElem_receiver_ar__mediumRs_ar.simps)

lemma abpelem_mediumrs_as__sender_as_dom[simp]: "sbeDom (aBPElem_mediumRs_as__sender_as x) = {\<C> ''DoNotUse_4ea8f2_mediumRs_as__sender_as''}"
  apply(cases x)
  apply(simp add: aBPElem_mediumRs_as__sender_as.simps sbeDom_def aBPElem_raw_mediumRs_as__sender_as.rep_eq)
  by(simp add: aBPElem_mediumRs_as__sender_as.simps)

lemma abpelemin_i_dom[simp]: "sbeDom (aBPElemIn_i port_i) = aBPDom"
  by(auto simp add: aBPElemIn_i_def aBPDom_def)

lemma abpelemout_o_dom[simp]: "sbeDom (aBPElemOut_o port_o) = aBPRan"
  by(auto simp add: aBPElemOut_o_def aBPRan_def)

lemma abpin_i_dom[simp]: "ubDom\<cdot>(aBPIn_i port_i) = aBPDom"
  by(simp add: aBPIn_i_def)

lemma abpout_o_dom[simp]: "ubDom\<cdot>(aBPOut_o port_o) = aBPRan"
  by(simp add: aBPOut_o_def)


subsection \<open>sender\<close>

lemma abpsenderelemin_as_i_dom[simp]: "sbeDom (aBPSenderElemIn_as_i port_as port_i) = aBPSenderDom"
  sorry

lemma abpsenderelemout_ds_dom[simp]: "sbeDom (aBPSenderElemOut_ds port_ds) = aBPSenderRan"
  sorry

lemma abpsenderin_as_i_dom[simp]: "ubDom\<cdot>(aBPSenderIn_as_i port_as port_i) = aBPSenderDom"
  sorry

lemma abpsenderout_ds_dom[simp]: "ubDom\<cdot>(aBPSenderOut_ds port_ds) = aBPSenderRan"
  sorry


subsection \<open>mediumSr\<close>

lemma abpmediumsrelemin_ar_dom[simp]: "sbeDom (aBPMediumSrElemIn_ar port_ar) = aBPMediumSrDom"
  sorry

lemma abpmediumsrelemout_as_dom[simp]: "sbeDom (aBPMediumSrElemOut_as port_as) = aBPMediumSrRan"
  sorry

lemma abpmediumsrin_ar_dom[simp]: "ubDom\<cdot>(aBPMediumSrIn_ar port_ar) = aBPMediumSrDom"
  sorry

lemma abpmediumsrout_as_dom[simp]: "ubDom\<cdot>(aBPMediumSrOut_as port_as) = aBPMediumSrRan"
  sorry


subsection \<open>receiver\<close>

lemma abpreceiverelemin_dr_dom[simp]: "sbeDom (aBPReceiverElemIn_dr port_dr) = aBPReceiverDom"
  sorry

lemma abpreceiverelemout_ar_o_dom[simp]: "sbeDom (aBPReceiverElemOut_ar_o port_ar port_o) = aBPReceiverRan"
  sorry

lemma abpreceiverin_dr_dom[simp]: "ubDom\<cdot>(aBPReceiverIn_dr port_dr) = aBPReceiverDom"
  sorry

lemma abpreceiverout_ar_o_dom[simp]: "ubDom\<cdot>(aBPReceiverOut_ar_o port_ar port_o) = aBPReceiverRan"
  sorry


subsection \<open>mediumRs\<close>

lemma abpmediumrselemin_ar_dom[simp]: "sbeDom (aBPMediumRsElemIn_ar port_ar) = aBPMediumRsDom"
  sorry

lemma abpmediumrselemout_as_dom[simp]: "sbeDom (aBPMediumRsElemOut_as port_as) = aBPMediumRsRan"
  sorry

lemma abpmediumrsin_ar_dom[simp]: "ubDom\<cdot>(aBPMediumRsIn_ar port_ar) = aBPMediumRsDom"
  sorry

lemma abpmediumrsout_as_dom[simp]: "ubDom\<cdot>(aBPMediumRsOut_as port_as) = aBPMediumRsRan"
  sorry


section \<open>Stream-setter\<close>

lemma abp_stream_receiver_o__o_dom[simp]: "ubDom\<cdot>(aBP_stream_receiver_o__o\<cdot>x) = {\<C> ''DoNotUse_4ea8f2_receiver_o__o''}"
  by(simp add: aBP_stream_receiver_o__o.rep_eq ubdom_insert DoNotUse_4ea8f2_aBP_stream_receiver_o__o_h.rep_eq)

lemma abp_stream_i__sender_i_dom[simp]: "ubDom\<cdot>(aBP_stream_i__sender_i\<cdot>x) = {\<C> ''DoNotUse_4ea8f2_i__sender_i''}"
  by(simp add: aBP_stream_i__sender_i.rep_eq ubdom_insert DoNotUse_4ea8f2_aBP_stream_i__sender_i_h.rep_eq)

lemma abp_stream_sender_ds__mediumsr_ar_dom[simp]: "ubDom\<cdot>(aBP_stream_sender_ds__mediumSr_ar\<cdot>x) = {\<C> ''DoNotUse_4ea8f2_sender_ds__mediumSr_ar''}"
  by(simp add: aBP_stream_sender_ds__mediumSr_ar.rep_eq ubdom_insert DoNotUse_4ea8f2_aBP_stream_sender_ds__mediumSr_ar_h.rep_eq)

lemma abp_stream_mediumsr_as__receiver_dr_dom[simp]: "ubDom\<cdot>(aBP_stream_mediumSr_as__receiver_dr\<cdot>x) = {\<C> ''DoNotUse_4ea8f2_mediumSr_as__receiver_dr''}"
  by(simp add: aBP_stream_mediumSr_as__receiver_dr.rep_eq ubdom_insert DoNotUse_4ea8f2_aBP_stream_mediumSr_as__receiver_dr_h.rep_eq)

lemma abp_stream_receiver_ar__mediumrs_ar_dom[simp]: "ubDom\<cdot>(aBP_stream_receiver_ar__mediumRs_ar\<cdot>x) = {\<C> ''DoNotUse_4ea8f2_receiver_ar__mediumRs_ar''}"
  by(simp add: aBP_stream_receiver_ar__mediumRs_ar.rep_eq ubdom_insert DoNotUse_4ea8f2_aBP_stream_receiver_ar__mediumRs_ar_h.rep_eq)

lemma abp_stream_mediumrs_as__sender_as_dom[simp]: "ubDom\<cdot>(aBP_stream_mediumRs_as__sender_as\<cdot>x) = {\<C> ''DoNotUse_4ea8f2_mediumRs_as__sender_as''}"
  by(simp add: aBP_stream_mediumRs_as__sender_as.rep_eq ubdom_insert DoNotUse_4ea8f2_aBP_stream_mediumRs_as__sender_as_h.rep_eq)

lemma abpin_stream_i_dom[simp]: "ubDom\<cdot>(aBPIn_stream_i\<cdot>port_i__sender_port_i) = aBPDom"
  apply(simp add: aBPIn_stream_i_def ubclUnion_ubundle_def)
  by(auto simp add: aBPDom_def)

lemma abpout_stream_o_dom[simp]: "ubDom\<cdot>(aBPOut_stream_o\<cdot>receiver_port_o__port_o) = aBPRan"
  apply(simp add: aBPOut_stream_o_def ubclUnion_ubundle_def)
  by(auto simp add: aBPRan_def)


subsection \<open>sender\<close>

lemma abpsenderin_stream_as_i_dom[simp]: "ubDom\<cdot>(aBPSenderIn_stream_as_i\<cdot>    mediumRs_port_as__sender_port_as\<cdot>port_i__sender_port_i) = aBPSenderDom"
  apply(simp add: aBPSenderIn_stream_as_i_def ubclUnion_ubundle_def)
  by(auto simp add: aBPSenderDom_def)

lemma abpsenderout_stream_ds_dom[simp]: "ubDom\<cdot>(aBPSenderOut_stream_ds\<cdot>    sender_port_ds__mediumSr_port_ar) = aBPSenderRan"
  apply(simp add: aBPSenderOut_stream_ds_def ubclUnion_ubundle_def)
  by(auto simp add: aBPSenderRan_def)


subsection \<open>mediumSr\<close>

lemma abpmediumsrin_stream_ar_dom[simp]: "ubDom\<cdot>(aBPMediumSrIn_stream_ar\<cdot>    sender_port_ds__mediumSr_port_ar) = aBPMediumSrDom"
  apply(simp add: aBPMediumSrIn_stream_ar_def ubclUnion_ubundle_def)
  by(auto simp add: aBPMediumSrDom_def)

lemma abpmediumsrout_stream_as_dom[simp]: "ubDom\<cdot>(aBPMediumSrOut_stream_as\<cdot>    mediumSr_port_as__receiver_port_dr) = aBPMediumSrRan"
  apply(simp add: aBPMediumSrOut_stream_as_def ubclUnion_ubundle_def)
  by(auto simp add: aBPMediumSrRan_def)


subsection \<open>receiver\<close>

lemma abpreceiverin_stream_dr_dom[simp]: "ubDom\<cdot>(aBPReceiverIn_stream_dr\<cdot>    mediumSr_port_as__receiver_port_dr) = aBPReceiverDom"
  apply(simp add: aBPReceiverIn_stream_dr_def ubclUnion_ubundle_def)
  by(auto simp add: aBPReceiverDom_def)

lemma abpreceiverout_stream_ar_o_dom[simp]: "ubDom\<cdot>(aBPReceiverOut_stream_ar_o\<cdot>    receiver_port_ar__mediumRs_port_ar\<cdot>receiver_port_o__port_o) = aBPReceiverRan"
  apply(simp add: aBPReceiverOut_stream_ar_o_def ubclUnion_ubundle_def)
  by(auto simp add: aBPReceiverRan_def)


subsection \<open>mediumRs\<close>

lemma abpmediumrsin_stream_ar_dom[simp]: "ubDom\<cdot>(aBPMediumRsIn_stream_ar\<cdot>    receiver_port_ar__mediumRs_port_ar) = aBPMediumRsDom"
  apply(simp add: aBPMediumRsIn_stream_ar_def ubclUnion_ubundle_def)
  by(auto simp add: aBPMediumRsDom_def)

lemma abpmediumrsout_stream_as_dom[simp]: "ubDom\<cdot>(aBPMediumRsOut_stream_as\<cdot>    mediumRs_port_as__sender_port_as) = aBPMediumRsRan"
  apply(simp add: aBPMediumRsOut_stream_as_def ubclUnion_ubundle_def)
  by(auto simp add: aBPMediumRsRan_def)


section \<open>Lemmas for getter\<close>

subsection \<open>Identity lemmas for single sbElems\<close>

lemma abpelem_receiver_o__o_id[simp]: "aBPElem_get_receiver_o__o (aBPElem_receiver_o__o x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_receiver_o__o.simps)
  unfolding aBPElem_get_receiver_o__o_def aBPElem_raw_receiver_o__o.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma abpelem_i__sender_i_id[simp]: "aBPElem_get_i__sender_i (aBPElem_i__sender_i x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_i__sender_i.simps)
  unfolding aBPElem_get_i__sender_i_def aBPElem_raw_i__sender_i.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma abpelem_sender_ds__mediumsr_ar_id[simp]: "aBPElem_get_sender_ds__mediumSr_ar (aBPElem_sender_ds__mediumSr_ar x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_sender_ds__mediumSr_ar.simps)
  unfolding aBPElem_get_sender_ds__mediumSr_ar_def aBPElem_raw_sender_ds__mediumSr_ar.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma abpelem_mediumsr_as__receiver_dr_id[simp]: "aBPElem_get_mediumSr_as__receiver_dr (aBPElem_mediumSr_as__receiver_dr x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_mediumSr_as__receiver_dr.simps)
  unfolding aBPElem_get_mediumSr_as__receiver_dr_def aBPElem_raw_mediumSr_as__receiver_dr.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma abpelem_receiver_ar__mediumrs_ar_id[simp]: "aBPElem_get_receiver_ar__mediumRs_ar (aBPElem_receiver_ar__mediumRs_ar x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_receiver_ar__mediumRs_ar.simps)
  unfolding aBPElem_get_receiver_ar__mediumRs_ar_def aBPElem_raw_receiver_ar__mediumRs_ar.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)

lemma abpelem_mediumrs_as__sender_as_id[simp]: "aBPElem_get_mediumRs_as__sender_as (aBPElem_mediumRs_as__sender_as x) = x"
  apply(cases x)
  apply(auto simp add: aBPElem_mediumRs_as__sender_as.simps)
  unfolding aBPElem_get_mediumRs_as__sender_as_def aBPElem_raw_mediumRs_as__sender_as.rep_eq
  apply simp
  apply (meson f_inv_into_f rangeI abpMessage.inject)
  by(simp add: sbeNull.rep_eq)


subsection \<open>Identity lemmas for single SBs from streams\<close>

lemma abp_stream_receiver_o__o_id[simp]: "aBP_get_stream_receiver_o__o\<cdot>(aBP_stream_receiver_o__o\<cdot>x) = x"
  apply(simp add: aBP_get_stream_receiver_o__o.rep_eq aBP_stream_receiver_o__o.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_4ea8f2_aBP_stream_receiver_o__o_h.rep_eq)
  by (simp add: inj_def)

lemma abp_stream_i__sender_i_id[simp]: "aBP_get_stream_i__sender_i\<cdot>(aBP_stream_i__sender_i\<cdot>x) = x"
  apply(simp add: aBP_get_stream_i__sender_i.rep_eq aBP_stream_i__sender_i.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_4ea8f2_aBP_stream_i__sender_i_h.rep_eq)
  by (simp add: inj_def)

lemma abp_stream_sender_ds__mediumsr_ar_id[simp]: "aBP_get_stream_sender_ds__mediumSr_ar\<cdot>(aBP_stream_sender_ds__mediumSr_ar\<cdot>x) = x"
  apply(simp add: aBP_get_stream_sender_ds__mediumSr_ar.rep_eq aBP_stream_sender_ds__mediumSr_ar.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_4ea8f2_aBP_stream_sender_ds__mediumSr_ar_h.rep_eq)
  by (simp add: inj_def)

lemma abp_stream_mediumsr_as__receiver_dr_id[simp]: "aBP_get_stream_mediumSr_as__receiver_dr\<cdot>(aBP_stream_mediumSr_as__receiver_dr\<cdot>x) = x"
  apply(simp add: aBP_get_stream_mediumSr_as__receiver_dr.rep_eq aBP_stream_mediumSr_as__receiver_dr.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_4ea8f2_aBP_stream_mediumSr_as__receiver_dr_h.rep_eq)
  by (simp add: inj_def)

lemma abp_stream_receiver_ar__mediumrs_ar_id[simp]: "aBP_get_stream_receiver_ar__mediumRs_ar\<cdot>(aBP_stream_receiver_ar__mediumRs_ar\<cdot>x) = x"
  apply(simp add: aBP_get_stream_receiver_ar__mediumRs_ar.rep_eq aBP_stream_receiver_ar__mediumRs_ar.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_4ea8f2_aBP_stream_receiver_ar__mediumRs_ar_h.rep_eq)
  by (simp add: inj_def)

lemma abp_stream_mediumrs_as__sender_as_id[simp]: "aBP_get_stream_mediumRs_as__sender_as\<cdot>(aBP_stream_mediumRs_as__sender_as\<cdot>x) = x"
  apply(simp add: aBP_get_stream_mediumRs_as__sender_as.rep_eq aBP_stream_mediumRs_as__sender_as.rep_eq)
  apply(simp add: ubGetCh_def DoNotUse_4ea8f2_aBP_stream_mediumRs_as__sender_as_h.rep_eq)
  by (simp add: inj_def)


subsection \<open>Identity lemmas for input sbElems\<close>

lemma abpelemin_i_i__sender_i_id[simp]: "aBPElem_get_i__sender_i (aBPElemIn_i port_i__sender_port_i) = port_i__sender_port_i"
  apply(simp add: aBPElemIn_i_def aBPElem_get_i__sender_i_def)
  by(metis aBPElem_get_i__sender_i_def abpelem_i__sender_i_id)


subsection \<open>Identity lemmas for output sbElems\<close>

lemma abpelemout_o_receiver_o__o_id[simp]: "aBPElem_get_receiver_o__o (aBPElemOut_o receiver_port_o__port_o) = receiver_port_o__port_o"
  apply(simp add: aBPElemOut_o_def aBPElem_get_receiver_o__o_def)
  by(metis aBPElem_get_receiver_o__o_def abpelem_receiver_o__o_id)


subsection \<open>Identity lemmas for input SBs\<close>

lemma abpin_i_i__sender_i_id[simp]: "aBP_get_stream_i__sender_i\<cdot>(aBPIn_i port_i__sender_port_i) = \<up>port_i__sender_port_i"
  apply(simp add: aBP_get_stream_i__sender_i_def aBPIn_i_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: aBPDom_def aBPElemIn_i_def)
  apply(cases port_i__sender_port_i)
  apply(auto simp add: aBPElem_i__sender_i.simps)
  unfolding aBPElem_get_i__sender_i_def aBPElem_raw_i__sender_i.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)


subsection \<open>Identity lemmas for output SBs\<close>

lemma abpout_o_receiver_o__o_id[simp]: "aBP_get_stream_receiver_o__o\<cdot>(aBPOut_o receiver_port_o__port_o) = \<up>receiver_port_o__port_o"
  apply(simp add: aBP_get_stream_receiver_o__o_def aBPOut_o_def)
  apply(subst sbe2sb_getch)
  apply(auto simp add: aBPDom_def aBPElemOut_o_def)
  apply(cases receiver_port_o__port_o)
  apply(auto simp add: aBPElem_receiver_o__o.simps)
  unfolding aBPElem_get_receiver_o__o_def aBPElem_raw_receiver_o__o.rep_eq
  apply(simp add: inj_def)
  by(simp add: sbeNull.rep_eq)


subsection \<open>Identity lemmas for input SBs from streams\<close>

lemma abpin_stream_i_i__sender_i_id[simp]: "aBP_get_stream_i__sender_i\<cdot>(aBPIn_stream_i\<cdot>port_i__sender_port_i) = port_i__sender_port_i"
  apply(auto simp add: aBP_get_stream_i__sender_i.rep_eq aBPIn_stream_i_def ubclUnion_ubundle_def)
  by (metis aBP_get_stream_i__sender_i.rep_eq abp_stream_i__sender_i_id)


subsection \<open>Identity lemmas for output SBs from streams\<close>

lemma abpout_stream_o_receiver_o__o_id[simp]: "aBP_get_stream_receiver_o__o\<cdot>(aBPOut_stream_o\<cdot>receiver_port_o__port_o) = receiver_port_o__port_o"
  apply(auto simp add: aBP_get_stream_receiver_o__o.rep_eq aBPOut_stream_o_def ubclUnion_ubundle_def)
  by (metis aBP_get_stream_receiver_o__o.rep_eq abp_stream_receiver_o__o_id)


end