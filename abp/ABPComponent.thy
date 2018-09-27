(*
 * DO NOT MODIFY!
 * This file was generated from ABP.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 1.0.0
 *)
theory ABPComponent
  imports ReceiverAutomaton SenderAutomaton MediumAutomaton

begin

(* Dummy *)
definition uspecComp :: "('m,'m) ufun uspec \<Rightarrow> ('m,'m) ufun uspec \<Rightarrow> ('m,'m) ufun uspec" (infixl "\<Otimes>" 50) where
"uspecComp S1 S2 \<equiv> undefined"

(* Dummy *)
definition spf2Sps :: "('m,'m) SPF \<Rightarrow> 'm SPS" where
"spf2Sps f = undefined"


section \<open>Datatype definition\<close>

datatype ('e::countable) abpMessage = AbpPair_E_Bool "('e\<times>bool)" | AbpBool "bool" | AbpE "'e"

instance abpMessage :: (countable) countable
  apply(intro_classes)
  by(countable_datatype)

instantiation abpMessage :: (countable) message
begin
  fun ctype_abpMessage :: "channel \<Rightarrow> ('e::countable) abpMessage set" where
  "ctype_abpMessage c = (
    if c = \<C> ''sender_i'' then range AbpE else
    if c = \<C> ''sender_ds__mediumSr_ar'' then range AbpPair_E_Bool else
    if c = \<C> ''mediumSr_as__receiver_dr'' then range AbpPair_E_Bool else
    if c = \<C> ''receiver_ar__mediumRs_ar'' then range AbpBool else
    if c = \<C> ''receiver_o'' then range AbpE else
    if c = \<C> ''mediumRs_as__sender_as'' then range AbpBool else
    undefined)"
  instance
    by(intro_classes)
end


section \<open>Getter and Setter\<close>

(* mediumSr.as \<rightarrow> receiver.dr *)
lift_definition abp_get_stream_mediumSr_as__receiver_dr :: "('e::countable) abpMessage tsyn SB \<rightarrow> ('e\<times>bool) tsyn stream" is
"undefined"
  sorry

(* i \<rightarrow> sender.i *)
lift_definition abp_get_stream_i__sender_i :: "('e::countable) abpMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"undefined"
  sorry

(* mediumRs.as \<rightarrow> sender.as *)
lift_definition abp_get_stream_mediumRs_as__sender_as :: "('e::countable) abpMessage tsyn SB \<rightarrow> bool tsyn stream" is
"undefined"
  sorry

(* sender.ds \<rightarrow> mediumSr.ar *)
lift_definition abp_get_stream_sender_ds__mediumSr_ar :: "('e::countable) abpMessage tsyn SB \<rightarrow> 'e tsyn stream" is
"undefined"
  sorry

definition abpReceiverOut_stream_ar_o :: "bool tsyn stream \<rightarrow> 'e tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"abpReceiverOut_stream_ar_o =  undefined"

definition abpSenderOut_stream_ds :: "('e\<times>bool) tsyn stream \<rightarrow> 'e abpMessage tsyn SB" where
"abpSenderOut_stream_ds = undefined"


section \<open>Converter\<close>

(* Receiver *)
lift_definition receiverInConvert::"('e::countable) abpMessage tsyn SB \<rightarrow> 'e receiverMessage tsyn SB" is
"\<lambda>sb. receiverIn_stream_dr\<cdot>(abp_get_stream_mediumSr_as__receiver_dr\<cdot>sb)"
  by (simp add: cfun_def)

lift_definition receiverOutConvert::"('e::countable) receiverMessage tsyn SB \<rightarrow> 'e abpMessage tsyn SB" is
"\<lambda>sb. abpReceiverOut_stream_ar_o\<cdot>(receiver_get_stream_ar\<cdot>sb)\<cdot>(receiver_get_stream_o\<cdot>sb)"
  by (simp add: cfun_def)

(* Sender *)
lift_definition senderInConvert::"('e::countable) abpMessage tsyn SB \<rightarrow> 'e senderMessage tsyn SB" is
"\<lambda>sb. senderIn_stream_as_i\<cdot>(abp_get_stream_mediumRs_as__sender_as\<cdot>sb)\<cdot>(abp_get_stream_i__sender_i\<cdot>sb)"
  by (simp add: cfun_def)

lift_definition senderOutConvert::"('e::countable) senderMessage tsyn SB \<rightarrow> 'e abpMessage tsyn SB" is
"\<lambda>sb. abpSenderOut_stream_ds\<cdot>(sender_get_stream_ds\<cdot>sb)"
  by (simp add: cfun_def)


section \<open>Alternative Converter mit Serieller Komposition\<close>

lift_definition receiverInConverterSPF::"('e::countable) abpMessage tsyn SB \<Rrightarrow> 'e receiverMessage tsyn SB" is
"(\<Lambda> sb . ((ubDom\<cdot>sb = undefined) \<leadsto> receiverInConvert\<cdot>sb))"
  sorry

lift_definition receiverOutConverterSPF::"('e::countable) receiverMessage tsyn SB \<Rrightarrow> 'e abpMessage tsyn SB" is
"(\<Lambda> sb . ((ubDom\<cdot>sb = undefined) \<leadsto> receiverOutConvert\<cdot>sb))"
  sorry


section \<open>Instanzen der Sub-Komponenten\<close>

definition sender :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"sender = ufApplyIn senderInConvert\<cdot>(ufApplyOut senderOutConvert\<cdot>senderSPF)"

definition mediumSr :: "('e::countable) abpMessage tsyn SPS" where
"mediumSr = undefined"

definition receiver :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"receiver = ufApplyIn receiverInConvert\<cdot>(ufApplyOut receiverOutConvert\<cdot>receiverSPF)"

definition mediumRs :: "('e::countable) abpMessage tsyn SPS" where
"mediumRs = undefined"


section \<open>Alternative Instanzen mit den alternativen Convertern\<close>

definition receiver2 :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"receiver2 = (receiverInConverterSPF \<circ> receiverSPF \<circ> receiverOutConverterSPF)"


section \<open>Die Komponente selbst\<close>

definition abp :: "('e::countable) abpMessage tsyn SPS" where
"abp = (spf2Sps(sender) \<Otimes>  mediumSr \<Otimes>  spf2Sps(receiver) \<Otimes>  mediumRs)"


end