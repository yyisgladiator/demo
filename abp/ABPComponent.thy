(*
 * DO NOT MODIFY!
 * This file was generated from ABP.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 *  1.0.0
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


(* SWS: Und noch die normalen definitionen/lemma über den globalen Datentypen *)


(* SWS: channel heißt hier anders, aber für simplicity lasse ich das auf dr *)
lift_definition abp_get_stream_dr :: "('e::countable) abpMessage tsyn SB \<rightarrow> ('e\<times>bool) tsyn stream" is
"undefined"
  sorry

(* SWS: ToDo: bessere namen/soll sich an bisherige konventionen halten *)
definition abpReceiverIn_stream_dr :: "('e\<times>bool) tsyn stream \<rightarrow> ('e::countable) abpMessage tsyn SB" where
"abpReceiverIn_stream_dr =  undefined"





(* TODO Channel renamen für die Lampe? *)
section \<open>Instanzen der Sub-Komponenten\<close>


definition sender :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"sender = undefined"

definition mediumSr :: "('e::countable) abpMessage tsyn SPS" where
"mediumSr = undefined"


lift_definition recevierInConvert::"('e::countable) abpMessage tsyn SB \<rightarrow> 'e receiverMessage tsyn SB" is
"\<lambda>sb. receiverIn_stream_dr\<cdot>(abp_get_stream_dr\<cdot>sb)"
  by (simp add: cfun_def)

lift_definition recevierInConverterSPF::"('e::countable) abpMessage tsyn SB \<Rrightarrow> 'e receiverMessage tsyn SB" is
"(\<Lambda> sb . ((ubDom\<cdot>sb = undefined (* TODO *)) \<leadsto> recevierInConvert\<cdot>sb))"
  sorry

lift_definition recevierOutConvert::"('e::countable) receiverMessage tsyn SB \<rightarrow> 'e abpMessage tsyn SB" is
"\<lambda>sb. abpReceiverIn_stream_dr\<cdot>(receiver_get_stream_dr\<cdot>sb)"
  by (simp add: cfun_def)

lift_definition recevierOutConverterSPF::"('e::countable) receiverMessage tsyn SB \<Rrightarrow> 'e abpMessage tsyn SB" is
"(\<Lambda> sb . ((ubDom\<cdot>sb = undefined (*ToDo *)) \<leadsto> recevierOutConvert\<cdot>sb))"
  sorry


(* SWS: Receiver im neuen Datentypen *)
definition receiver :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"receiver = ufSerComp (ufSerComp recevierInConverterSPF receiverSPF)  recevierOutConverterSPF"
(* Es gibt eine infix-Notation für ufSerComp ... klappt aber nicht so richtig *)

definition mediumRs :: "('e::countable) abpMessage tsyn SPS" where
"mediumRs = undefined"


section \<open>Die Komponente selbst\<close>

definition abp :: "('e::countable) abpMessage tsyn SPS" where
"abp = (spf2Sps(sender) \<Otimes>  mediumSr \<Otimes>  spf2Sps(receiver) \<Otimes>  mediumRs)"


end