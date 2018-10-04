(*
 * DO NOT MODIFY!
 * This file was generated from ABP.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 1.0.0
 *)
theory ABPComponent
  imports ABPDatatype
          SenderAutomaton MediumAutomaton ReceiverAutomaton
          spec.SPS spec.USpec_UFunComp

begin


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


section \<open>Instances and Final Definition\<close>

definition aBPSender :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"aBPSender = (senderInConverterSPF\<circ>senderSPF\<circ>senderOutConverterSPF)"

definition aBPMediumSr :: "('e::countable) abpMessage tsyn SPS" where
"aBPMediumSr = ((uspecConst mediumSrInConverterSPF)\<circle>mediumSPS\<circle>(uspecConst mediumSrOutConverterSPF))"

definition aBPReceiver :: "(('e::countable) abpMessage tsyn, ('e::countable) abpMessage tsyn) SPF" where
"aBPReceiver = (receiverInConverterSPF\<circ>receiverSPF\<circ>receiverOutConverterSPF)"

definition aBPMediumRs :: "('e::countable) abpMessage tsyn SPS" where
"aBPMediumRs = ((uspecConst mediumRsInConverterSPF)\<circle>mediumSPS\<circle>(uspecConst mediumRsOutConverterSPF))"

definition aBPSPS :: "('e::countable) abpMessage tsyn SPS" where
"aBPSPS = ((uspecConst aBPSender)\<Otimes>aBPMediumSr\<Otimes>(uspecConst aBPReceiver)\<Otimes>aBPMediumRs)"


end