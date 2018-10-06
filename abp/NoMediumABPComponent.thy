(*
 * DO NOT MODIFY!
 * This file was generated from NoMediumABP.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * isartransformer 1.0.0
 *)
theory NoMediumABPComponent
  imports NoMediumABPDatatype
          SenderAutomaton ReceiverAutomaton
          spec.SPS spec.USpec_UFunComp

begin


section \<open>Converter\<close>


subsection \<open>sender\<close>

lift_definition senderInConvert :: "('e::countable) noMediumABPMessage tsyn SB \<rightarrow> ('e) senderMessage tsyn SB" is
"\<lambda>sb. senderIn_stream_as_i\<cdot>(noMediumABP_get_stream_receiver_ar__sender_as\<cdot>sb)\<cdot>(noMediumABP_get_stream_i__sender_i\<cdot>sb)"
  by (simp add: cfun_def)

lift_definition senderOutConvert :: "('e) senderMessage tsyn SB \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" is
"\<lambda>sb. noMediumABPSenderOut_stream_ds\<cdot>(sender_get_stream_ds\<cdot>sb)"
  by (simp add: cfun_def)

definition senderInConverterSPF :: "('e::countable) noMediumABPMessage tsyn SB \<Rrightarrow> ('e) senderMessage tsyn SB" where
"senderInConverterSPF = ufLift noMediumABPSenderDom senderInConvert"

definition senderOutConverterSPF :: "('e) senderMessage tsyn SB \<Rrightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"senderOutConverterSPF = ufLift noMediumABPSenderRan senderOutConvert"


subsection \<open>receiver\<close>

lift_definition receiverInConvert :: "('e::countable) noMediumABPMessage tsyn SB \<rightarrow> ('e) receiverMessage tsyn SB" is
"\<lambda>sb. receiverIn_stream_dr\<cdot>(noMediumABP_get_stream_sender_ds__receiver_dr\<cdot>sb)"
  by (simp add: cfun_def)

lift_definition receiverOutConvert :: "('e) receiverMessage tsyn SB \<rightarrow> ('e::countable) noMediumABPMessage tsyn SB" is
"\<lambda>sb. noMediumABPReceiverOut_stream_ar_o\<cdot>(receiver_get_stream_ar\<cdot>sb)\<cdot>(receiver_get_stream_o\<cdot>sb)"
  by (simp add: cfun_def)

definition receiverInConverterSPF :: "('e::countable) noMediumABPMessage tsyn SB \<Rrightarrow> ('e) receiverMessage tsyn SB" where
"receiverInConverterSPF = ufLift noMediumABPReceiverDom receiverInConvert"

definition receiverOutConverterSPF :: "('e) receiverMessage tsyn SB \<Rrightarrow> ('e::countable) noMediumABPMessage tsyn SB" where
"receiverOutConverterSPF = ufLift noMediumABPReceiverRan receiverOutConvert"


section \<open>Instances and Final Definition\<close>

definition noMediumABPSender :: "(('e::countable) noMediumABPMessage tsyn, ('e::countable) noMediumABPMessage tsyn) SPF" where
"noMediumABPSender = (senderInConverterSPF\<circ>senderSPF\<circ>senderOutConverterSPF)"

definition noMediumABPReceiver :: "(('e::countable) noMediumABPMessage tsyn, ('e::countable) noMediumABPMessage tsyn) SPF" where
"noMediumABPReceiver = (receiverInConverterSPF\<circ>receiverSPF\<circ>receiverOutConverterSPF)"

definition noMediumABPSPF :: "(('e::countable) noMediumABPMessage tsyn, ('e::countable) noMediumABPMessage tsyn) SPF" where
"noMediumABPSPF = (noMediumABPSender\<otimes>noMediumABPReceiver)"


end