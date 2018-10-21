(*
 * DO NOT MODIFY!
 * This file was generated from NoMediumABP.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 18, 2018 11:59:05 PM by isartransformer 3.1.0
 *)
theory NoMediumABPProof
  imports NoMediumABPComponent

begin

lemma final: "tsynAbs\<cdot>(noMediumABP_get_stream_receiver_o__o\<cdot>(noMediumABPSPF\<rightleftharpoons>(noMediumABPIn_stream_i\<cdot>s))) \<sqsubseteq> tsynAbs\<cdot>s"
  oops


end