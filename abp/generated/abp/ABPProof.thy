(*
 * DO NOT MODIFY!
 * This file was generated from ABP.maa and will be overridden when changed. To change
 * permanently, consider changing the model itself.
 *
 * Generated on Oct 18, 2018 11:59:05 PM by isartransformer 3.1.0
 *)
theory ABPProof
  imports ABPComponent

begin

lemma final:
    assumes "uspec_in someSPF aBPSPS"
     shows  "tsynAbs\<cdot>(aBP_get_stream_receiver_o__o\<cdot>(someSPF\<rightleftharpoons>(aBPIn_stream_i\<cdot>s))) \<sqsubseteq> tsynAbs\<cdot>s"
  oops


end