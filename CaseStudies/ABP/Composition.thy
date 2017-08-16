(*  Title:        Composition.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory Composition
imports Medium Receiver

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition of the set of sender *}
(* ----------------------------------------------------------------------- *)

type_synonym 'a sender = "('a tstream \<rightarrow> bool tstream  \<rightarrow> ('a \<times> bool) tstream)"

definition tsSender :: "('a sender) set" where
"tsSender = {send :: 'a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream. 
  \<forall>i as. 
  tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i \<and> 
  tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<and>
  #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))) \<and>
  (#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>)
}"

lemma set2tssnd_prefix_inp: assumes "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i"
  using assms tsSender_def by auto

lemma set2tssnd_alt_bit: assumes "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))"
  using assms tsSender_def by auto

lemma set2tssnd_alt_bit_tabs: assumes "send \<in> tsSender"
  shows "srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(send\<cdot>i\<cdot>as)))) 
    = (sprojsnd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(send\<cdot>i\<cdot>as))))"
  by (metis assms set2tssnd_alt_bit tsprojsnd_tsabs tsremdups_tsabs)
    
lemma set2tssnd_ack2trans: assumes "send \<in> tsSender"
  shows "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
  using assms tsSender_def by auto

lemma set2tssnd_nack2inftrans: assumes "send \<in> tsSender"
  shows "(#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>)"
  using assms tsSender_def by auto

lemma set2tssnd_ack2trans2: assumes "send\<in>tsSender"
  shows "#(tsAbs\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) 
    = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"  
  using assms(1) set2tssnd_ack2trans by simp
       
lemma  assumes "send\<in>tsSender"
  shows "#(tsAbs\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<le> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
using assms(1) set2tssnd_ack2trans by fastforce
   
lemma assumes "send\<in>tsSender" and "#(tsAbs\<cdot>as) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<le> # (tsAbs\<cdot>(tsRemDups\<cdot>as))"
 oops
  
  

(* ----------------------------------------------------------------------- *)
subsection {* sender and receiver composition *}
(* ----------------------------------------------------------------------- *)

text {* 
   i = input stream
   as = acks stream
   ds = output stream 
*}
    
lemma tssnd_tsprojsnd_tsremdups: 
  assumes send_def: "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(send\<cdot>i\<cdot>as))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))"
  apply (simp add: tsprojsnd_tsabs tsremdups_tsabs sprojsnd_def)
  by (metis eta_cfun send_def set2tssnd_alt_bit_tabs sprojsnd_def srcdups_smap_com)
    
lemma tsaltbitpro_inp2out_nmed:
  assumes send_def: "send \<in> tsSender"
    and out_def: "ds = send\<cdot>i\<cdot>as"
    and acks_def: "as = tsProjSnd\<cdot>ds"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
proof -
  have "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))))"
    by (metis acks_def out_def tsprojfst_tsabs_slen tsprojsnd_tsabs_slen 
        tssnd_tsprojsnd_tsremdups send_def)
  thus "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
    by (metis eq_slen_eq_and_less min_rek out_def send_def set2tssnd_ack2trans 
        set2tssnd_prefix_inp tsrecsnd_insert)
  qed

(* ----------------------------------------------------------------------- *)
subsection {* sender, receiver and second medium composition *}
(* ----------------------------------------------------------------------- *)

lemma tsaltbitpro_inp2out_sndmed_shd:
  assumes send_def: "send \<in> tsSender"
    and ora_def: "#({True} \<ominus> p2) = \<infinity>"
    and out_def: "ds = send\<cdot>i\<cdot>as"
    and acks2med_def: "ar = tsProjSnd\<cdot>ds"
    and acks2snd_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "shd (tsAbs\<cdot>(tsRecSnd\<cdot>ds)) = shd (tsAbs\<cdot>i)"
  by (metis below_shd bot_is_0 eq_slen_eq_and_less lnat.con_rews min_def out_def send_def 
      set2tssnd_ack2trans set2tssnd_prefix_inp strict_slen tsrecsnd_insert)

text {*
   i = input stream
   as = acks stream (in sender)
   ar = acks stream (from receiver)
   ds = output stream (from sender)
   p2 = oracle stream
*}

lemma tsaltbitpro_inp2out_nmed2:
  assumes send_def: "send \<in> tsSender"
    and out_def: "ds = send\<cdot>i\<cdot>as"
    and acks_def: "as = tsProjSnd\<cdot>ds"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
proof -
  have h1: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRecSnd\<cdot>ds))"
    by (metis acks_def eq_iff out_def send_def tsprojfst_tsabs_slen tsprojsnd_tsabs_slen 
        tsrecsnd_insert tssnd_tsprojsnd_tsremdups)
  hence h2: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
    by (metis le_less less_imp_le min_less_iff_conj min_rek out_def send_def set2tssnd_ack2trans
        tsrecsnd_insert)
  have h3: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) 
              \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
    by (metis le_less_linear min_absorb2 send_def set2tssnd_ack2trans)
  hence h4: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<or> (#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<or> #(tsAbs\<cdot>as) < \<infinity>)"
    by (metis acks_def eq_iff min_rek out_def send_def set2tssnd_ack2trans tsprojfst_tsabs_slen 
        tsprojsnd_tsabs_slen tssnd_tsprojsnd_tsremdups)
  hence h5: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<or> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity>"
    by (metis acks_def leI neq_iff out_def send_def set2tssnd_nack2inftrans tsprojsnd_tsabs_slen)
  hence h6: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<ge> #(tsAbs\<cdot>i)"
    by auto
  show "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
    by (metis dual_order.antisym eq_slen_eq_and_less h2 h6 less_lnsuc min.absorb1 out_def send_def
        set2tssnd_ack2trans set2tssnd_prefix_inp tsrecsnd_insert)
  qed

lemma tsaltbitpro_inp2out_sndmed_assm:
  assumes send_def: "send \<in> tsSender"
    and ora_def: "#({True} \<ominus> p2) = \<infinity>"
    and out_def: "ds = send\<cdot>i\<cdot>as"
    and acks2med_def: "ar = tsProjSnd\<cdot>ds"
    and acks2snd_def: "as = tsMed\<cdot>ar\<cdot>p2"
    and "#(tsAbs\<cdot>ds) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<or> #(tsAbs\<cdot>as) < \<infinity>"
proof -
  have ora_inf: "#p2 = \<infinity>"
    using ora_def sfilterl4 by auto
  hence tsmed_tsprojsnd: "tsMed\<cdot>(tsProjSnd\<cdot>ds)\<cdot>p2 = tsProjSnd\<cdot>(tsMed\<cdot>ds\<cdot>p2)"
    by (simp add: tsprojsnd_insert tsmed_map)
  thus "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<or> #(tsAbs\<cdot>as) < \<infinity>"
    apply (simp add: acks2snd_def acks2med_def)
    sorry
  qed

lemma tssnd_tsprojsnd_tsremdups_med: 
  assumes send_def: "send \<in> tsSender"
    and ora_def: "#({True} \<ominus> p2) = \<infinity>"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>(send\<cdot>i\<cdot>as)\<cdot>p2))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>(send\<cdot>i\<cdot>as)\<cdot>p2)))"
  sorry

(* oops-Lemmata in Medium *)
text {* If infinite messages will be sent infinite messages will be transmitted. *}
lemma tsmed_tsabs_slen_inf [simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(tsAbs\<cdot>msg)=\<infinity>" 
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
  sorry

lemma tsaltbitpro_inp2out_sndmed:
  assumes send_def: "send \<in> tsSender"
(*
  tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i 
  tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))
  #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))
  (#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>)
*)
    and ora_def: "#({True} \<ominus> p2) = \<infinity>"
    and out_def: "ds = send\<cdot>i\<cdot>as"
    and acks2med_def: "ar = tsProjSnd\<cdot>ds"
    and acks2snd_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
proof -
  have ora_inf: "#p2 = \<infinity>"
    using ora_def sfilterl4 by auto
  hence tsmed_tsprojsnd: "tsMed\<cdot>(tsProjSnd\<cdot>ds)\<cdot>p2 = tsProjSnd\<cdot>(tsMed\<cdot>ds\<cdot>p2)"
    by (simp add: tsprojsnd_insert tsmed_map)
  have h1: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRecSnd\<cdot>ds))"
    apply (simp add: acks2med_def acks2snd_def tsmed_tsprojsnd tsrecsnd_insert)
    apply (subst out_def)
    apply (subst tssnd_tsprojsnd_tsremdups_med)
    apply (simp_all add: send_def ora_def)
    apply (subst out_def)
    sorry
  hence h2: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
    by (metis le_less less_imp_le min_less_iff_conj min_rek out_def send_def set2tssnd_ack2trans
        tsrecsnd_insert)
  
  have h3: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) 
              \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
    by (metis le_less_linear min_absorb2 send_def set2tssnd_ack2trans)
  hence h4: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<or> (#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<or> #(tsAbs\<cdot>as) < \<infinity>)"
    by (metis acks2med_def acks2snd_def leI ora_def out_def send_def set2tssnd_nack2inftrans 
        tsaltbitpro_inp2out_sndmed_assm)
  hence h5: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<or> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity>"
    using acks2med_def acks2snd_def le_less_linear neq_iff ora_def out_def send_def set2tssnd_nack2inftrans by fastforce
  hence h6: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<ge> #(tsAbs\<cdot>i)"
    by auto
  show "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
    by (metis dual_order.antisym eq_slen_eq_and_less h2 h6 less_lnsuc min.absorb1 out_def send_def
        set2tssnd_ack2trans set2tssnd_prefix_inp tsrecsnd_insert)
  oops
    
(* ----------------------------------------------------------------------- *)
subsection {* complete composition *}
(* ----------------------------------------------------------------------- *)

text {* 
   i = input stream
   as = acks stream (in sender)
   ar = acks stream (from receiver)
   ds = output stream (from sender)
   dr = output stream (in receiver)
   p1/p2 = oracle stream
*}

lemma tsaltbitpro_inp2out:
  assumes "send \<in> tsSender"
    and "#({True} \<ominus> p1) = \<infinity>"
    and "#({True} \<ominus> p2) = \<infinity>"
    and "ds = send\<cdot>i\<cdot>as"
    and "dr = tsMed\<cdot>ds\<cdot>p1"
    and "ar = tsProjSnd\<cdot>dr"
    and "as = tsMed\<cdot>ar\<cdot>p2"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>dr) = tsAbs\<cdot>i"
  oops
    
end