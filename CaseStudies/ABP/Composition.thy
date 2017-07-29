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

(* ----------------------------------------------------------------------- *)
subsection {* sender and receiver composition *}
(* ----------------------------------------------------------------------- *)

text {* 
   i = input stream
   as = acks stream
   ds = output stream 
*}

lemma srcdups_smap_adm [simp]: 
  "adm (\<lambda>a. srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>a)) = smap f\<cdot>(srcdups\<cdot>a) 
    \<longrightarrow> srcdups\<cdot>(smap f\<cdot>a) = smap f\<cdot>(srcdups\<cdot>a))"
  apply(rule admI)
  apply (auto simp add: contlub_cfun_arg)
    sorry
    
      declare [[show_types]]
(* Move to Streams.thy after done *)
lemma srcdups_smap_com:
  shows "srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>s)) = smap f\<cdot>(srcdups\<cdot>s) \<Longrightarrow> srcdups\<cdot>(smap f\<cdot>s)= smap f\<cdot>(srcdups\<cdot>s)"
  proof(induction rule: ind [of _ s])
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case by simp
  next
    case (3 a s)
    have s_eps: "s = \<bottom> \<Longrightarrow>  srcdups\<cdot>(\<up>(f a) \<bullet> smap f\<cdot>s) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s))" by simp
    hence f1: "shd s = a \<Longrightarrow> ?case"
      by (metis "3.IH" "3.prems" smap_scons srcdups_eq surj_scons)
    have h1: "s\<noteq>\<bottom> \<Longrightarrow> s = (\<up>(shd s) \<bullet> srt\<cdot>s)" by (simp add: surj_scons)
    have h2: "s\<noteq>\<bottom> \<Longrightarrow> shd s\<noteq>a \<Longrightarrow>f (shd s) \<noteq> f a \<Longrightarrow> srcdups\<cdot>(smap f\<cdot>(\<up>a \<bullet> (\<up>(shd s) \<bullet> srt\<cdot>s))) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet>  (\<up>(shd s) \<bullet> srt\<cdot>s)))" 
      apply simp using "3.IH" sorry
    have f2: "s\<noteq>\<bottom> \<Longrightarrow> shd s\<noteq>a \<Longrightarrow>f (shd s) \<noteq> f a \<Longrightarrow> ?case"
      using h1 h2 by auto 
    have f3: "s\<noteq>\<bottom> \<Longrightarrow> shd s\<noteq>a \<Longrightarrow>f (shd s) = f a \<Longrightarrow> ?case" sorry (* This case can never occur, see assumption *)
      
    then show ?case using f1 f2 by fastforce
  qed
    
lemma tssnd_tsprojsnd_tsremdups: 
  assumes send_def: "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(send\<cdot>i\<cdot>as))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))"
  apply (simp add: tsprojsnd_tsabs tsremdups_tsabs sprojsnd_def)
    using srcdups_smap_com assms set2tssnd_alt_bit_tabs srcdups_smap_com
    by (metis Abs_cfun_inverse2 cont_Rep_cfun2 sprojsnd_def)
    
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

text {*
   i = input stream
   as = acks stream (in sender)
   ar = acks stream (from receiver)
   ds = output stream (from sender)
   p2 = oracle stream
*}

lemma tsmed_tsabs_slen_inf [simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(tsAbs\<cdot>msg)=\<infinity>" 
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
sorry

lemma tsaltbitpro_inp2out_sndmed:
  assumes send_def: "send \<in> tsSender"
    and ora_def: "#({True} \<ominus> p2) = \<infinity>"
    and out_def: "ds = send\<cdot>i\<cdot>as"
    and acks2med_def: "ar = tsProjSnd\<cdot>ds"
    and acks2snd_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
(*
  tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i 
  tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))
  #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))
  (#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>)

  lemma min_rek: assumes  "z = min x (lnsuc\<cdot>z)" shows "z = x"
*)
proof -
  have "#(tsAbs\<cdot>ds) = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>as) = \<infinity>"
    using acks2med_def acks2snd_def ora_def out_def by fastforce
  have "#(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = \<infinity>"
    sorry
  hence "(#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>) 
          \<Longrightarrow> #(tsAbs\<cdot>i) \<le> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
    by (metis (no_types, hide_lams) dual_order.trans inf_ub leI less_lnsuc min_def 
        out_def send_def set2tssnd_ack2trans tsprojfst_tsabs_slen tsprojsnd_tsabs_slen)
  hence "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) = #(tsAbs\<cdot>i)"
    by (metis min_def send_def set2tssnd_ack2trans set2tssnd_nack2inftrans)
  thus "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>i"
    by (simp add: eq_slen_eq_and_less out_def send_def set2tssnd_prefix_inp tsrecsnd_insert)
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