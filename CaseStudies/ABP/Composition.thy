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

 (*TODO: adm & not use smt & change lemmanames & move some lemmas to Streams.thy*)
lemma srcdups_eq2:"a=b \<Longrightarrow> srcdups\<cdot>(\<up>a\<bullet>\<up>b\<bullet>s) = srcdups\<cdot>(\<up>b\<bullet>s)"
  by simp
    
lemma srcdups_ex:"\<exists>y. srcdups\<cdot>(\<up>a\<bullet>s) = \<up>a\<bullet>y"
  by(subst srcdups_def [THEN fix_eq2], auto)
    
lemma [simp]:"shd (srcdups\<cdot>(\<up>a\<bullet>s)) = a"
  by(subst srcdups_def [THEN fix_eq2], auto)

lemma srcdups2srcdups: "srcdups\<cdot>(srcdups\<cdot>s) = srcdups\<cdot>s"
  apply(induction s,auto)
proof -
  fix u :: "'a discr\<^sub>\<bottom>" and s :: "'a stream" 
  assume a1:"u\<noteq>\<bottom>"
  assume a2:"srcdups\<cdot>(srcdups\<cdot>s) = srcdups\<cdot>s"
  have f0:"u=updis (shd s) \<Longrightarrow> s\<noteq>\<epsilon>\<Longrightarrow> srcdups\<cdot>(u && s) = srcdups\<cdot>s"
    apply(simp add: lscons_conv)
    using srcdups_eq[of "shd s" "srt\<cdot>s"] surj_scons[of s] by auto
  have f1:"u=updis (shd s) \<Longrightarrow> s\<noteq>\<epsilon> \<Longrightarrow> srcdups\<cdot>(srcdups\<cdot>(u && s)) = srcdups\<cdot>(u && s)"
    using f0 a2 by auto
  have "(u && s) = \<up>(THE a. updis a = u) \<bullet> s"
    by (metis a1 lscons_conv shd1 shd_updis updis_exists)
  moreover have f2_h:"u\<noteq> updis (shd s) \<Longrightarrow> srcdups\<cdot>(u && s) = \<up>(THE a. updis a = u)\<bullet>srcdups\<cdot>s"
    by (metis (no_types, lifting) calculation lshd_updis srcdups_neq 
        stream.sel_rews(4) strict_srcdups surj_scons tsabs_bot tsremdups_h_strict tsremdups_h_tsabs)  
  ultimately have f2:"u\<noteq> updis (shd s) \<Longrightarrow>srcdups\<cdot>(srcdups\<cdot>(u && s)) = srcdups\<cdot>(u && s)"
    using surj_scons[of s] apply auto
    using srcdups_ex[of "(THE a. updis a = u)" "srcdups\<cdot>s"] apply auto
    by (smt a2 lscons_conv srcdups_ex srcdups_neq stream.injects strict_srcdups)
  show "srcdups\<cdot>(srcdups\<cdot>(u && s)) = srcdups\<cdot>(u && s)"
  apply(cases "s=\<epsilon>", simp)
  apply (metis f2 tsabs_bot tsremdups_h_strict tsremdups_h_tsabs)
  using f1 f2 by auto     
qed
  
lemma srcdupsadm1[simp]:"adm (\<lambda>a. srcdups\<cdot>(\<up>x \<bullet> a) \<noteq> \<up>x \<bullet> \<up>x \<bullet> srcdups\<cdot>a)"
  using admI inf_chainl4 l42 contlub_cfun_arg
  sorry
    
lemma srcdupsimposs: "srcdups\<cdot>(\<up>a \<bullet> s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> srcdups\<cdot>s"
apply(cases "s=\<epsilon>", simp)
apply(induction s arbitrary: a,auto)
proof -
  fix u :: "'a discr\<^sub>\<bottom>" and s :: "'a stream" and a:: 'a   
  assume a1:"u\<noteq>\<bottom>"
  assume a2: "(\<And>a. s \<noteq> \<epsilon> \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> srcdups\<cdot>s)"
  have f1: "u= updis a \<Longrightarrow>  u && s = \<up>a \<bullet> s"
    by(simp add: lscons_conv)
  have f2: "u= updis a \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> u && \<epsilon>) = \<up>a"
    using f1 srcdups_eq2
    by (metis sconc_snd_empty sup'_def tsabs_bot tsremdups_h_strict tsremdups_h_tsabs)
  have f3: "u \<noteq> updis a \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> u && \<epsilon>) = \<up>a \<bullet> u && \<epsilon>"
    using srcdups_neq a1
    by (smt lscons_conv stream.injects stream.sel_rews(4) surj_scons tsabs_bot tsremdups_h_strict tsremdups_h_tsabs)
  have f4:"u \<noteq> updis a \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> u && s) = \<up>a \<bullet> srcdups\<cdot>(u && s)"
    using srcdups_neq a1
    by (metis lscons_conv updis_exists)
  have f5:"u \<noteq> updis a \<Longrightarrow> updis (shd s)\<noteq> u \<Longrightarrow> s\<noteq>\<epsilon> \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> u && s) = \<up>a\<bullet> u && (srcdups\<cdot>s)"
    using srcdups_neq
    by (smt a1 lscons_conv stream.injects surj_scons up_defined)
  have f6:"u \<noteq> updis a \<Longrightarrow> updis (shd s)= u \<Longrightarrow> s\<noteq>\<epsilon> \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> u && s) = \<up>a \<bullet> (srcdups\<cdot>s)"
    by (metis f4 lscons_conv srcdups_eq2 surj_scons)
  show "srcdups\<cdot>(\<up>a \<bullet> u && s) = \<up>a \<bullet> \<up>a \<bullet> srcdups\<cdot>(u && s) \<Longrightarrow> False"
    apply(insert srcdups_ex[of "shd s" "srt\<cdot>s"],auto)
    by (smt a1 a2 f2 f3 f5 inject_scons lscons_conv srcdups_eq2 srcdups_neq stream.con_rews(2) stream.sel_rews(4) sup'_def surj_scons)
qed

lemma srcdupsimposs2_h:"\<forall>x. srcdups\<cdot>(\<up>a \<bullet> s)\<noteq> \<up>a \<bullet> \<up>a \<bullet> srcdups\<cdot>x"
  by (metis srcdups2srcdups srcdups_eq2 srcdupsimposs)

lemma srcdupsadm2[simp]:"adm (\<lambda>b. srcdups\<cdot>(\<up>a \<bullet> b) \<noteq> \<up>a \<bullet> \<up>a \<bullet> x)"
  apply(rule admI)
  apply (auto simp add: contlub_cfun_arg)
  using admI inf_chainl4 l42
  sorry

lemma srcdupsimposs2_h2:"\<forall>x. srcdups\<cdot>(\<up>a \<bullet> s)\<noteq> \<up>a \<bullet> \<up>a \<bullet> x"
  apply(induction s arbitrary: a, auto)
proof-   
  fix u :: "'a discr\<^sub>\<bottom>" and s :: "'a stream" and a:: 'a and x:: "'a stream"  
  assume a1:"u\<noteq>\<bottom>"
  assume a2: "(\<And>a. \<forall>x. srcdups\<cdot>(\<up>a \<bullet> s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> x)"
  have f1:"u= updis a \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> u && s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> x"
    by (simp add: a2 lscons_conv)
  have f2: "u\<noteq> updis a \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> u && s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> x"
(*  proof -
    assume a1: "u \<noteq> updis a"
    have f2: "\<up>(shd (u && s)) \<bullet> srt\<cdot>(u && s) = u && s"
      sorry
    then have f3: "\<up>(THE a. updis a = u) \<bullet> srt\<cdot>(u && s) = u && s"
      by (simp add: shd_updis)
    have f4: "u && s = updis (THE a. updis a = u) && srt\<cdot>(u && s)"
      using f2 by (simp add: lscons_conv shd_updis)
    have "\<forall>u s ua sa. u = \<bottom> \<or> (u && (s::'a stream) = ua && sa) = (u = ua \<and> s = sa)"
      using stream.injects by blast
    then have "a \<noteq> (THE a. updis a = u)"
      using f4 a1 sorry
    then have f5: "srcdups\<cdot> (\<up>a \<bullet> \<up>(THE a. updis a = u) \<bullet> srt\<cdot>(u && s)) = \<up>a \<bullet> srcdups\<cdot> (\<up>(THE a. updis a = u) \<bullet> srt\<cdot>(u && s))"
      by (meson srcdups_neq)
    have f6: "updis a = \<bottom> \<or> (updis a && srcdups\<cdot>(u && s) = updis a && \<up>a \<bullet> x) = (srcdups\<cdot>(u && s) = \<up>a \<bullet> x)"
      by simp
    have "(srcdups\<cdot>(\<up>a \<bullet> u && s) = \<up>a \<bullet> \<up>a \<bullet> x) = (srcdups\<cdot>(\<up>a \<bullet> u && s) = \<up>a \<bullet> \<up>a \<bullet> x)"
      by simp
    moreover
    { assume "updis a = \<bottom>"
      moreover
      { assume "srcdups\<cdot>(\<up>a \<bullet> x) \<noteq> \<up>a \<bullet> srcdups\<cdot>(u && s)"
        then have "srcdups\<cdot>(\<up>a \<bullet> x) \<noteq> srcdups\<cdot>(\<up>a \<bullet> u && s)"
        using f5 f3 by force }
    ultimately have "\<up>a \<bullet> \<up>a \<bullet> x \<noteq> srcdups\<cdot>(\<up>a \<bullet> x) \<or> srcdups\<cdot>(\<up>a \<bullet> x) \<noteq> srcdups\<cdot>(\<up>a \<bullet> u && s) \<or> srcdups\<cdot>(\<up>a \<bullet> u && s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> x"
      by simp }
  ultimately have "\<up>a \<bullet> \<up>a \<bullet> x \<noteq> srcdups\<cdot>(\<up>a \<bullet> x) \<or> srcdups\<cdot>(\<up>a \<bullet> x) \<noteq> srcdups\<cdot>(\<up>a \<bullet> u && s) \<or> \<up>a \<bullet> \<up>a \<bullet> x \<noteq> srcdups\<cdot>(\<up>a \<bullet> u && s) \<or> srcdups\<cdot>(\<up>a \<bullet> u && s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> x"
    using f6 f5 f3 by (metis (no_types) lscons_conv srcdups2srcdups srcdupsimposs)
  then show ?thesis
    by (metis (no_types) srcdups2srcdups srcdups_eq)
qed*)
    by (smt a1 discr.simps(1) lscons_conv shd_updis srcdups2srcdups srcdups_eq srcdups_neq srcdupsimposs stream.con_rews(2) stream.injects surj_scons up_eq)
  show "srcdups\<cdot>(\<up>a \<bullet> u && s) = \<up>a \<bullet> \<up>a \<bullet> x \<Longrightarrow> False"
    using f1 f2 by auto
qed
  
lemma srcdupsimposs2: "srcdups\<cdot>(\<up>a \<bullet> s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> s"
  by(simp add: srcdupsimposs2_h2) 

    
lemma srcdups_anotb_h:"srcdups\<cdot>(\<up>a\<bullet>\<up>b) = \<up>a \<bullet> \<up>b \<Longrightarrow> a \<noteq> b"
  by (metis lscons_conv srcdups_eq2 stream.con_rews(2) stream.sel_rews(5) sup'_def tsabs_bot 
      tsremdups_h_strict tsremdups_h_tsabs up_defined)
  
lemma srcdups_anotb:"srcdups\<cdot>(\<up>a \<bullet> \<up>b \<bullet> s) = \<up>a \<bullet> \<up>b \<bullet> s \<Longrightarrow> a\<noteq> b"
  using srcdupsimposs2_h2 by auto
    
lemma srcdups_smap_adm [simp]: 
  "adm (\<lambda>a. srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>a)) = smap f\<cdot>(srcdups\<cdot>a) 
    \<longrightarrow> srcdups\<cdot>(smap f\<cdot>a) = smap f\<cdot>(srcdups\<cdot>a))"
  apply(rule admI)
  apply (auto simp add: contlub_cfun_arg)
  sorry
 
lemma srcdups_smap_com_h:"s\<noteq>\<epsilon> \<Longrightarrow> a \<noteq> shd s \<Longrightarrow> srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s))) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s)) \<Longrightarrow>f (shd s) \<noteq> f a"
  apply(cases "shd(srt\<cdot>s) \<noteq> shd s")
  apply (insert srcdups_neq[of a "shd s" "srt\<cdot>s"] surj_scons[of s], simp)
  apply (metis smap_scons srcdups_ex srcdupsimposs2_h2)
  apply (insert srcdups_neq[of a "shd s" "srt\<cdot>s"] surj_scons[of s], simp)
  apply(insert srcdups_ex[of "shd s" "srt\<cdot>s"],auto)
  by (simp add: srcdupsimposs2_h2)

    declare [[show_types]]
(* Move to Streams.thy after done *)
lemma srcdups_smap_com:
  shows "srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>s)) = smap f\<cdot>(srcdups\<cdot>s) \<Longrightarrow> srcdups\<cdot>(smap f\<cdot>s)= smap f\<cdot>(srcdups\<cdot>s)"
  proof(induction rule: ind [of _ s])
    case 1
    then show ?case 
      by simp
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
      apply simp using "3.IH"
      by (smt "3.prems" h1 inject_scons smap_hd_rst smap_scons srcdups_anotb srcdups_neq strict_smap strict_srcdups) 
    have f2: "s\<noteq>\<bottom> \<Longrightarrow> shd s\<noteq>a \<Longrightarrow>f (shd s) \<noteq> f a \<Longrightarrow> ?case"
      using h1 h2 by auto
    have f3: "s\<noteq>\<bottom> \<Longrightarrow> shd s\<noteq>a \<Longrightarrow>f (shd s) = f a \<Longrightarrow> ?case"
      by (simp add: "3.prems" srcdups_smap_com_h)
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