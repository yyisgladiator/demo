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

 (*TODO: adm & move some lemmas to Streams.thy*)
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
  have f1:"u=updis (shd s) \<Longrightarrow> s\<noteq>\<epsilon>\<Longrightarrow> srcdups\<cdot>(u && s) = srcdups\<cdot>s"
    apply(simp add: lscons_conv)
    using srcdups_eq[of "shd s" "srt\<cdot>s"] surj_scons[of s] by auto
  have f2:"u=updis (shd s) \<Longrightarrow> s\<noteq>\<epsilon> \<Longrightarrow> srcdups\<cdot>(srcdups\<cdot>(u && s)) = srcdups\<cdot>(u && s)"
    using f1 a2 by auto
  have "(u && s) = \<up>(THE a. updis a = u) \<bullet> s"
    by (metis a1 lscons_conv shd1 shd_updis updis_exists)
  moreover have"u\<noteq> updis (shd s) \<Longrightarrow> srcdups\<cdot>(u && s) = \<up>(THE a. updis a = u)\<bullet>srcdups\<cdot>s"
    by (metis (no_types, lifting) calculation lshd_updis srcdups_neq 
        stream.sel_rews(4) strict_srcdups surj_scons tsabs_bot tsremdups_h_strict tsremdups_h_tsabs)  
  ultimately have f3:"u\<noteq> updis (shd s) \<Longrightarrow>srcdups\<cdot>(srcdups\<cdot>(u && s)) = srcdups\<cdot>(u && s)"
    using surj_scons[of s] srcdups_ex[of "(THE a. updis a = u)" "srcdups\<cdot>s"] apply simp_all
  proof -
    assume a3: "u && s = \<up>(THE a. updis a = u) \<bullet> s"
    assume a4: "u \<noteq> updis (shd s)"
    assume a5: "s \<noteq> \<epsilon> \<Longrightarrow> \<up>(shd s) \<bullet> srt\<cdot>s = s"
    assume a6: "srcdups\<cdot>(\<up>(THE a. updis a = u) \<bullet> s) = \<up>(THE a. updis a = u) \<bullet> srcdups\<cdot>s"
    have f4: "updis (THE a. updis a = u) && s = u && s"
      using a3 lscons_conv by auto
    obtain ss :: "'a stream \<Rightarrow> 'a \<Rightarrow> 'a stream" where
      f5: "\<forall>a s. srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> ss s a"
      by (meson srcdups_ex)
    have "(THE a. updis a = u) \<noteq> shd s"
      using f4 a4 by auto
    moreover
    { assume "(srcdups\<cdot> (\<up>(THE a. updis a = u) \<bullet> \<up>(shd s) \<bullet> ss (srt\<cdot>s) (shd s)) = \<up>(THE a. updis a = u) \<bullet> srcdups\<cdot> (\<up>(shd s) \<bullet> ss (srt\<cdot>s) (shd s))) \<noteq> (srcdups\<cdot>(\<up>(THE a. updis a = u) \<bullet> srcdups\<cdot>s) = \<up>(THE a. updis a = u) \<bullet> srcdups\<cdot>s)"
      then have "\<up>(shd s) \<bullet> ss (srt\<cdot>s) (shd s) \<noteq> srcdups\<cdot>s"
        using a2 by force
      then have "srcdups\<cdot>(\<up>(THE a. updis a = u) \<bullet> srcdups\<cdot>s) = \<up>(THE a. updis a = u) \<bullet> srcdups\<cdot>s"
        using f5 a5 a6 by (metis (no_types) strict_srcdups) }
    ultimately show "srcdups\<cdot>(\<up>(THE a. updis a = u) \<bullet> srcdups\<cdot>s) = \<up>(THE a. updis a = u) \<bullet> srcdups\<cdot>s"
      by (meson srcdups_neq)
  qed
  show "srcdups\<cdot>(srcdups\<cdot>(u && s)) = srcdups\<cdot>(u && s)"
  apply(cases "s=\<epsilon>", simp)
  apply (metis f3 tsabs_bot tsremdups_h_strict tsremdups_h_tsabs)
  using f2 f3 by auto     
qed
  
lemma srcdups_imposs_adm_h[simp]:"adm (\<lambda>b. srcdups\<cdot>(\<up>a \<bullet> b) \<noteq> \<up>a \<bullet> \<up>a)"
  by (metis (mono_tags, lifting) lscons_conv sconc_snd_empty srcdups2srcdups srcdups_eq 
stream.con_rews(2) stream.injects triv_admI tsabs_bot tsremdups_h_strict tsremdups_h_tsabs up_defined)

lemma srcdups_imposs_adm[simp]:"adm (\<lambda>b. srcdups\<cdot>(\<up>a \<bullet> b) \<noteq> \<up>a \<bullet> \<up>a \<bullet> y)"
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun)
  sorry
   
lemma srcdups_imposs:"srcdups\<cdot>(\<up>a \<bullet> s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> y"
  apply(induction s,simp+)
proof -
  fix u :: "'a discr\<^sub>\<bottom>" and s :: "'a stream" and a ::'a and y :: "'a stream"
  assume a1:"u\<noteq>\<bottom>"
  assume a2:"srcdups\<cdot>(\<up>a \<bullet> s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> y"
  have f1:"u=updis a \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> u && s)\<noteq> \<up>a \<bullet> \<up>a \<bullet> y"
    by (simp add: lscons_conv a2)
  have f2:"u\<noteq>updis a \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> u && s)\<noteq> \<up>a \<bullet> \<up>a \<bullet> y"
    proof -
      assume a3: "u \<noteq> updis a"
      have f2: "\<up>(shd (u && s)) \<bullet> srt\<cdot>(u && s) = u && s"
        by (meson a1 stream.con_rews(2) surj_scons)
      then have "u = lshd\<cdot>(\<up>(THE a. updis a = u) \<bullet> srt\<cdot>(u && s))"
        by (simp add: shd_updis)
      then have f3: "a \<noteq> (THE a. updis a = u)"
        using a3 by auto
      obtain ss :: "'a stream \<Rightarrow> 'a \<Rightarrow> 'a stream" where
        f4: "\<forall>a s. srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> ss s a"
        by (meson srcdups_ex)
      then have f5: "\<up>a \<bullet> ss (u && s) a = srcdups\<cdot> (\<up>a \<bullet> \<up>(THE a. updis a = u) \<bullet> srt\<cdot>(u && s))"
        using f2 by (simp add: shd_updis)
      have "\<forall>a aa s. (a::'a) = aa \<or> srcdups\<cdot>(\<up>a \<bullet> \<up>aa \<bullet> s) = \<up>a \<bullet> srcdups\<cdot>(\<up>aa \<bullet> s)"
        by (meson srcdups_neq)
      then have "\<up>a \<bullet> ss (u && s) a = \<up>a \<bullet> \<up>(THE a. updis a = u) \<bullet> ss (srt\<cdot>(u && s)) (THE a. updis a = u)"
        using f5 f4 f3 by auto
      then have "\<up>a \<bullet> \<up>a \<bullet> y \<noteq> \<up>a \<bullet> ss (u && s) a"
        using f3 by (metis inject_scons)
      then show ?thesis
        using f4 by presburger
    qed
  show "srcdups\<cdot>(\<up>a \<bullet> u && s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> y"
    using f1 f2 by auto
qed
  
lemma srcdupsimposs: "srcdups\<cdot>(\<up>a \<bullet> s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> srcdups\<cdot>s"
  by (simp add: srcdups_imposs)
    
lemma srcdupsimposs2_h2:"\<forall>x. srcdups\<cdot>(\<up>a \<bullet> s)\<noteq> \<up>a \<bullet> \<up>a \<bullet> x"
  by (simp add: srcdups_imposs)
  
lemma srcdupsimposs2: "srcdups\<cdot>(\<up>a \<bullet> s) \<noteq> \<up>a \<bullet> \<up>a \<bullet> s"
  by(simp add: srcdups_imposs) 
    
lemma srcdups_anotb_h:"srcdups\<cdot>(\<up>a\<bullet>\<up>b) = \<up>a \<bullet> \<up>b \<Longrightarrow> a \<noteq> b"
  by (metis lscons_conv srcdups_eq2 stream.con_rews(2) stream.sel_rews(5) sup'_def tsabs_bot 
      tsremdups_h_strict tsremdups_h_tsabs up_defined)
  
lemma srcdups_anotb:"srcdups\<cdot>(\<up>a \<bullet> \<up>b \<bullet> s) = \<up>a \<bullet> \<up>b \<bullet> s \<Longrightarrow> a\<noteq> b"
  using srcdupsimposs2_h2 by auto
    
lemma srcdups_smap_adm [simp]: 
  "adm (\<lambda>a. srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>a)) = smap f\<cdot>(srcdups\<cdot>a) 
    \<longrightarrow> srcdups\<cdot>(smap f\<cdot>a) = smap f\<cdot>(srcdups\<cdot>a))"
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun)
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
    proof -
      assume a1: "f (shd s) \<noteq> f a"
      assume a2: "s \<noteq> \<epsilon>"
      assume a3: "shd s \<noteq> a"
      have f4: "s = \<up>(shd s) \<bullet> srt\<cdot>s"
        using a2 by (metis h1)
      obtain ss :: "'b stream \<Rightarrow> 'b \<Rightarrow> 'b stream" where
        f5: "\<forall>b s. srcdups\<cdot>(\<up>b \<bullet> s) = \<up>b \<bullet> ss s b"
        by (meson srcdups_ex)
      then have f6: "\<up>(shd s) \<bullet> ss (srt\<cdot>s) (shd s) = srcdups\<cdot>s"
        using f4 by metis
      have f7: "srcdups\<cdot> (\<up>(f a) \<bullet> \<up>(f (shd s)) \<bullet> smap f\<cdot> (ss (srt\<cdot>s) (shd s))) = \<up>(f a) \<bullet> srcdups\<cdot> (\<up>(f (shd s)) \<bullet> smap f\<cdot> (ss (srt\<cdot>s) (shd s)))"
        using a1 by auto
      have f8: "\<up>a \<bullet> \<up>(shd s) \<bullet> ss (srt\<cdot>s) (shd s) = srcdups\<cdot>(\<up>a \<bullet> \<up>(shd s) \<bullet> srt\<cdot>s)"
        using f5 a3 by (metis (no_types) srcdups_neq)
      then have f9: "\<up>(f a) \<bullet> \<up>(f (shd s)) \<bullet> smap f\<cdot> (ss (srt\<cdot>s) (shd s)) = smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s))"
        using f4 by (metis (no_types) smap_scons)
      then obtain ssa :: "'a stream \<Rightarrow> 'a \<Rightarrow> 'a stream" where
        f10: "\<up>(f a) \<bullet> ssa (\<up>(f (shd s)) \<bullet> ssa (smap f\<cdot>(ss (srt\<cdot>s) (shd s))) (f (shd s))) (f a) = srcdups\<cdot>(smap f\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s)))"
        by (simp add: "3.prems")
      then have f11: "\<up>(f a) \<bullet> ssa (\<up>(f (shd s)) \<bullet> ssa (smap f\<cdot>(ss (srt\<cdot>s) (shd s))) (f (shd s))) (f a) = srcdups\<cdot> (\<up>(f a) \<bullet> \<up>(f (shd s)) \<bullet> smap f\<cdot> (ss (srt\<cdot>s) (shd s)))"
        using f9 by presburger
      have "\<up>(f a) \<bullet> ssa (\<up>(f (shd s)) \<bullet> ssa (smap f\<cdot>(ss (srt\<cdot>s) (shd s))) (f (shd s))) (f a) = \<up>(f a) \<bullet> smap f\<cdot>(srcdups\<cdot>s)"
        using f10 f8 f6 f4 by (metis (no_types) "3.prems" smap_scons)
      then have "srcdups\<cdot>(smap f\<cdot>s) = smap f\<cdot>(srcdups\<cdot>s)"
        using f11 f7 f6 by (metis (no_types) "3.IH" inject_scons smap_scons)
      then have "srcdups\<cdot> (smap f\<cdot>(\<up>a \<bullet> \<up>(shd s) \<bullet> srt\<cdot>s)) = smap f\<cdot> (\<up>a \<bullet> \<up>(shd s) \<bullet> ss (srt\<cdot>s) (shd s))"
        using f6 f4 a1 by (metis (no_types) smap_scons srcdups_neq)
      then show ?thesis
        using f8 by presburger
    qed
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