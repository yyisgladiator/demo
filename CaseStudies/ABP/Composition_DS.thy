(*  Title:        Composition.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory Composition_DS
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
  (#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>) \<and>
  (min (#\<surd>i) (#\<surd>as) < \<infinity> \<longrightarrow> min (#\<surd>i) (#\<surd>as) <  #\<surd>(send\<cdot>i\<cdot>as))
}"

(* 1st axiom *)
lemma set2tssnd_prefix_inp: assumes "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i"
  using assms tsSender_def by auto

lemma set2tssnd_alt_bit: assumes "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))"
  using assms tsSender_def by auto

(* 5th axiom *)  
lemma set2tssnd_ack2trans: assumes "send \<in> tsSender"
  shows "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) 
    = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
  using assms tsSender_def by auto

(* 4th axiom *)
lemma set2tssnd_nack2inftrans: assumes "send \<in> tsSender"
  shows "(#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(send\<cdot>i\<cdot>as)) = \<infinity>)"
  using assms tsSender_def by auto

(* ----------------------------------------------------------------------- *)
subsection {* additional lemmata *}
(* ----------------------------------------------------------------------- *)

(* prop0 helper begin*)
lemma prop0_h:"#(srcdups\<cdot>(s\<bullet>s2)) \<le> #(srcdups\<cdot>(s\<bullet>\<up>b\<bullet>s2))"
proof(induction rule: ind [of _ s])
  case 1
  then show ?case
  apply(rule admI)
  by (metis inf_chainl4 l42 order_refl sconc_fst_inf)
next
  case 2
  then show ?case 
  proof -
    { assume "\<not> #(srcdups\<cdot>(\<epsilon> \<bullet> s2)) \<le> #(srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2))"
      { assume "srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2) \<noteq> \<up>b \<bullet> srcdups\<cdot>(\<up>(shd s2) \<bullet> srt\<cdot>s2)"
        { assume "srcdups\<cdot> (\<up>b \<bullet> \<up>(shd s2) \<bullet> srt\<cdot>s2) \<noteq> \<up>b \<bullet> srcdups\<cdot>(\<up>(shd s2) \<bullet> srt\<cdot>s2)"
          moreover
          { assume "srcdups\<cdot>(\<up>b \<bullet> \<up>(shd s2) \<bullet> srt\<cdot>s2) = srcdups\<cdot>(\<up>(shd s2) \<bullet> srt\<cdot>s2) \<and> srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2) \<noteq> srcdups\<cdot>(\<epsilon> \<bullet> s2)"
            then have "\<up>(shd s2) \<bullet> srt\<cdot>s2 \<noteq> s2"
              by force }
          ultimately have "\<up>(shd s2) \<bullet> srt\<cdot>s2 = s2 \<longrightarrow> #(srcdups\<cdot>(\<epsilon> \<bullet> s2)) \<le> #(srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2))"
            by (metis (no_types) eq_iff srcdups_eq2 srcdups_neq) }
        then have "\<up>(shd s2) \<bullet> srt\<cdot>s2 = s2 \<longrightarrow> #(srcdups\<cdot>(\<epsilon> \<bullet> s2)) \<le> #(srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2))"
          by force }
      moreover
      { assume "\<up>(shd s2) \<bullet> srt\<cdot>s2 \<noteq> s2"
        then have "s2 = \<epsilon>"
          by (metis surj_scons)
        then have ?thesis
          by force }
      ultimately have ?thesis
        by fastforce }
    then show ?thesis
      by metis
  qed
next
  case (3 a s)
  then have case_epseq:"a=b \<Longrightarrow> #(srcdups\<cdot>(\<up>a \<bullet> s2)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> \<up>b \<bullet> s2))"
   by simp
  have case_epsneq:"a\<noteq>b \<Longrightarrow> #(srcdups\<cdot>(\<up>a \<bullet> s2)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> \<up>b \<bullet> s2))"
    apply(subst srcdups_neq,simp)
    apply(cases "s2=\<epsilon>",simp)
    apply(cases "b=shd s2")
    apply (metis eq_refl srcdups_eq srcdups_neq surj_scons)
    using surj_scons[of s2] srcdups_neq[of b "shd s2" "srt\<cdot>s2"] apply auto
  proof -
    assume a1: "\<up>(shd s2) \<bullet> srt\<cdot>s2 = s2"
    have "#(srcdups\<cdot>s2) \<le> lnsuc\<cdot>(lnsuc\<cdot>(#(srcdups\<cdot>s2)))"
      by (meson dual_order.trans less_lnsuc)
    then show "#(srcdups\<cdot>(\<up>a \<bullet> s2)) \<le> lnsuc\<cdot>(lnsuc\<cdot>(#(srcdups\<cdot>s2)))"
      using a1 by (metis (no_types) less_lnsuc slen_scons srcdups_eq2 srcdups_neq)
  qed
  have case_eq: "s\<noteq>\<epsilon> \<Longrightarrow> a = shd s \<Longrightarrow> ?case"
    by (metis "3.IH" sconc_scons srcdups_eq surj_scons)
  have "s\<noteq>\<epsilon> \<Longrightarrow> a\<noteq>shd s \<Longrightarrow> ?case"
  proof -
    assume a1: "s \<noteq> \<epsilon>"
    assume a2: "a \<noteq> shd s"
    have "\<up>(shd s) \<bullet> srt\<cdot>s = s"
      using a1 by (meson surj_scons)
    then show ?thesis
      using a2 by (metis (no_types) "3.IH" lnsuc_lnle_emb sconc_scons slen_scons srcdups_neq)
  qed
  then show ?case
    using case_epseq case_epsneq case_eq by fastforce
qed
   
lemma prop0_h2: assumes "#p=\<infinity>"
    shows"#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>b\<bullet>p)))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<bullet>p))))"
  apply(cases "b", simp)
proof(induction ts)
  case adm
  then show ?case
    apply(rule adm_imp,simp)
    apply(rule admI)
    by(simp add: contlub_cfun_arg assms contlub_cfun_fun lub_mono2)
next
  case bottom
  then show ?case
    by simp
next
  case (delayfun ts)
  then show ?case
    by (simp add: tsmed_delayfun)
next
  case (mlscons ts t)
  have f1:"tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>(\<up>b \<bullet> p) = tsMed\<cdot>ts\<cdot>p"
    using tsmed_mlscons_false[of ts "p" t]  by (simp add: assms lscons_conv mlscons.hyps mlscons.prems)
  then show ?case 
    apply (simp add: f1)
    by (metis assms bot_is_0 lnle_def lscons_conv minimal mlscons.hyps prop0_h sconc_fst_empty 
        slen_empty_eq strict_srcdups tsabs_bot tsabs_mlscons tsmed_mlscons_true)
qed

lemma prop0_h2_2: assumes "#p=\<infinity>"
    shows"#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>p))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<bullet>(srt\<cdot>p)))))"
  using prop0_h2[of "srt\<cdot>p" ts "shd p"]
  by (metis Inf'_neq_0 assms fold_inf inject_lnsuc slen_empty_eq srt_decrements_length surj_scons)

  
lemma prop0_h3_h:"tsMed\<cdot>ts\<cdot>p\<noteq>\<bottom> \<Longrightarrow> tsAbs\<cdot>(updis t &&\<surd> tsMed\<cdot>ts\<cdot>p) = \<up>t \<bullet> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>p))"
  by (simp add: lscons_conv tsabs_mlscons)

lemma tsmed_shd_adm_h2:"chain Y \<Longrightarrow> Y i\<noteq>\<epsilon> \<Longrightarrow> shd (Y i) = shd (\<Squnion>i. Y i)"
  by (simp add: below_shd is_ub_thelub)
    
lemma tsmed_shd:"#ora1=\<infinity> \<Longrightarrow> #ora2=\<infinity> \<Longrightarrow> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(updis True && ora1))) = shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(updis True && ora2)))"
proof(induction ts)
  case adm
  then show ?case
    apply (rule adm_imp,auto)+
    apply (rule admI) 
    apply(simp add: contlub_cfun_arg contlub_cfun_fun)
    proof-
      fix Y::"nat \<Rightarrow>'a tstream"
      assume a1: "chain Y"
      assume a2: "\<forall>i. shd (tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora1))) = shd (tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora2)))"
      have c1:"chain (\<lambda>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora1)))"
        by (simp add: a1)
      have c2:"chain (\<lambda>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora2)))"
        by (simp add: a1)
      show "shd (\<Squnion>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora1))) = shd (\<Squnion>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora2)))"
        by (metis (no_types, lifting) a2 c1 c2 lub_eq_bottom_iff tsmed_shd_adm_h2)
    qed
next
  case bottom
  then show ?case 
    by simp
next
  case (delayfun ts)
  then show ?case
    by (metis stream.con_rews(2) tsabs_delayfun tsmed_delayfun)
next
  case (mlscons ts t)
  then show ?case
    by (metis prop0_h3_h shd1 tsmed_mlscons_true tsmed_nbot)
qed

lemma tsmed_srcdups_shd:"#ora1=\<infinity> \<Longrightarrow> #ora2=\<infinity> \<Longrightarrow> shd (srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(updis True && ora1)))) = shd (srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(updis True && ora2))))"
  by (metis srcdups_shd2 strict_srcdups tsmed_shd)  
    
(*maybe nice to have
    
lemma prop0_ind_h2:
  shows"#p2=\<infinity> \<Longrightarrow> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(p1 \<bullet> p2)))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>((p1 \<bullet> \<up>True \<bullet> srt\<cdot>p2)))))"
*)

lemma prop0_h2_ind_h: assumes "#p=\<infinity>"
    shows"#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>b \<bullet> p)))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<bullet>p))))"
  apply(cases "b", simp)
proof(induction ts)
  case adm
  then show ?case
    apply(rule adm_imp,simp)
    apply(rule admI)
    by(simp add: contlub_cfun_arg assms contlub_cfun_fun lub_mono2)
next
  case bottom
  then show ?case
    by simp
next
  case (delayfun ts)
  then show ?case
    by (simp add: tsmed_delayfun)
next
  case (mlscons ts t)
  have f1:"tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>(\<up>b \<bullet> p) = tsMed\<cdot>ts\<cdot>p"
    using tsmed_mlscons_false[of ts "p" t]  by (simp add: assms lscons_conv mlscons.hyps mlscons.prems)
  then show ?case 
    apply (simp add: f1)
    by (metis assms lscons_conv mlscons.hyps prop0_h prop0_h3_h tsmed_mlscons_true tsmed_nbot)
qed    
    
    
lemma prop0_h3: "#p=\<infinity> \<Longrightarrow> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>p))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<infinity>))))"
proof(induction ts arbitrary: p)
  case adm
  then show ?case
    apply simp
    apply (rule adm_all)
    apply (rule adm_imp, auto)
    apply (rule admI)
    by (simp add: contlub_cfun_fun contlub_cfun_arg lub_mono2)
next
  case bottom
  then show ?case
    by simp
next
  case (delayfun ts)
  then show ?case
    by (metis (no_types, lifting) tsabs_delayfun tsmed_delayfun tsmed_strict(2))
next
  case (mlscons ts t)
  
  have h1:"tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>(\<up>True\<bullet>(srt\<cdot>p)) = updis t &&\<surd> tsMed\<cdot>ts\<cdot>(srt\<cdot>p)"
    by (metis (no_types, lifting) Inf'_neq_0 fold_inf inject_lnsuc lscons_conv mlscons.hyps mlscons.prems slen_empty_eq srt_decrements_length tsmed_mlscons_true)
  have h2:"tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>\<up>True\<infinity> = updis t &&\<surd> tsMed\<cdot>ts\<cdot>\<up>True\<infinity>"
    by (metis tsmed_inftrue)
  have h5:"tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)) \<noteq> \<epsilon> \<Longrightarrow> t\<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<infinity>))) \<Longrightarrow> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))) =lnsuc\<cdot>(#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))))"
  proof -
    assume a1: "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)) \<noteq> \<epsilon>"
    assume a2: "t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))"
    have "p \<noteq> \<epsilon>"
      using mlscons.prems by force
    then have "lnsuc\<cdot>(#(srt\<cdot>p)) = \<infinity>"
      by (metis (no_types) mlscons.prems slen_scons surj_scons)
    then have "tsAbs\<cdot>ts \<noteq> \<epsilon>"
      using a1 by (metis bot_is_0 fold_inf inject_lnsuc leD lnless_def minimal slen_empty_eq tsmed_tsabs_slen)
    then show ?thesis
      using a2 by (metis (no_types) slen_scons srcdups_neq surj_scons tsmed_inftrue)
  qed
  have "#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>(\<up>True\<bullet>(srt\<cdot>p)))))\<le>#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>\<up>True\<infinity>)))"
    apply(simp only: h1 h2)
    apply(subst prop0_h3_h)
    apply (metis Inf'_neq_0 fold_inf inject_lnsuc mlscons.hyps mlscons.prems only_empty_has_length_0 srt_decrements_length tsmed_nbot)
    apply(subst prop0_h3_h)
    apply (simp add: mlscons.hyps)
    proof-
      have srt_len:"#(srt\<cdot>p) = \<infinity>"
        by (metis Inf'_neq_0 fold_inf inject_lnsuc mlscons.prems slen_empty_eq srt_decrements_length)
      then have h1:"#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)))) \<le>#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p)))))"
        by (metis Inf'_neq_0 prop0_h2_ind_h fold_inf lnat.sel_rews(2) only_empty_has_length_0 srt_decrements_length surj_scons)
      have h2:"#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
        proof(cases "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))) = \<epsilon>")
          case True
          then show ?thesis
            by (metis lnle_def minimal monofun_cfun_arg)
        next
          case False
          then show ?thesis
           proof(cases "t= shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))")
          case True
          assume a1: "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))) \<noteq> \<epsilon>"
          assume a2: "t = shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))"
          have h10:"\<And>s a. #(srcdups\<cdot>s) \<le> #(srcdups\<cdot>(\<up>(a::'a) \<bullet> s))"
            by (metis (full_types) prop0_h sconc_fst_empty)
          then have "#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)))) \<le> #(srcdups\<cdot> (\<up>t \<bullet> tsAbs\<cdot> (tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
            using srt_len dual_order.trans mlscons.IH by blast
          then show "#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
            using a2 a1
          proof -
            have "\<not> #(srcdups\<cdot> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))) < #(srcdups\<cdot> (\<up>t \<bullet> tsAbs\<cdot> (tsMed\<cdot>ts\<cdot> (\<up>True \<bullet> srt\<cdot> (srt\<cdot>p)))))"
              by (metis (no_types) Inf'_neq_0 srt_len a1 a2 leD mlscons.IH only_empty_has_length_0 slen_scons srcdups_eq surj_scons)
            then show ?thesis
              by (meson h10 le_less_trans not_le_imp_less)
          qed
        next
          case False
          assume a1: "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))) \<noteq> \<epsilon>"
          assume a2: "t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))"
          have "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>) \<noteq>\<epsilon>"
            by (metis Inf'_neq_0 srt_len a1 leD lnless_def lnzero_def minimal slen_empty_eq slen_scons srt_decrements_length tsmed_inftrue tsmed_tsabs_slen)
          then have "shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p)))) = shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))"
            by (metis tsmed_shd sinftimes_unfold deconstruct_infstream_h lscons_conv mlscons.prems slen_sinftimes stream.con_rews(2) stream.sel_rews(5) sup'_def up_defined)
          then have "t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))"
            using a2 by simp
          then show "#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
          proof -
            have f1: "lnsuc\<cdot> (#(srcdups\<cdot> (tsAbs\<cdot> (tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p)))))) \<le> lnsuc\<cdot> (#(srcdups\<cdot> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))))"
              by (metis (no_types) Inf'_neq_0 srt_len lnsuc_lnle_emb mlscons.IH only_empty_has_length_0 slen_scons surj_scons)
            have f2: "\<forall>s. s = \<epsilon> \<or> \<up>(shd s::'a) \<bullet> srt\<cdot>s = s"
              by (metis surj_scons)
            have f3: "\<forall>a aa s. (a::'a) = aa \<or> srcdups\<cdot>(\<up>a \<bullet> \<up>aa \<bullet> s) = \<up>a \<bullet> srcdups\<cdot>(\<up>aa \<bullet> s)"
              by (meson srcdups_neq)
            then have "srcdups\<cdot> (\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)) = \<up>t \<bullet> srcdups\<cdot> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))"
              using f2 by (metis (no_types) \<open>t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))\<close> \<open>tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>) \<noteq> \<epsilon>\<close>)
            then show ?thesis
              using f3 f2 f1 by (metis (no_types) \<open>shd (tsAbs\<cdot> (tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p)))) = shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))\<close> \<open>t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))\<close> a1 slen_scons)
          qed
        qed    
      qed
      show "#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
        using h1 h2 order.trans by blast
    qed
    then show ?case
      using trans_lnle mlscons.prems prop0_h2_2 by blast 
  qed

 
       
(* prop0 helper end*)
    
(* property 0 *)
lemma prop0: assumes "#({True} \<ominus> p) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>ts\<cdot>p))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>ts))"
  apply (simp add: tsremdups_tsabs)
  using prop0_h3 assms sfilterl4 by fastforce
    
(* property 1 *)
lemma prop1: assumes p1_def: "#({True} \<ominus> p1) = \<infinity>" and p2_def: "#({True} \<ominus> p2) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1))\<cdot>p2))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))"
proof -
  have "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1)))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))"
    by (metis (no_types) p1_def prop0 sfilterl4 tsProjSnd_def tsmed_map)
  thus "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1))\<cdot>p2))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))"
    using p2_def prop0 trans_lnle by blast
  qed

lemma set2tssnd_alt_bit_tabs: assumes "send \<in> tsSender"
  shows "srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(send\<cdot>i\<cdot>as)))) 
    = (sprojsnd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(send\<cdot>i\<cdot>as))))"
  by (metis assms set2tssnd_alt_bit tsprojsnd_tsabs tsremdups_tsabs)

(* replaced property 2 #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts))) \<le> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts))) *)
lemma tssnd_tsprojsnd_tsremdups:
  assumes send_def: "send \<in> tsSender"
  shows "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(send\<cdot>i\<cdot>as))) = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))"
  apply (simp add: tsprojsnd_tsabs tsremdups_tsabs sprojsnd_def)
  by (metis eta_cfun send_def set2tssnd_alt_bit_tabs sprojsnd_def srcdups_smap_com)

(* oops-Lemmata in Medium *)
text {* If infinite messages will be sent infinite messages will be transmitted. *}
lemma tsmed_tsabs_slen_inf [simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(tsAbs\<cdot>msg)=\<infinity>" 
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
  sorry

(* property 3 *)
lemma prop3: assumes p1_def: "#({True} \<ominus> p1) = \<infinity>" and p2_def: "#({True} \<ominus> p2) = \<infinity>"
  shows "#(tsAbs\<cdot>ts) = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p1))\<cdot>p2)) = \<infinity>"
  by (simp add: p1_def p2_def)

(* property 4 *)
lemma prop4: assumes "#({True} \<ominus> p) = \<infinity>"
  shows (* #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts))) \<noteq> \<infinity> *) 
  "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts)))
  \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ts))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>ts\<cdot>p))))
  \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ts)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>ts\<cdot>p)))"
  sorry

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

(* oops-Lemmata in Medium *)
text {* Two medium can be reduced to one medium. *}
lemma tsmed2med: obtains ora3 where "tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>ora3"
  sorry

(* oops-Lemmata in Medium *)
text {* Two medium with fairness requirement can be reduced to one medium with 
        fairness requirement. *}
lemma tsmed2infmed: assumes "#({True} \<ominus> ora1)=\<infinity>" and "#({True} \<ominus> ora2)=\<infinity>" 
  obtains ora3 where "tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>ora3" and "#({True} \<ominus> ora3)=\<infinity>"
  sorry

lemma lnle2le: "m < lnsuc\<cdot>n \<Longrightarrow> m \<le> n"
  apply (case_tac "m=\<infinity>", auto)
  by (metis Fin_Suc less2lnleD lncases lnsuc_lnle_emb)

lemma le2lnle: "m < \<infinity> \<Longrightarrow> lnsuc\<cdot>m \<le> n \<Longrightarrow> m < n"
  by (metis dual_order.strict_iff_order dual_order.trans leD ln_less)

(* 2nd axiom *)
lemma axiom2: assumes "send \<in> tsSender"
  shows "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) \<le> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
  using assms(1) set2tssnd_ack2trans by fastforce

(* 3rd axiom modification *)
lemma axiom3: assumes send_def: "send \<in> tsSender" and as_def: "#(tsAbs\<cdot>as) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
  proof -
    show "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as)))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      sorry
  oops

lemma tsaltbitpro_inp2out:
  assumes send_def: "send \<in> tsSender"
    and p1_def: "#({True} \<ominus> p1) = \<infinity>"
    and p2_def: "#({True} \<ominus> p2) = \<infinity>"
    and ds_def: "ds = send\<cdot>i\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>p1"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    (* definition 5 *)
    and as_def: "as = tsMed\<cdot>ar\<cdot>p2"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
  proof -
    (* #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i) *)
    have h1: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ar_def as_def dr_def p1_def p2_def prop1)
    hence h4: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    hence leq: "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> #(tsAbs\<cdot>i)"
      using ds_def send_def set2tssnd_ack2trans by fastforce
    (* #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) *)
    have hh1: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow> #(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (simp add: lnle2le)

    have hh2: "lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) < #(tsAbs\<cdot>i) \<Longrightarrow> #(tsAbs\<cdot>ds) = \<infinity>"
      by (simp add: ds_def dual_order.strict_trans2 less_asym' send_def set2tssnd_nack2inftrans)
    have hh3: "lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) < #(tsAbs\<cdot>i) \<Longrightarrow> #(tsAbs\<cdot>as) = \<infinity>"
      by (simp add: ar_def as_def dr_def hh2 p1_def p2_def)

(*
    have hh4: "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) 
      \<Longrightarrow> (#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<or> #(tsAbs\<cdot>as) \<noteq> \<infinity>)"
      sorry
*)

(* property0 medien zusammenfassen tsremdupsblatsremdups lemma *)

    have h3: "#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))
          \<or> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
      by (metis ds_def le_less_linear min_absorb2 send_def set2tssnd_ack2trans)

    have hh4: "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>ds)\<cdot>p1)\<cdot>p2))) 
                 \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>ds)\<cdot>p1)))"
      by (simp add: p2_def prop0)
    have hh5: " #(tsAbs\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>(tsProjSnd\<cdot>ds)\<cdot>p1))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: p1_def prop0)
  
    have hh6: "#p1 = \<infinity>"
      using p1_def sfilterl4 by auto
    hence hh7: "tsProjSnd\<cdot>(tsMed\<cdot>ds\<cdot>p1) = tsMed\<cdot>(tsProjSnd\<cdot>ds)\<cdot>p1"
      by (simp add: tsprojsnd_insert tsmed_map)
 
  
    have "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      apply (simp add: as_def ar_def dr_def hh7)
      sorry

(*
    hence "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<or> (#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<or> #(tsAbs\<cdot>as) \<noteq> \<infinity>)"
      sorry
    hence "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<or> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity>"
      sorry
*)
    hence geq: "#(tsAbs\<cdot>i) \<le> #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (metis ds_def dual_order.antisym h4 min_rek send_def set2tssnd_ack2trans)
    (* equalities *)
    have eq: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
      by (simp add: dual_order.antisym geq leq)
    (* property 6 *)
    have prop6: "#(tsAbs\<cdot>i) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds)))"
      by (metis ds_def eq less_lnsuc min_absorb1 send_def set2tssnd_ack2trans)
    (* property 7 *)
    have prop7: "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds)))"
      by (simp add: ds_def send_def tssnd_tsprojsnd_tsremdups)
    (* property 8 *)
    have prop8: "#(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>ds))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>dr)))"
      by (metis ar_def as_def dr_def dual_order.antisym eq p1_def p2_def prop0 prop6 prop7
          sfilterl4 tsmed_map tsprojsnd_insert)
    (* tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i *)
    have h2: "(* #(tsAbs\<cdot>i) \<noteq> \<infinity> \<Longrightarrow> *) tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>ds))"
      using dr_def p1_def prop4 prop6 prop7 prop8 by force  
    show "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>i"
      (* apply (cases "#(tsAbs\<cdot>i) \<noteq> \<infinity>", simp_all) *)
      by (simp add: ds_def eq_slen_eq_and_less h2 prop6 send_def set2tssnd_prefix_inp)      
  qed
    
end