(*  Title:        StreamTheorie.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  General Lemmas about Streams. 
                    Especially about: sinftimes, sntimes, siterate
*)

theory StreamTheorie

imports Streams
begin


(* stream is defined on countables, hence the default type is set to countable *)
default_sort countable



(* Lemmas für TStream *)

(* sscanl - lemmas *)


lemma stwbl_id_help:
  shows "(\<forall>a\<in>sdom\<cdot>s. f a) \<longrightarrow> stwbl f\<cdot>s = s"
  apply (rule ind [of _s])
    apply(rule adm_imp)
     apply(rule admI, rule+)
     using l4 apply blast
    apply(rule admI)
    apply (metis cont2contlubE cont_Rep_cfun2 lub_eq)
   using strict_stwbl apply blast
  apply rule+
  by simp

lemma stwbl_id [simp]: "(\<And> a. a\<in>sdom\<cdot>s \<Longrightarrow> f a) \<Longrightarrow> stwbl f\<cdot>s = s"
by (simp add: stwbl_id_help)

lemma stwbl_notEps: "s\<noteq>\<epsilon> \<Longrightarrow> (stwbl f\<cdot>s)\<noteq>\<epsilon>"
by (smt lnat.con_rews lnzero_def sconc_snd_empty slen_scons strict_slen stwbl_f stwbl_t surj_scons)


lemma stwbl2stakewhile: assumes "a\<in>sdom\<cdot>s" and "\<not>f a"
  shows "\<exists>x. (stwbl f\<cdot>s) = stakewhile f\<cdot>s \<bullet> \<up>x" 
proof -
  have "#(stwbl f\<cdot>s) < \<infinity>" using assms(1) assms(2) snth2sdom stwbl_fin by blast
  hence "stwbl f\<cdot>s \<noteq> \<epsilon>" by (metis assms(1) assms(2) stakewhile_dom strict_stakewhile stwbl_notEps) 
  thus ?thesis
    by (smt Fin_02bot approxl2 assms(1) assms(2) bottomI lnle_def lnzero_def mem_Collect_eq sconc_snd_empty sdom_def2 sdrop_0 slen_empty_eq slen_rt_ile_eq split_streaml1 stakewhile_below stakewhile_noteq stakewhile_sdropwhilel1 stwbl_notEps stwbl_stakewhile surj_scons tdw ub_slen_stake) 
qed

lemma stwbl_sfoot: assumes "a\<in>sdom\<cdot>s" and "\<not>f a"
  shows "\<not> f (sfoot (stwbl f\<cdot>s))" 
proof(rule ccontr)
  assume "\<not> \<not> f (sfoot (stwbl f\<cdot>s))"
  hence "f (sfoot (stwbl f\<cdot>s))" by blast
  obtain x where x_def:"(stwbl f\<cdot>s) = stakewhile f\<cdot>s \<bullet> \<up>x"
    using assms(1) assms(2) stwbl2stakewhile by blast
  hence "sfoot (stwbl f\<cdot>s) = x"
    using assms(1) assms(2) sfoot1 stwbl_fin by blast
  have "stakewhile f\<cdot>s \<bullet> \<up>x \<sqsubseteq> s" by (metis stwbl_below x_def)
  have "f x"
    using \<open>f (sfoot (stwbl f\<cdot>s))\<close> \<open>sfoot (stwbl f\<cdot>s) = x\<close> by blast
  thus False
    by (smt Fin_02bot \<open>sfoot (stwbl f\<cdot>s) = x\<close> approxl2 assms(1) assms(2) assoc_sconc bottomI lnle_def lnzero_def sconc_fst_empty sconc_snd_empty sdrop_0 sdropwhile_t sfoot1 slen_empty_eq slen_rt_ile_eq split_streaml1 stakewhile_below stakewhile_dom stakewhile_sdropwhilel1 stakewhile_stwbl stream.take_strict strict_stakewhile stwbl_fin stwbl_notEps stwbl_stakewhile surj_scons tdw ub_slen_stake)
qed

lemma stwbl2stbl[simp]: "stwbl f\<cdot>(stwbl f\<cdot>s) = stwbl f\<cdot>s"
  apply(rule ind [of _s])
    apply simp_all
  by (metis sconc_snd_empty stwbl_f stwbl_t)


lemma stakewhileDropwhile[simp]: "stakewhile f\<cdot>s \<bullet> (sdropwhile f\<cdot>s) = s "
  apply(rule ind [of _s])
    apply (rule admI)
    apply (metis (no_types, lifting) approxl2 inf_chainl4 lub_eqI lub_finch2 sconc_fst_inf split_streaml1 stakewhile_below stakewhile_sdropwhilel1)
   apply simp
  by (metis assoc_sconc sconc_fst_empty sdropwhile_f sdropwhile_t stakewhile_t tdw)

lemma stwbl_eps: "stwbl f\<cdot>s = \<epsilon> \<longleftrightarrow> s=\<epsilon>"
using strict_stwbl stwbl_notEps by blast


lemma srtdw_stwbl [simp]: "srtdw f\<cdot> (stwbl f\<cdot>s) = \<epsilon>" (is "?F s")
proof(rule ind [of _s ])
  show "adm ?F" by simp
  show "?F \<epsilon>" by simp

  fix a
  fix s
  assume IH: "?F s"
  thus "?F (\<up>a \<bullet> s)" 
  proof (cases "f a")
    case True thus ?thesis by (simp add: IH)
  next
    case False thus ?thesis by simp
  qed
qed


lemma sconc_neq_h: assumes "s1 \<noteq> s2"
  shows "#a < \<infinity> \<longrightarrow> a \<bullet> s1 \<noteq> a \<bullet> s2"
  apply(rule ind [of _a ])
    apply(rule admI)
    apply (rule impI)
    apply (metis inf_chainl4 l42 neq_iff)
   apply (simp add: assms)
  by (metis inf_ub inject_scons less_le sconc_scons slen_sconc_snd_inf)
 
lemma sconc_neq: assumes "s1 \<noteq> s2" and "#a < \<infinity>"
  shows "a \<bullet> s1 \<noteq> a \<bullet> s2"
using assms(1) assms(2) sconc_neq_h by blast


lemma adm_nsdom [simp]:  "adm (\<lambda>x. b \<notin> sdom\<cdot>x)"
proof (rule admI)
  fix Y
  assume as1: "chain Y" and as2: "\<forall>i. b\<notin>sdom\<cdot>(Y i)"
  thus "b\<notin>sdom\<cdot>(\<Squnion>i. Y i)"
  proof (cases "finite_chain Y")
    case True thus ?thesis using as1 as2 l42 by fastforce 
  next
    case False
    hence "#(\<Squnion>i. Y i) = \<infinity>" using as1 inf_chainl4 by blast
    hence "\<And>n. snth n (\<Squnion>i. Y i) \<noteq> b"
    proof -
      fix n
      obtain j where "Fin n < # (Y j)"  by (metis False Streams.inf_chainl2 as1 inf_chainl3rf less_le) 
      hence "snth n (Y j) \<noteq>b" using as2 snth2sdom by blast
      thus "snth n (\<Squnion>i. Y i) \<noteq> b" using \<open>Fin n < #(Y j)\<close> as1 is_ub_thelub snth_less by blast
    qed
    thus ?thesis using sdom2snth by blast 
  qed
qed

lemma strdw_filter_h: "b\<in>sdom\<cdot>s \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>s)) = #({b} \<ominus> s)"
proof(rule ind [of _s])
  have "adm (\<lambda>a. lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>a)) = #({b} \<ominus> a))" by simp
  thus "adm (\<lambda>a. b \<in> sdom\<cdot>a \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>a)) = #({b} \<ominus> a))" by(simp add: adm_nsdom)
  show "b \<in> sdom\<cdot>\<epsilon> \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>\<epsilon>)) = #({b} \<ominus> \<epsilon>)" by simp
  fix a 
  fix s
  assume IH: " b \<in> sdom\<cdot>s \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>s)) = #({b} \<ominus> s)"
  show " b \<in> sdom\<cdot>(\<up>a \<bullet> s) \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(\<up>a \<bullet> s))) = #({b} \<ominus> \<up>a \<bullet> s)"
  proof (cases "a=b")
    case True thus ?thesis by (simp add: sfilter_in singletonI slen_scons stwbl_f stwbl_srtdw) 
  next
    case False
    hence f1:"#({b} \<ominus> \<up>a \<bullet> s) = #({b} \<ominus> s)" using sfilter_nin singletonD by auto
    hence f2:"#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(\<up>a \<bullet> s)) = #({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(s))" using False by auto
    hence "b \<in> sdom\<cdot>(\<up>a \<bullet> s) \<Longrightarrow> b\<in>sdom\<cdot>s" using False by auto
    thus ?thesis using IH f2 local.f1 by auto 
  qed
qed

lemma strdw_filter: "b\<in>sdom\<cdot>s \<Longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>s)) = #({b} \<ominus> s)"
by(simp add: strdw_filter_h)


lemma stwbl_filterlen[simp]: "b\<in>sdom\<cdot>ts \<longrightarrow> #({b} \<ominus> stwbl (\<lambda>a. a \<noteq> b)\<cdot>ts) = Fin 1"
  apply(rule ind [of _ ts])
    apply(rule adm_imp)
     apply simp
    apply simp
   apply simp
  apply auto
  by (metis (mono_tags, lifting) Fin_02bot Fin_Suc One_nat_def lnzero_def sconc_snd_empty sfilter_in sfilter_nin singletonD singletonI slen_scons strict_sfilter strict_slen stwbl_f stwbl_t)


lemma srtdw_conc: "b\<in>sdom\<cdot>ts  \<Longrightarrow> (srtdw (\<lambda>a. a \<noteq> b)\<cdot>(ts \<bullet> as)) = srtdw (\<lambda>a. a \<noteq> b)\<cdot>(ts) \<bullet> as"
  apply(induction ts arbitrary: as)
    apply (rule adm_imp)
     apply auto
   apply(rule admI)
   apply rule+
   apply (metis (no_types, lifting) approxl3 assoc_sconc is_ub_thelub)
proof -
  fix u ts as
  assume as1: "u \<noteq> \<bottom>" and as2: "(\<And>as. b \<in> sdom\<cdot>ts \<Longrightarrow> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(ts \<bullet> as) = srtdw (\<lambda>a. a \<noteq> b)\<cdot>ts \<bullet> as)"
       and as3: "b \<in> sdom\<cdot>(u && ts)"
  obtain a where a_def: "updis a = u" by (metis Exh_Up as1 discr.exhaust) 
  have "a\<noteq>b \<Longrightarrow> b\<in>sdom\<cdot>ts" by (metis UnE a_def as3 lscons_conv sdom2un singletonD) 
  hence "a\<noteq>b \<Longrightarrow> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(\<up>a\<bullet> (ts \<bullet> as)) = srtdw (\<lambda>a. a \<noteq> b)\<cdot>(\<up>a\<bullet> ts) \<bullet> as " using as2 a_def by auto
  thus "srtdw (\<lambda>a. a \<noteq> b)\<cdot>((u && ts) \<bullet> as) = srtdw (\<lambda>a. a \<noteq> b)\<cdot>(u && ts) \<bullet> as "
    by (smt a_def inject_scons lscons_conv sconc_scons stwbl_f stwbl_srtdw) 
qed


lemma stwbl_conc[simp]: "b\<in>sdom\<cdot>ts \<Longrightarrow>
    (stwbl (\<lambda>a. a \<noteq> b)\<cdot>(stwbl (\<lambda>a. a \<noteq> b)\<cdot>ts \<bullet> xs)) =
    (stwbl (\<lambda>a. a \<noteq> b)\<cdot>(ts))"
  apply(induction ts)
    apply(rule adm_imp)
     apply simp
    apply(rule admI)
    apply (metis (no_types, lifting) ch2ch_Rep_cfunR contlub_cfun_arg inf_chainl4 lub_eqI lub_finch2 sconc_fst_inf stwbl2stbl)
   apply simp
  by (smt UnE assoc_sconc sdom2un singletonD stream.con_rews(2) stream.sel_rews(5) stwbl_f stwbl_t surj_scons)











(* takes a function and 2 streams, merges the 2 streams according to the function *)
definition merge:: "('a  \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a stream \<rightarrow> 'b stream \<rightarrow> 'c stream" where
"merge f \<equiv> \<Lambda> s1 s2 . smap (\<lambda> s3. f (fst s3) (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2)"


lemma merge_unfold: "merge f\<cdot>(\<up>x \<bullet> xs)\<cdot>(\<up>y\<bullet> ys) = \<up>(f x y) \<bullet> merge f\<cdot>xs\<cdot>ys"
  by(simp add: merge_def)

lemma merge_snth[simp]: "Fin n <#xs \<Longrightarrow>Fin n < #ys \<Longrightarrow> snth n (merge f\<cdot>xs\<cdot>ys) = f (snth n xs) (snth n ys)"
  apply(induction n arbitrary:xs ys)
   apply (metis Fin_02bot merge_unfold lnless_def lnzero_def shd1 slen_empty_eq snth_shd surj_scons)
  by (smt Fin_Suc Fin_leq_Suc_leq Suc_eq_plus1_left merge_unfold inject_lnsuc less2eq less2lnleD lnle_conv lnless_def lnsuc_lnle_emb sconc_snd_empty sdropostake shd1 slen_scons snth_rt snth_scons split_streaml1 stream.take_strict surj_scons ub_slen_stake)

lemma merge_eps1[simp]: "merge f\<cdot>\<epsilon>\<cdot>ys = \<epsilon>"
  by(simp add: merge_def)

lemma merge_eps2[simp]: "merge f\<cdot>xs\<cdot>\<epsilon> = \<epsilon>"
  by(simp add: merge_def)

lemma [simp]: "srt\<cdot>(merge f\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>b \<bullet> bs)) = merge f\<cdot>as\<cdot>bs"
  by (simp add: merge_unfold)

lemma merge_len [simp]: "#(merge f\<cdot>as\<cdot>bs) = min (#as) (#bs)"
by(simp add: merge_def)

lemma merge_commutative: assumes "\<And> a b. f a b = f b a"
  shows "merge f\<cdot>as\<cdot>bs = merge f\<cdot>bs\<cdot>as"
  apply(rule snths_eq)
   apply (simp add: min.commute)
  by (simp add: assms)
  

end