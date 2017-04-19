

(* Warning: you should not use this in production, this is just a test, use the "normal" StreamTheorie *)


(*  Title:        StreamTheorie.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de
    Description:  General Lemmas about Streams. 
                    Especially about: sinftimes, sntimes, siterate
*)

theory StreamCase_Study2

imports StreamTheorie2
begin


(* stream is defined on countables, hence the default type is set to countable *)
default_sort countable

definition f_iter:: "nat \<Rightarrow> 'a set \<Rightarrow> 'a stream set" where
"f_iter n A = iterate n\<cdot>(\<Lambda> F. { s. ((s=\<epsilon> \<or> shd s \<in> A)  \<and>  srt\<cdot>s \<in> F)})\<cdot>\<bottom>"

(* Hässliche definition, ein albtraum *)
definition F :: "'a set \<Rightarrow> 'a stream set" where
"F A = fix\<cdot>(\<Lambda> F. { s. ((s=\<epsilon> \<or> shd s \<in> A)  \<and>  srt\<cdot>s \<in> F)})"

lemma [simp]: "f_iter 0 A = UNIV"
apply(simp add: f_iter_def UU_eq_empty)
done


lemma f_monofun [simp]: "monofun (\<lambda> F. { s. ((s=\<epsilon> \<or> shd s \<in> A)  \<and>  srt\<cdot>s \<in> F)})"
apply(rule monofunI)
apply(auto simp add: less_set_def)
done

lemma f_cont[simp]: "cont (\<lambda> F. { s. ((s=\<epsilon> \<or> shd s \<in> A)  \<and>  srt\<cdot>s \<in> F)})"
apply(rule contI2)
apply simp
by (auto simp add: Inter_is_lub lub_eq_Inter less_set_def) 

lemma f_chain [simp]:"chain (\<lambda>i. f_iter i A)"
by(simp add: f_iter_def)

thm "iterate_Suc"
lemma f_unfold: "F A = { s. ((s=\<epsilon> \<or> shd s \<in> A)  \<and>  srt\<cdot>s \<in> F A)}"
apply(simp add: F_def)
apply(subst fix_eq)
apply simp
done

lemma f_iter2F:"(\<Squnion>i. f_iter i A) = F A"
apply(simp add: F_def f_iter_def fix_def)
done


lemma f_iter_Suc: "f_iter (Suc n) A = { s. ((s=\<epsilon> \<or> shd s \<in> A)  \<and>  srt\<cdot>s \<in> f_iter n A)}"
by(simp add: f_iter_def)



lemma [simp]: "{s. s = \<epsilon> \<and> \<not> sdom s \<subseteq> A} = {}"
by simp

lemma [simp]: "\<epsilon> \<in> f_iter n A"
apply(induction n)
apply simp
apply(subst  f_iter_Suc)
apply simp
done

lemma set_eq: assumes "\<And>x. x\<in>A \<Longrightarrow> x\<in>B" and "\<And>x. x\<in>B \<Longrightarrow> x\<in>A"
  shows "A=B"
by (simp add: assms(1) assms(2) eq_iff subsetI)

lemma sdom_srt: "\<not>sdom (srt\<cdot>x) \<subseteq> A \<Longrightarrow> \<not>sdom x\<subseteq> A"
by (metis Un_upper2 contra_subsetD sdom2un stream.sel_rews(2) subsetI surj_scons)


lemma sdom_srt2: assumes "x\<noteq>\<epsilon>" and "shd x\<in>A" and "sdom (srt\<cdot>x)\<subseteq>A"
  shows "sdom x\<subseteq>A"
by (smt Un_insert_left assms(1) assms(2) assms(3) contra_subsetD insert_iff sdom2un subsetI sup_bot.left_neutral surj_scons)



lemma sdom_shd: assumes "sdom s \<subseteq> A" and "s\<noteq>\<epsilon>"
  shows "shd s\<in>A"
by (metis (mono_tags, lifting) Fin_02bot assms(1) assms(2) contra_subsetD iterate_0 lnless_def lnzero_def mem_Collect_eq minimal sdom_def sdrop_def slen_empty_eq snth_def)


lemma f_iter_sdom_ind: assumes "f_iter n A = {s. sdom (stake n\<cdot>s) \<subseteq> A}"
       shows "f_iter (Suc n) A = {s. sdom (stake (Suc n)\<cdot>s) \<subseteq> A}" (is "?L = ?R")
  apply(simp add: f_iter_Suc slen_rt_ile_eq assms)
  apply (rule set_eq)
   apply (case_tac "x=\<epsilon>", simp_all)
   apply (smt inject_scons sdom_srt2 stake_Suc strictI surj_scons)
  apply (case_tac "x=\<epsilon>", simp_all)
  by (metis (no_types, lifting) lscons_conv sdom_shd sdom_srt shd1 stream.con_rews(2) stream.sel_rews(5) stream.take_rews surj_scons)


thm stake_Suc
lemma stake_Suc2: "s\<noteq>\<epsilon>\<Longrightarrow> stake (Suc n)\<cdot>s = (\<up> (shd s)) \<bullet> stake n\<cdot>(srt\<cdot>s)"
by (metis stake_Suc surj_scons)


lemma f_iter_sdom: "f_iter n A = {s. sdom (stake n\<cdot>s) \<subseteq> A}"
apply(induction n)
apply (simp)
by (metis Collect_cong f_iter_sdom_ind)


lemma snth_stake:"Fin i\<le>#s \<Longrightarrow> i<j \<Longrightarrow> snth i s = snth i (stake j\<cdot>s)"
  apply(induction i arbitrary: j s)
   apply simp
   apply (metis gr0_implies_Suc shd1 stake_Suc stream.take_strict surj_scons)
  apply(simp add: snth_rt)
  by (smt Fin_02bot Fin_Suc Suc_lessE bot_is_0 fin2stake_lemma inject_Fin inject_scons less_le linorder_not_less nat.simps(3) slen_rt_ile_eq slen_scons stake_Suc strictI strict_slen surj_scons)


lemma sdom_stake: assumes "\<And>i. sdom(stake i\<cdot>s) \<subseteq> A"
  shows "sdom s\<subseteq>A"
proof(rule ccontr)
  assume "\<not>sdom s\<subseteq>A"
  obtain i where "snth i s \<notin> A \<and> Fin i<#s" by (smt \<open>\<not> sdom s \<subseteq> A\<close> mem_Collect_eq sdom_def subsetI)
  hence snth_take: "snth i (stake (Suc i)\<cdot>s) \<notin> A" by (metis lessI less_le snth_stake)
  have "Fin (Suc i) \<le> #(stake (Suc i)\<cdot>s)" by (metis \<open>\<not> sdom s \<subseteq> A\<close> assms fin2stake infI order_refl slen_stake_fst_inf)
  hence "\<not>sdom(stake i\<cdot>s)\<subseteq>A"
    by (metis Suc_n_not_le_n assms contra_subsetD less2nat lnat_po_eq_conv not_le snth2sdom snth_take ub_slen_stake)
  thus False by (simp add: assms)
qed

lemma f_iter_lub_sdom: "(\<Squnion>i. f_iter i A) = {s. sdom s \<subseteq> A}"
  apply(simp add: lub_eq_Inter f_iter_sdom)
  apply (rule set_eq)
   apply (simp add: sdom_stake)
  apply simp
  by (metis contra_subsetD sdom_sconc split_streaml1 subsetI)

lemma f_sdom: "F A = {s. sdom s \<subseteq> A}"
by (metis Collect_cong f_iter2F f_iter_lub_sdom)



end
