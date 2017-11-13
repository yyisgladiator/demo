theory Sender_OZ
imports Sender

begin
  
lemma h2:"i \<noteq> \<bottom> \<Longrightarrow> (tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>tsInfTick\<cdot>(Discr ack))) = \<up>(t, ack)\<infinity> \<bullet> (tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>tsInfTick\<cdot>(Discr ack))) "
  by (smt delayfun_nbot lscons_conv s2sinftimes sconc_fst_inf slen_sinftimes strict_icycle tsabs_delayfun tsabs_mlscons tsinftick_unfold tssnd_h_delayfun_nack)  
  
lemma hhhhh:"#(tsAbs\<cdot>i) \<noteq> 0 \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>tsInfTick\<cdot>(Discr ack))) = \<infinity>"  
proof(induction i arbitrary: ack)
  case adm
  then show ?case
  by(rule adm_imp,simp+)
next
  case bottom
  then show ?case 
  by simp
next
  case (delayfun i)
  then show ?case
  by (metis tsabs_delayfun tsinftick_unfold tssnd_h_delayfun)
next
  case (mlscons i t)
  then show ?case
  apply(simp add: tsabs_mlscons)
  using h2 by fastforce
qed
  
lemma tssnd_nack2inftrans_h:"#\<surd>as = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> #(tsAbs\<cdot>as)\<noteq> \<infinity> \<Longrightarrow> (\<exists>k. i = k \<bullet>\<surd> is) 
       \<and> (#(tsAbs\<cdot>is)\<noteq>0) \<and> ((\<exists>t. (tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)) = t \<bullet>\<surd> (tsSnd_h\<cdot>is\<cdot>tsInfTick\<cdot>(Discr ack)))\<or>(\<exists>t. (tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)) = t \<bullet>\<surd> (tsSnd_h\<cdot>is\<cdot>tsInfTick\<cdot>(Discr (\<not>ack)))))"
oops

lemma tssnd_h_tsAbs_nbot: "tsAbs\<cdot>msg \<noteq> \<epsilon> \<Longrightarrow>  #\<surd> acks = \<infinity> \<Longrightarrow> tsAbs\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)) \<noteq> \<epsilon>"
  apply (induction acks arbitrary: msg ack)
  apply (simp_all)
  apply (rule adm_all, rule adm_imp,simp, rule adm_imp,simp)
  apply (rule_tac ts=msg in tscases, simp_all)
  apply (simp add: delayfun_tslscons tsmlscons_lscons)
  apply (case_tac "t=ack", simp_all)
  apply (meis tsmlscons_bot2 tsmlscons_nbot tssnd_h_mlscons_ack up_defined)
  by (mets tsmlscons_bot2 tsmlscons_nbot tssnd_h_mlscons_nack up_defined)

lemma tssnd_nack2inftrans_h2: "#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = Fin k \<Longrightarrow> #\<surd> as = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<ge> #(tsAbs\<cdot>i)"
  apply (erule_tac contrapos_pp)

apply (induction k arbitrary: i as ack,simp_all)
  apply (case_tac "tsAbs\<cdot>i=\<epsilon>",simp)
  apply (erule_tac contrapos_pp)
  apply (simp add: tssnd_h_tsAbs_nbot)
  
  apply (rule_tac ts=i in tscases,simp_all)
  apply (rule_tac ts=as in tscases,simp_all)
  apply (simp add: tssnd_h_delayfun tsremdups_insert tsremdups_h_delayfun)
  using shit apply blast
  apply (metis delay_infTick shit tsabs_delayfun tsremdups_insert)
  apply (rule_tac ts=as in tscases,simp_all)
  apply (metis delay_infTick shit tsremdups_insert)
oops

lemma tssnd_infmsg2inftrans: "#\<surd> as = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>i) = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = \<infinity>"
sorry

lemma less_fin:" n < Fin k \<Longrightarrow> \<exists>k2. n = Fin k2"
  using lnat_well_h1 by blast

lemma nmsg_inftick: "tsAbs\<cdot>as = \<epsilon> \<Longrightarrow> #\<surd> as = \<infinity> \<Longrightarrow> as = tsInfTick"
sorry

lemma tssnd_fmsg2inftrans: assumes "#(tsAbs\<cdot>i) = Fin k" "#(srcdups\<cdot>(tsAbs\<cdot>as)) = Fin k2"  "#(srcdups\<cdot>(tsAbs\<cdot>as)) < Fin k" " #\<surd> as = \<infinity>" shows "#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = \<infinity>"
  using assms apply(induction "(srcdups\<cdot>(tsAbs\<cdot>as))" arbitrary: i as ack k k2 rule: finind)
  using assms apply simp
  apply (case_tac "tsAbs\<cdot>i = \<epsilon>",simp)
  using hhhhh nmsg_inftick srcdups_nbot apply auto[1]
  apply (simp)
  apply (subst srcdups_step)
  using lnat_well_h1 apply forc

sorry

lemma tssnd_nack2inftrans: 
  "#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> #\<surd>as = \<infinity> \<Longrightarrow>  #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = \<infinity>"
(*  apply (erule_tac contrapos_pp)
  using ninf2Fin [of "#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))"] apply auto
  by (simp add: leD tssnd_nack2inftrans_h2) *)
  apply (case_tac "#(tsAbs\<cdot>i) = \<infinity>")
  apply (simp add:  tssnd_infmsg2inftrans)
   using ninf2Fin [of "#(tsAbs\<cdot>i)"] apply auto
apply(simp add: tsremdups_tsabs)
  using tssnd_fmsg2inftrans by blast
proof(induction "tsAbs\<cdot>i" arbitrary: i as ack rule: finind)
  case adm
  then show ?case
    apply(rule adm_all)
    apply(rule adm_imp)
    apply (simp add: not_less)
    apply (sm adm_upward min.coboundedI2 min_def mono_slen monofun_cfun_arg)
    apply(rule admI)
    apply(simp add: contlub_cfun_arg contlub_cfun_fun)
    apply(meso lnle_def lub_below monofun_cfun_arg not_le po_class.chain_def)
    by simp
next
  case bottom
  then show ?case 
  by (metis lnle_def lnzero_def minimal not_less strict_slen tsabs_bot)
next
  case (delayfun i)
  then show ?case 
    apply(rule_tac ts = as in tscases, simp_all)
    apply(simp add: tssnd_h_delayfun)
    apply(simp add: delayFun_def)
    apply(case_tac "as= \<bottom>",simp_all)
    by(simp add: tssnd_h_delayfun_msg tsabs_mlscons lscons_conv tstickcount_mlscons)
next
  case (mlscons i t)
  then show ?case 
    apply(simp add: tsabs_mlscons lscons_conv)
    by (metis (no_types, lifting) fold_inf inf_less_eq lnle2le mlscons.prems(2) neq_iff srcdups2srcdups strict_slen tsabs_bot tsremdups_tsabs tsremdups_tstickcount tssnd_nack2inftrans_h)  
qed 
  

lemma adm_H:"adm (\<lambda>xa. #\<surd> x \<le> #\<surd> f\<cdot>xa)"
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  by (meson below_lub lnle_def monofun_cfun_arg po_class.chain_def)

lemma adm_H2:"adm (\<lambda>xa. #\<surd> x \<ge> #\<surd> f\<cdot>xa)"    
  apply(rule admI)  
  apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  by (meson lnle_def lub_below monofun_cfun_arg po_class.chain_def)

lemma adm_slen_smaller:"adm (\<lambda>xa. \<not> #xa < #x)"
  apply(rule admI)
  by (metis ch2ch_Rep_cfunR contlub_cfun_arg inf_ub l42 not_less unique_inf_lub)
    
lemma adm_slen_tsabs_smaller:"adm (\<lambda>xa. \<not> #(tsAbs\<cdot>xa) < #(tsAbs\<cdot>x))"
  apply(rule admI)
  apply(simp add: not_less contlub_cfun_arg contlub_cfun_fun)
  by (meson below_lub lnle_def monofun_cfun_arg po_class.chain_def)
    
    
lemma tssnd_as_inftick_h2:" #(srcdups\<cdot>(\<up>False \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>i)) \<Longrightarrow>
            (*(\<And>i. #(srcdups\<cdot>(tsAbs\<cdot>as)) < #(tsAbs\<cdot>i) \<Longrightarrow> #\<surd> as \<le> #\<surd> tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr True)) \<Longrightarrow>*)
            i \<noteq> \<bottom> \<Longrightarrow> as \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> #\<surd> tsSnd_h\<cdot>(updis a &&\<surd> i)\<cdot>as\<cdot>(Discr True)"
proof(induction as arbitrary: i a)
  case adm
  then show ?case 
  apply(rule adm_all)
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: not_less contlub_cfun_arg contlub_cfun_fun)
  apply(meson below_lub lnle_def monofun_cfun_arg po_class.chain_def)
  apply(rule adm_imp,simp)
  apply(rule adm_imp,simp)
  apply(rule admI)
  by(simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
next
  case bottom
  then show ?case 
  by simp  
next
  case (delayfun as)
  then show ?case
  apply(simp add: tssnd_h_delayfun_nack tstickcount_mlscons)
  apply(simp add: delayFun_def)
  by fastforce
next
  case (mlscons as t)
  then show ?case 
  apply(case_tac "t= True",simp_all)
  apply(simp add: tssnd_h_mlscons_ack tstickcount_mlscons tsabs_mlscons lscons_conv)defer
  apply(simp add: tssnd_h_mlscons_nack tstickcount_mlscons tsabs_mlscons lscons_conv)
  sorry
qed
    
lemma tssnd_as_inftick_h:"#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>as)) < #(tsAbs\<cdot>i) \<Longrightarrow>
          (*(\<And>i. #(srcdups\<cdot>(tsAbs\<cdot>as)) < #(tsAbs\<cdot>i) \<Longrightarrow> #\<surd> as \<le> #\<surd> tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr True)) \<Longrightarrow>*)
          as \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>i\<cdot>(updis t &&\<surd> as)\<cdot>(Discr True))"
proof(induction i arbitrary: as t)
  case adm
  then show ?case 
  apply(rule adm_all)
  apply(rule adm_all)
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: not_less contlub_cfun_arg contlub_cfun_fun)
  apply(meson lnle_def lub_below monofun_cfun_arg not_le po_class.chain_def)
  apply(rule adm_imp,simp)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  sorry
next
  case bottom
  then show ?case 
  apply simp
  by (metis below_bottom_iff lnless_def lnzero_def)
next
  case (delayfun i)
  then show ?case 
    apply(simp add: tssnd_h_delayfun_msg)
    apply(simp add: delayFun_def)
    using dual_order.trans less_lnsuc by blast
next
  case (mlscons i ta)
  then show ?case 
  apply(case_tac "i=\<bottom>",simp_all)
  apply(case_tac "t=True",simp_all)
  apply(simp add: tssnd_h_mlscons_ack tstickcount_mlscons tsabs_mlscons lscons_conv)defer
  apply(simp add: tssnd_h_mlscons_nack tstickcount_mlscons tsabs_mlscons lscons_conv)
  using less_lnsuc trans_lnle tssnd_as_inftick_h2 apply blast    
  sorry
qed     
    
lemma tssnd_as_inftick:"#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> lnsuc\<cdot>(#\<surd>as) \<le> #\<surd>(tsSnd\<cdot>i\<cdot>as)"
apply(simp add: tsSnd_def)
apply(simp add: delayFun_def)
apply(simp add: tsremdups_tsabs)
proof(induction as arbitrary: i)
  case adm
  then show ?case
  apply(rule adm_all)
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: not_less contlub_cfun_arg contlub_cfun_fun)
  apply(meson below_lub lnle_def monofun_cfun_arg po_class.chain_def)
  apply(rule admI)
  by(simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
next
  case bottom
  then show ?case by simp
next
  case (delayfun as)
  then show ?case 
  apply(rule_tac ts = i in tscases,simp_all)
  apply(metis below_bottom_iff lnless_def lnzero_def)
  apply(simp add: tssnd_h_delayfun)
  apply(simp add: delayFun_def)
  apply(case_tac "as=\<bottom>",simp_all)
  apply(metis below_bottom_iff lnless_def lnzero_def)
  apply(simp add: tssnd_h_delayfun_nack tstickcount_mlscons)
  by(simp add: delayFun_def)
next
  case (mlscons as t)
  then show ?case
  apply(rule_tac ts = i in tscases,simp_all)
  apply (metis below_bottom_iff lnless_def lnzero_def)
  apply(rename_tac it) 
  apply(case_tac "as=\<bottom>",simp_all)
  apply(simp add: tssnd_h_delayfun_msg tstickcount_mlscons tsabs_mlscons lscons_conv)
  apply(simp add: delayFun_def)
  using tssnd_as_inftick_h apply blast
  apply(case_tac "as=\<bottom>",simp_all)
  apply(metis below_bottom_iff lnless_def lnzero_def)
  apply(case_tac "t=True",simp_all)    
  apply(simp add: tssnd_h_mlscons_ack)
  apply(simp add: tsabs_mlscons lscons_conv tstickcount_mlscons)defer
  apply(simp add: tssnd_h_mlscons_nack tstickcount_mlscons tsabs_mlscons lscons_conv tssnd_as_inftick_h2)
  sorry
qed
(*proof(induction i arbitrary: as ack)
  case adm
  then show ?case 
    apply(rule adm_all)
    apply(rule adm_imp)
    apply(rule admI)
    apply(simp add: contlub_cfun_arg contlub_cfun_fun)
    apply(meson lnle_def lub_below monofun_cfun_arg not_le po_class.chain_def)
    apply(rule admI)
    apply(simp add: contlub_cfun_arg contlub_cfun_fun)
        sorry
next
  case bottom
  then show ?case 
    apply simp
    by (metis below_bottom_iff lnless_def lnzero_def neq_iff)
next
  case (delayfun ia)
  then show ?case 
    apply(rule_tac ts = as in tscases, simp_all)
    apply(simp add: tssnd_h_delayfun)
    apply(simp add: delayFun_def)
    apply(case_tac "as= \<bottom>",simp_all)
    apply(simp add: tssnd_h_delayfun_msg tsabs_mlscons lscons_conv tstickcount_mlscons)
    apply(simp add: delayFun_def)
    by (metis (no_types, lifting) less_lnsuc lscons_conv trans_lnle tsabs_mlscons tstickcount_mlscons)
next
  case (mlscons ia t)
  then show ?case
  apply(rule_tac ts = as in tscases, simp_all)
  apply(case_tac "ia \<noteq> \<bottom>",simp_all) 
  apply(simp add: tssnd_h_delayfun_nack tstickcount_mlscons)
  apply(simp add: delayFun_def)defer
  apply(case_tac "ia \<noteq> \<bottom>",simp_all)
  apply(case_tac "as \<noteq> \<bottom>",simp_all)
  apply(case_tac "a = true", simp_all)
      apply(simp add: tssnd_h_mlscons_ack tstickcount_mlscons tsabs_mlscons lscons_conv)
      defer
      apply(simp add: tssnd_h_mlscons_nack tstickcount_mlscons tsabs_mlscons lscons_conv)
  sorry
qed  *)
  
end