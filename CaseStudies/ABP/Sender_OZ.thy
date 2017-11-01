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
sorry
  
lemma tssnd_nack2inftrans: "#\<surd>as = \<infinity> \<Longrightarrow> 
  #(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = \<infinity>"
apply(simp add: tsremdups_tsabs)
proof(induction i arbitrary: as ack)
  case adm
  then show ?case
    apply(rule adm_all)
    apply(rule adm_imp,simp)
    apply(rule adm_imp)
    apply(rule admI)
    apply(simp add: contlub_cfun_arg contlub_cfun_fun)
    apply(meson lnle_def lub_below monofun_cfun_arg not_le po_class.chain_def)
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
  
end