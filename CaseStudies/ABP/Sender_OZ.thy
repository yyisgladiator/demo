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