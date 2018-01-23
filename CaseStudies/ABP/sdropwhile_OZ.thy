theory sdropwhile_OZ
imports Sender

begin
  
lemma sdropwhile_nle:" #(sdropwhile f\<cdot>as) \<le> #as"
  apply(induction as arbitrary: f,simp_all)
  apply(rule adm_all)
  apply (metis (mono_tags, lifting) admI inf_chainl4 inf_ub lub_eqI lub_finch2)
  by (smt less_lnsuc order_eq_iff sdropwhile_f sdropwhile_t slen_scons stream.con_rews(2) stream.sel_rews(5) surj_scons trans_lnle)
    
lemma sdropwhile_sfoot_empty:"#s < \<infinity> \<Longrightarrow>  sfoot s = sfoot (sdropwhile f\<cdot>s) \<or> sdropwhile f\<cdot>s = \<epsilon>"
  by (metis inf_ub lnless_def order_less_le sconc_fst_inf sfoot_conc slen_sconc_snd_inf stakewhileDropwhile)
  
lemma sdropwhile_nempty_empty:"#as < \<infinity> \<and>(\<exists>x. as = x \<bullet> \<up>a) \<Longrightarrow> \<exists>t. (sdropwhile f\<cdot>as) = t \<bullet> \<up>a \<or> (sdropwhile f\<cdot>as) = \<epsilon>"
  by (metis fold_inf lnsuc_lnle_emb not_le sdropwhile_sfoot_empty sfoot12 sfoot2 slen_lnsuc)

lemma sdropwhile_le:" #as\<noteq>\<infinity> \<Longrightarrow>  as\<noteq>\<epsilon> \<Longrightarrow> f (shd as) \<Longrightarrow> #(sdropwhile f\<cdot>as) < #as"   
  apply(rule_tac x=as in scases,simp_all)
  by (smt inf_ub leD ln_less order_less_le sdropwhile_nle trans_lnle)

lemma sdropwhile_lub:"\<And>Y. chain Y \<Longrightarrow>\<forall>i. sdropwhile f\<cdot>(Y i) = \<epsilon> \<Longrightarrow>sdropwhile f\<cdot>(\<Squnion>i. Y i) = \<epsilon> "
  by(simp add: contlub_cfun_arg contlub_cfun_fun)
    
lemma sdropwhile_sdrop:" #as \<noteq> \<infinity> \<Longrightarrow>\<exists>n. sdropwhile f\<cdot>as = sdrop n\<cdot>as"
proof -  
  assume a0:"#as\<noteq> \<infinity>"
  have h0:"\<exists>n. #(stakewhile f\<cdot>as) = Fin n"
    by (meson a0 dual_order.strict_trans2 inf_ub less_le lnat_well_h2 stakewhile_less)
  then show ?thesis
    using stakewhile_sdropwhilel1 by blast
qed
  
lemma sdrop_empty:"#as \<noteq> \<infinity> \<Longrightarrow> lntake n\<cdot>(#as) = (#as) \<Longrightarrow> sdrop n\<cdot>as = \<epsilon>"
  apply(induction n arbitrary: as)
  apply simp
  using lnzero_def slen_empty_eq apply auto[1]
  by (smt fold_inf inject_lnsuc lntake_more sdrop_forw_rt srt_decrements_length strict_sdrop)
  
lemma sdropwhile_all_h1:"u \<noteq> \<bottom> \<Longrightarrow> (\<And>f. \<forall>x. x \<in> sdom\<cdot>as \<longrightarrow> f x \<Longrightarrow> sdropwhile f\<cdot>as = \<epsilon>) \<Longrightarrow>  \<forall>x. x \<in> sdom\<cdot>(u && as) \<longrightarrow> f x \<Longrightarrow> sdropwhile f\<cdot>(u && as) = \<epsilon>"    
proof-
  assume a0:"u \<noteq> \<bottom>"
  assume a1:"(\<And>f. \<forall>x. x \<in> sdom\<cdot>as \<longrightarrow> f x \<Longrightarrow> sdropwhile f\<cdot>as = \<epsilon>)"
  assume a2:"\<forall>x. x \<in> sdom\<cdot>(u && as) \<longrightarrow> f x"
  have h0:" \<forall>x. x \<in> sdom\<cdot>as \<longrightarrow> f x \<Longrightarrow> sdropwhile f\<cdot>as = \<epsilon>"
    using a1 by blast
  have h1:"sdropwhile f\<cdot>(u && as) = sdropwhile f\<cdot>(as)"
    by (metis a0 a2 sdropwhile_t sfilter_ne_resup sfilter_sdoml4 stream.con_rews(2) stream.sel_rews(5) surj_scons)
  have h2:"\<forall>x. x \<in> sdom\<cdot>(as) \<longrightarrow> f x"
    by (meson a0 a2 contra_subsetD sdom_subset)
  then show ?thesis
    by (simp add: h0 h1)
qed 
  

lemma sdropwhile_all:"\<forall>x. x \<in> sdom\<cdot>(as::'a stream) \<longrightarrow> f x \<Longrightarrow>  sdropwhile f\<cdot>as = \<epsilon>"
  apply(induction as arbitrary: f)
  apply(rule adm_all)+
  apply(rule adm_imp,simp_all)
  apply(rule admI)
  apply (meson rev_subsetD sdom_chain2lub)
  by (simp add: sdropwhile_all_h1)
    
lemma sdropwhile_fair:"#({\<surd>} \<ominus> s) = \<infinity> \<Longrightarrow> \<exists>n. \<not>f (snth n s) \<Longrightarrow> #({\<surd>} \<ominus> sdropwhile f\<cdot>s) = \<infinity>"
proof -  
  assume a0:"#({\<surd>} \<ominus> s) = \<infinity>"
  assume a1:"\<exists>n. \<not>f (snth n s)"
  have h0:"\<exists>n. #(stakewhile f\<cdot>s) = Fin n"
    by (meson a1 antisym_conv3 lnat_well_h1 stakewhile_snth)
  then have h1:"\<exists>t. sdropwhile f\<cdot>s = sdrop t\<cdot>s"
    using stakewhile_sdropwhilel1 by blast
  then show ?thesis
    using a0 slen_sfilter_sdrop by force
qed
  
lemma ts_well_sdropwhile_2:"ts_well as \<Longrightarrow> sdropwhile f\<cdot>as \<noteq> \<epsilon> \<Longrightarrow>
    #({\<surd>} \<ominus> sdropwhile f\<cdot>as) \<noteq> \<infinity> \<Longrightarrow> \<exists>xa. sdropwhile f\<cdot>as = xa \<bullet> \<up>\<surd>"
proof-  
  assume a0:"ts_well as"
  assume a1:"sdropwhile f\<cdot>as \<noteq> \<epsilon>"
  assume a2:"#({\<surd>} \<ominus> sdropwhile f\<cdot>as) \<noteq> \<infinity>"
  have h0:"as = \<epsilon> \<or> #({\<surd>} \<ominus> as) = \<infinity> \<or> #as < \<infinity> \<and> (\<exists>x. as = x \<bullet> \<up>\<surd>)"
    by (meson a0 ts_well_def)
  have h1:"as = \<epsilon> \<Longrightarrow> (sdropwhile f\<cdot>as) = \<epsilon>"
    by simp
  have h2:"#({\<surd>} \<ominus> as) = \<infinity> \<Longrightarrow>  #as = \<infinity>"
    using sfilterl4 by fastforce
  have h3:"#({\<surd>} \<ominus> as) = \<infinity> \<Longrightarrow>#({\<surd>} \<ominus> sdropwhile f\<cdot>as) = \<infinity> \<or>
        (sdropwhile f\<cdot>as) = \<epsilon>"
    apply(case_tac "\<exists>n. \<not>f (snth n as)")
    apply(simp add: sdropwhile_fair)
    by (smt ex_snth_in_sfilter_nempty lnat.con_rews lnzero_def sdropwhile_all singletonD slen_empty_eq strdw_filter_h)
  have h4:"#as < \<infinity> \<and> (\<exists>x. as = x \<bullet> \<up>\<surd>) \<Longrightarrow> \<exists>t. (sdropwhile f\<cdot>as) = t \<bullet> \<up>\<surd> \<or> (sdropwhile f\<cdot>as) = \<epsilon>"
    using sdropwhile_nempty_empty by blast
  then show ?thesis
    using a1 a2 h0 h1 h3 by blast
qed    
       
lemma ts_well_sdropwhile_1:"ts_well as \<Longrightarrow> sdropwhile f\<cdot>as \<noteq> \<epsilon> \<Longrightarrow>
    #({\<surd>} \<ominus> sdropwhile f\<cdot>as) \<noteq> \<infinity> \<Longrightarrow> #(sdropwhile f\<cdot>as) < \<infinity>"  
proof-
  assume a0:"ts_well as"
  assume a1:"sdropwhile f\<cdot>as \<noteq> \<epsilon>"
  assume a2:"#({\<surd>} \<ominus> sdropwhile f\<cdot>as) \<noteq> \<infinity>"
  have h0:"as = \<epsilon> \<or> #({\<surd>} \<ominus> as) = \<infinity> \<or> #as < \<infinity> \<and> (\<exists>x. as = x \<bullet> \<up>\<surd>)"
    by (meson a0 ts_well_def)
  have h1:"as = \<epsilon> \<Longrightarrow> (sdropwhile f\<cdot>as) = \<epsilon>"
    by simp
  have h2:"#({\<surd>} \<ominus> as) = \<infinity> \<Longrightarrow> #as = \<infinity>"
    using sfilterl4 by fastforce
  have h3:"#({\<surd>} \<ominus> as) = \<infinity> \<Longrightarrow>#({\<surd>} \<ominus> sdropwhile f\<cdot>as) = \<infinity> \<or> (sdropwhile f\<cdot>as) = \<epsilon>"
    apply(case_tac "\<exists>n. \<not>f (snth n as)")
    apply(simp add: sdropwhile_fair)
    by (smt ex_snth_in_sfilter_nempty lnat.con_rews lnzero_def sdropwhile_all singletonD slen_empty_eq strdw_filter_h)
  have h4:"#as < \<infinity> \<Longrightarrow> #(sdropwhile f\<cdot>as) < \<infinity> "
    by (meson sdropwhile_nle leD leI trans_lnle)
  then show ?thesis
    using a1 a2 h0 h1 h3 by blast
qed
  
lemma ts_well_sdropwhile:assumes "ts_well as" shows "ts_well(sdropwhile f\<cdot>as)"
  apply(simp add: ts_well_def,auto)
  using ts_well_sdropwhile_1 assms apply blast
  using ts_well_sdropwhile_2 assms by blast
    
lemma cont_sdopwhile_tsabs:"cont(\<lambda>as. tsAbs\<cdot>(Abs_tstream ((sdropwhile f\<cdot>(Rep_tstream as)))))"
  by(simp add: ts_well_sdropwhile)

lemma cont_h:"chain Y \<Longrightarrow> 
(\<Squnion>i::nat. tsAbs\<cdot>(Abs_tstream (sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)\<cdot>(Rep_tstream (Y i))))) =      
tsAbs\<cdot>(Abs_tstream (sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)\<cdot>(Rep_tstream (\<Squnion>i::nat. Y i))))"
proof-
  assume a0:"chain Y"
  have h0:"cont(\<lambda>as. tsAbs\<cdot>(Abs_tstream ((sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)\<cdot>(Rep_tstream as)))))"
    by (simp add: cont_sdopwhile_tsabs )
  then show ?thesis
    by (smt a0 cont2contlubE lub_eq)
qed

lemma sdropwhile_tsabs: "sdropwhile (\<lambda> x. x=a)\<cdot>(tsAbs\<cdot>(as::'a tstream)) = tsAbs\<cdot>(Abs_tstream (sdropwhile (\<lambda> x. x= Msg a \<or> x=\<surd>)\<cdot>(Rep_tstream as)))"
  apply (induction as arbitrary: a) 
  apply (rule adm_all, rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun cont_h)
  apply simp
  apply (simp add: delayFun.rep_eq tsconc_rep_eq)
  apply(case_tac "t=a",simp_all)
  apply(simp add: tsabs_mlscons)
  apply(simp add: lscons_conv tsmlscons_lscons2 )
  apply(simp add: tsabs_mlscons)
  apply(simp add: lscons_conv tsmlscons_lscons2)
  by (metis (no_types, lifting) lscons_conv tsabs_mlscons tslscons2lscons tsmlscons2tslscons)


end