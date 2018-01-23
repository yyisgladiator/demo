theory Sender_OZ
imports sdropwhile_OZ

begin
fixrec tsDropFirst2 :: " 'a tstream \<rightarrow> 'a tstream" where
"tsDropFirst2\<cdot>\<bottom> = \<bottom>" |
"tsDropFirst2\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = (tsDropFirst2\<cdot>ts)" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsDropFirst2\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = ts"

fixrec tsTickDrop :: " 'a tstream \<rightarrow> 'a tstream" where
"tsTickDrop\<cdot>\<bottom> = \<bottom>" |
"tsTickDrop\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = (tsTickDrop\<cdot>ts)" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsTickDrop\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = tsMLscons\<cdot>(up\<cdot>t)\<cdot>ts"

fixrec tsDropFirst3 :: " 'a tstream \<rightarrow> 'a tstream" where
"tsDropFirst3\<cdot>\<bottom> = \<bottom>" |
"tsDropFirst3\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = (tsDropFirst3\<cdot>ts)" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsDropFirst3\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = tsTickDrop\<cdot>ts"
  
fixrec tsDropWhile2 :: "'a discr \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsDropWhile2\<cdot>a\<cdot>\<bottom> = \<bottom>" |
"tsDropWhile2\<cdot>a\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = tsDropWhile2\<cdot>a\<cdot>ts" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsDropWhile2\<cdot>a\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = 
  (if t = a then tsDropWhile2\<cdot>a\<cdot>ts else tsMLscons\<cdot>(up\<cdot>t)\<cdot>ts)"

lemma stake_lntake_h:"(\<And>(i::'a stream). #(stake k\<cdot>i) = lntake k\<cdot>(#i)) \<Longrightarrow> #(stake (Suc k)\<cdot>(i::'a stream)) = lntake (Suc k)\<cdot>(#i)"
proof-
  assume a0:"(\<And>(i::'a stream). #(stake k\<cdot>i) = lntake k\<cdot>(#i))"
  have h0:"#(stake k\<cdot>(srt\<cdot>i)) = lntake k\<cdot>(#(srt\<cdot>i))"
    by (insert a0 [of "(srt\<cdot>i)"], auto)
  then show ?thesis
    by (metis lnat.take_strict lntake_more lnzero_def slen_scons stake_Suc stream.take_strict strict_slen surj_scons)
qed
  
lemma stake_lntake:"#(stake k\<cdot>i) = lntake k\<cdot>(#i)"
  apply(induction k arbitrary: i,simp)
  apply (simp add: lnzero_def)
  by (simp add: stake_lntake_h)

lemma stake2inf:"\<forall>k. #i > #(stake k\<cdot>i) \<Longrightarrow> #i = \<infinity>"
proof-
  assume a0:"\<forall>k. #i > #(stake k\<cdot>i)"
  have h0:"(\<forall>k. lntake k\<cdot>(#i) \<noteq> #i)"
    by (metis a0 lnless_def stake_lntake)
  then show ?thesis
    using nreach_lnat_rev by auto
qed
  
lemma tssnd_h_tsabs_nbot:"#(tsAbs\<cdot>i) \<noteq> \<bottom> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<noteq> \<bottom> \<Longrightarrow> tsAbs\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) \<noteq> \<bottom>"  
  apply(simp add: tsremdups_tsabs)
  apply(induction i arbitrary: as ack)
  apply(rule adm_imp,simp)
  apply(rule adm_all)
  apply(rule adm_imp,simp)
  apply(rule adm_all,simp)
  apply simp
  apply (simp add: lnzero_def)
  apply(rule_tac ts=as in tscases,simp_all)  
  apply (simp add: lnzero_def)
  apply(simp add: tssnd_h_delayfun)
  apply(case_tac "asa=\<bottom>",simp)
  apply (simp add: lnzero_def)
  apply(simp add: tssnd_h_delayfun_msg)
  apply(rule_tac ts=as in tscases,simp_all)  
  apply (simp add: lnzero_def)
  apply(case_tac "i=\<bottom>",simp)
  apply(simp add:tssnd_h_delayfun_nack tsabs_mlscons lscons_conv srcdups_nbot)
  apply(case_tac "i=\<bottom>",simp)
  apply(case_tac "asa=\<bottom>",simp)
  apply (simp add: lnzero_def)
  apply(case_tac "a=ack",simp_all)
  apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv srcdups_nbot)  
  by(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv srcdups_nbot)

lemma not_le_zero_eq:"\<not> 0 < #x \<Longrightarrow> #x = 0"
  using gr_0 slen_empty_eq srt_decrements_length by blast  
  
lemma tsabs_tsconc_tsinftick:"tsAbs\<cdot>(as \<bullet>\<surd> tsInfTick) = tsAbs\<cdot>(as)"
  apply(induction as)
  apply(rule admI)
  using l42 apply force
  apply simp
  apply (simp add: tsconc_delayfun)
  by (metis below_bottom_iff ts_tsconc_prefix tsabs_mlscons tsconc_mlscons)

lemma tstickdrop_mlscons:"i \<noteq> \<bottom> \<Longrightarrow> tsTickDrop\<cdot>(updis t &&\<surd> i) = (updis t &&\<surd> i)"
  by (simp add: tsmlscons_lscons)  

lemma tstickdrop_delayfun:"tsTickDrop\<cdot>(delayFun\<cdot>i) = tsTickDrop\<cdot>i"
  by (simp add: delayfun_tslscons)     
    
lemma tsdropfirst3_mlscons:"i \<noteq> \<bottom> \<Longrightarrow> tsDropFirst3\<cdot>(updis t &&\<surd> i) = tsTickDrop\<cdot>i"
  by (simp add: tsmlscons_lscons)
  
lemma tsdropfirst3_delayfun:"tsDropFirst3\<cdot>(delayFun\<cdot>i) = tsDropFirst3\<cdot>i"
  by (simp add: delayfun_tslscons)
    
lemma tsdropfirst2_mlscons:"i \<noteq> \<bottom> \<Longrightarrow> tsDropFirst2\<cdot>(updis t &&\<surd> i) = i"
  by (simp add: tsmlscons_lscons)
  
lemma tsdropfirst2_delayfun:"tsDropFirst2\<cdot>(delayFun\<cdot>i) = tsDropFirst2\<cdot>i"
  by (simp add: delayfun_tslscons)

lemma tsdropwhile2_delayfun: "tsDropWhile2\<cdot>a\<cdot>(delayFun\<cdot>as) = (tsDropWhile2\<cdot>a\<cdot>as)"
  by (simp add: delayfun_tslscons) 

lemma tsdropwhile2_t: "tsDropWhile2\<cdot>(Discr a)\<cdot>(updis a &&\<surd> as) = tsDropWhile2\<cdot>(Discr a)\<cdot>as"
  by (metis tsDropWhile2.simps(3) tsmlscons_lscons tsmlscons_nbot_rev)

lemma tsdropwhile2_f: "a \<noteq> b \<Longrightarrow>tsDropWhile2\<cdot>(Discr a)\<cdot>(updis b &&\<surd> as) = updis b &&\<surd> as"
  by (metis discr.inject tsDropWhile2.simps(1) tsDropWhile2.simps(3) tsmlscons_lscons tsmlscons_nbot_rev)

lemma tsdropwhile2_strict: "tsDropWhile2\<cdot>a\<cdot>\<bottom> = \<bottom>"
  by simp
    
lemma tsabs_tstickdrop:"tsAbs\<cdot>(tsTickDrop\<cdot>as) = tsAbs\<cdot>as"
  apply(induction as,simp_all)
  apply(simp add: tstickdrop_delayfun)
  by(simp add: tstickdrop_mlscons)

lemma tsdropfirst3_rt:"(tsAbs\<cdot>(tsDropFirst3\<cdot>i)) = srt\<cdot>(tsAbs\<cdot>i)"
  apply(induction i,simp_all)
  apply(simp add: tsdropfirst3_delayfun)
  by(simp add: tsdropfirst3_mlscons tsabs_mlscons tsabs_tstickdrop)
    
lemma tsdropfirst3_first:"tsAbs\<cdot>i = \<up>a \<bullet> s \<Longrightarrow> (tsAbs\<cdot>(tsDropFirst3\<cdot>i)) = s"
  by (simp add: tsdropfirst3_rt)
    
lemma tsdropwhile_2le2_h:"lnsuc\<cdot>(#(srcdups\<cdot>(tsAbs\<cdot>(tsDropWhile2\<cdot>(Discr a)\<cdot>as)))) = #(srcdups\<cdot>(\<up>a \<bullet> tsAbs\<cdot>as))"
  apply(induction as arbitrary:a,simp_all)
  apply(simp add: tsdropwhile2_delayfun)
  apply(case_tac "t=a",simp_all)
  apply(simp add: tsdropwhile2_t tsabs_mlscons lscons_conv)
  by(simp add: tsdropwhile2_f tsabs_mlscons lscons_conv)
    
lemma tsdropwhile2_le2:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis a \<Longrightarrow> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr a)\<cdot>as)))) = #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
  apply(simp add: tsremdups_tsabs)
  apply(induction as arbitrary: a,simp_all)
  apply(simp add: tsdropwhile2_delayfun)
  apply(case_tac "t=a",simp_all)
  apply(simp add: tsdropwhile2_t tsabs_mlscons lscons_conv)
  using tsdropwhile_2le2_h apply blast  
  apply(simp add: tsabs_mlscons lscons_conv)
  by (metis lshd_updis srcdups_ex updis_eq)

lemma cont_srt_sdropwhile:"cont(\<lambda>as. (Abs_tstream (srt\<cdot>(sdropwhile f\<cdot>(Rep_tstream as)))))"
  by(simp add: ts_well_sdropwhile)    
    
lemma tsdropfirst2_sdropwhile_adm_h:"chain Y \<Longrightarrow> 
(Abs_tstream (srt\<cdot>(sdropwhile (\<lambda>xa::'a event. xa = \<surd>)\<cdot>(Rep_tstream (\<Squnion>i::nat. Y i))))) =
(\<Squnion>i::nat. (Abs_tstream (srt\<cdot>(sdropwhile (\<lambda>xa::'a event. xa = \<surd>)\<cdot>(Rep_tstream (Y i)))))) "
proof-
  assume a0:"chain Y"
  have h0:"cont(\<lambda>as. (Abs_tstream (srt\<cdot>(sdropwhile (\<lambda>xa::'a event. xa = \<surd>)\<cdot>(Rep_tstream as)))))"
    by (simp add: cont_srt_sdropwhile)
  then show ?thesis
    by (smt a0 cont2contlubE lub_eq)
qed    
  
lemma tsdropfirts2_sdropwhile:"(Abs_tstream (srt\<cdot>(sdropwhile (\<lambda> x. x=\<surd>)\<cdot>(Rep_tstream as)))) = tsDropFirst2\<cdot>as"
  apply(induction as,simp_all)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun tsdropfirst2_sdropwhile_adm_h)
  apply(simp add: tsdropfirst2_delayfun)
  apply (simp add: tsdropwhile2_delayfun delayFun.rep_eq tsconc_rep_eq)
  apply(simp add: tsdropfirst2_mlscons)
  by(simp add: lscons_conv tsmlscons_lscons2)

lemma tsdropfirst2_inftick:"tsAbs\<cdot>as \<noteq> \<bottom> \<Longrightarrow> #\<surd> as = \<infinity> \<Longrightarrow> #\<surd> tsDropFirst2\<cdot>as = \<infinity>"
proof-
  assume a0:"tsAbs\<cdot>as \<noteq> \<bottom>"
  assume a1:"#\<surd> as = \<infinity>"
  have h0:"(Abs_tstream (srt\<cdot>(sdropwhile (\<lambda> x. x=\<surd>)\<cdot>(Rep_tstream as)))) = tsDropFirst2\<cdot>as"
    by (simp add: tsdropfirts2_sdropwhile)
  have h1:"\<exists>n. \<not>((\<lambda> x. x=\<surd>) (snth n (Rep_tstream as)))"
    by (metis (mono_tags, lifting) Rep_tstream_strict a0 ex_snth_in_sfilter_nempty mem_Collect_eq strict_sfilter tsabs_bot tsabs_insert)
  have h2:"#({\<surd>} \<ominus> (Rep_tstream as)) = \<infinity>"
    using a1 tsInfTicks tstreaml1 by blast
  have h3:"#({\<surd>} \<ominus> sdropwhile (\<lambda> x. x=\<surd>)\<cdot>(Rep_tstream as)) = \<infinity>"
    by (simp add: h1 h2 sdropwhile_fair)
  then show ?thesis
    by (metis h0 sfilter_srt_sinf ts_well_def tstickcount_rep_eq)
qed

lemma cont_sdopwhile_tsabs2:"cont(\<lambda>as. (Abs_tstream (sdropwhile f\<cdot>(Rep_tstream as))))"
  by(simp add: ts_well_sdropwhile)    
    
lemma tsdropwhile2_sdropwhile_adm_h:"chain Y \<Longrightarrow> 
(Abs_tstream (sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)\<cdot>(Rep_tstream (\<Squnion>i::nat. Y i)))) =
(\<Squnion>i::nat. (Abs_tstream (sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)\<cdot>(Rep_tstream (Y i))))) "
proof-
  assume a0:"chain Y"
  have h0:"cont(\<lambda>as. (Abs_tstream (sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)\<cdot>(Rep_tstream as))))"
    by (simp add: cont_sdopwhile_tsabs2)
  then show ?thesis
    by (smt a0 cont2contlubE lub_eq)
qed    
    
lemma tsdropwhile2_sdropwhile:"(Abs_tstream (sdropwhile (\<lambda> x. x= Msg a \<or> x=\<surd>)\<cdot>(Rep_tstream as))) = tsDropWhile2\<cdot>(Discr a)\<cdot>as"
  apply(induction as,simp_all)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun tsdropwhile2_sdropwhile_adm_h)
  apply(simp add: tsdropwhile2_delayfun)
  apply (simp add: tsdropwhile2_delayfun delayFun.rep_eq tsconc_rep_eq)
  apply(case_tac "t=a",simp_all)
  apply(simp add: tsdropwhile2_t)
  apply(simp add: lscons_conv tsmlscons_lscons2 )
  apply(simp add: tsdropwhile2_f)
  apply(simp add: lscons_conv tsmlscons_lscons2)
  by (metis (no_types, lifting) lscons_conv tslscons2lscons tsmlscons2tslscons)
 
lemma tsdropwhile2_inftick_h2:"as \<noteq> \<bottom> \<Longrightarrow>
            lshd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(updis a &&\<surd> as))) = updis a \<Longrightarrow>
            \<not> #(srcdups\<cdot>(tsAbs\<cdot>(updis a &&\<surd> as))) \<le> lnsuc\<cdot>0 \<Longrightarrow> {a} \<subset> tsDom\<cdot>(updis a &&\<surd> as)"
  apply(induction as arbitrary: a,simp_all)
  apply(rule adm_imp,simp)
  apply(rule adm_all)
  apply(rule adm_imp,simp)
  apply(rule adm_imp,simp)
  apply(rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (meson lnle_def lub_below monofun_cfun_arg po_class.chain_def)
  apply(rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_eq_Union SUP_subset_mono)
  using UN_iff UN_subset_iff bex_imageD empty_subsetI insert_subset apply fastforce
  apply(simp add: tsabs_mlscons lscons_conv tsdom_mlscons tsdom_delayfun)
  apply(case_tac "as=\<bottom>",simp_all)
  apply(case_tac "t=a",simp_all)
  apply(simp add: tsabs_mlscons lscons_conv tsdom_mlscons)
  apply(simp add: tsabs_mlscons lscons_conv tsdom_mlscons)
  by blast
    
lemma tsdropwhile2_inftick_h:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis a \<Longrightarrow>
        \<not> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> lnsuc\<cdot>0 \<Longrightarrow> {a} \<subset> tsDom\<cdot>as"
  apply(simp add: tsremdups_tsabs)
  apply(induction as ,simp_all)
  apply(rule adm_imp,simp)+
  apply(rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (meson lnle_def lub_below monofun_cfun_arg po_class.chain_def)
  apply(rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_eq_Union SUP_subset_mono)
  using UN_iff UN_subset_iff bex_imageD empty_subsetI insert_subset apply fastforce
  apply(simp add: tsdom_delayfun)
  apply(case_tac "t=a",simp_all)
  apply (simp add: tsdropwhile2_inftick_h2)
  apply(simp add: tsdom_mlscons)
  by (metis lscons_conv lshd_updis srcdups_ex tsabs_mlscons updis_eq)  
    
lemma tsdropwhile2_inftick:"#\<surd> as = \<infinity> \<Longrightarrow>
       tsAbs\<cdot>as \<noteq> \<epsilon> \<Longrightarrow>
       lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
        \<not> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> lnsuc\<cdot>0 \<Longrightarrow>#\<surd>tsDropWhile2\<cdot>(Discr ack)\<cdot>as = \<infinity>"
proof-
  assume a0:"#\<surd> as = \<infinity>"
  assume a1:"\<not> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> lnsuc\<cdot>0"
  assume a2:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack"
  have h0:"(Abs_tstream (sdropwhile (\<lambda> x. x= Msg ack \<or> x=\<surd>)\<cdot>(Rep_tstream as))) = tsDropWhile2\<cdot>(Discr ack)\<cdot>as"
    by (simp add: tsdropwhile2_sdropwhile)
  have h5:"{ack} \<subset> tsDom\<cdot>as"
    using tsdropwhile2_inftick_h a1 a2 by blast
  have h4:" {Msg ack ,\<surd>} \<subset> sdom\<cdot>(Rep_tstream as) "
    by (smt Collect_cong Inf'_neq_0 a0 event.inject event.simps(3) ex_snth_in_sfilter_nempty h5 insert_compr mem_Collect_eq order_less_le psubsetD singletonD slen_empty_eq snth2sdom subsetI tsdom_insert tstickcount_insert)
  have h1:"\<exists>n. \<not>((\<lambda> x. x= Msg ack \<or> x=\<surd>) (snth n (Rep_tstream as)))"
    by (smt Collect_cong h4 insert_compr mem_Collect_eq order.asym psubsetD sdom_def2)
  have h2:"#({\<surd>} \<ominus> (Rep_tstream as)) = \<infinity>"
    using a0 tsInfTicks tstreaml1 by blast
  then show ?thesis
    by (metis (mono_tags, lifting) h0 h1 sdropwhile_fair ts_well_Rep ts_well_sdropwhile tstickcount_rep_eq)
qed
    
lemma tsdropfirst3_le_eq:"#(tsAbs\<cdot>(tsDropFirst3\<cdot>i)) \<le> #(tsAbs\<cdot>i)"
  apply(induction i,simp_all)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (meson lnle_conv lub_mono monofun_cfun_arg po_class.chain_def)  
  apply (simp add: tsdropfirst3_delayfun)
  apply(simp add: tsdropfirst3_mlscons)
  by (metis (no_types, lifting) less_lnsuc lscons_conv slen_scons tsabs_mlscons tsdropfirst3_first tsdropfirst3_mlscons)

  
lemma tssnd_h_tickdrop_h:"i \<noteq> \<bottom> \<Longrightarrow> tsAbs\<cdot>as \<noteq> \<epsilon> \<Longrightarrow>
          srcdups\<cdot>(\<up>(t, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>as\<cdot>(Discr ack))) =
          srcdups\<cdot>(tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>(tsTickDrop\<cdot>as)\<cdot>(Discr ack)))"
proof(induction as arbitrary: i ack)
  case adm
  then show ?case
  by simp
next
  case bottom
  then show ?case
  by simp  
next
  case (delayfun as)
  then show ?case
  by(simp add: tstickdrop_delayfun tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)  
next
  case (mlscons as a)
  then show ?case 
  apply(simp add: tstickdrop_mlscons)
  apply(case_tac "a=ack",simp_all)
  apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv)
  by(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv)
qed
    
lemma tssnd_h_tickdrop:"tsAbs\<cdot>as \<noteq> \<bottom> \<Longrightarrow> (tsAbs\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = tsAbs\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsTickDrop\<cdot>i)\<cdot>(tsTickDrop\<cdot>as)\<cdot>(Discr ack))))"
apply(simp add: tsremdups_tsabs)
proof(induction i arbitrary: as ack)
  case adm
  then show ?case 
  by simp  
next
  case bottom
  then show ?case
  by simp  
next
  case (delayfun i)
  then show ?case 
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun tstickdrop_delayfun)
  apply(case_tac "as=\<bottom>",simp)
  by(simp add: tssnd_h_delayfun_msg tstickdrop_delayfun)
next
  case (mlscons i t)
  then show ?case
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tstickdrop_mlscons tstickdrop_delayfun tssnd_h_delayfun_nack tsabs_mlscons lscons_conv tssnd_h_tickdrop_h)
  apply(case_tac "as=\<bottom>",simp)
  by(simp add: tstickdrop_mlscons)   
qed 
    
lemma tsdropfirst3_le:"(tsAbs\<cdot>i) \<noteq> \<bottom> \<Longrightarrow> lnsuc\<cdot>(#(tsAbs\<cdot>(tsDropFirst3\<cdot>i))) = #(tsAbs\<cdot>i)"
  apply(induction i,simp_all)
  apply(simp add: tsdropfirst3_delayfun)
  apply(simp add: tsdropfirst3_mlscons tsabs_mlscons lscons_conv)
  by (simp add: tsabs_tstickdrop)
 
lemma tstickdrop_nempty:" lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>tsTickDrop\<cdot>as = updis(ack)&&\<surd>tsDropFirst2\<cdot>as" 
  apply(simp add: tsremdups_tsabs tsprojfst_tsabs)
  apply(induction as arbitrary: ack,simp_all)
  apply(simp add: tsdropfirst2_delayfun tstickdrop_delayfun)
  apply(simp add: tsdropfirst2_mlscons tstickdrop_mlscons tsabs_mlscons)
  by (metis stream.sel_rews(4) tsremdups_h_tsabs)    
    
lemma tssnd_h_rt_h3:"lnsuc\<cdot>0 < #(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) \<Longrightarrow> i \<noteq> \<bottom> \<Longrightarrow>
          sprojfst\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>(tsDropWhile2\<cdot>(Discr ack)\<cdot>as)\<cdot>(Discr (\<not> ack))))) =
          sprojfst\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>as\<cdot>(Discr (\<not> ack)))))"
proof(induction as arbitrary: i ack)
  case adm
  then show ?case 
  apply(rule adm_all)+
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (metis (no_types, lifting) leD lnle_def lub_below monofun_cfun_arg not_less po_class.chain_def)
  by simp   
next
  case bottom
  then show ?case 
  by simp
next
  case (delayfun as)
  then show ?case
  by(simp add: tsdropwhile2_delayfun tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
next
  case (mlscons as a)
  then show ?case 
  apply(case_tac "a=ack",simp_all)
  apply(simp add: tsdropwhile2_t tssnd_h_mlscons_nack tsabs_mlscons lscons_conv)
  by(simp add: tssnd_h_mlscons_ack tsdropwhile2_f tsabs_mlscons lscons_conv)    
qed
  
lemma tssnd_h_rt_h2:"lnsuc\<cdot>0 < #(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) \<Longrightarrow>
    sprojfst\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(tsSnd_h\<cdot>(tsTickDrop\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr ack)\<cdot>as)\<cdot>(Discr (\<not> ack))))) =
    srt\<cdot>(sprojfst\<cdot>(srcdups\<cdot>(\<up>(t, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack))))))"
proof(induction i arbitrary: as ack)
  case adm
  then show ?case 
  apply(rule adm_all)+
  apply(rule adm_imp,simp)+
  by simp   
next
  case bottom
  then show ?case
  by simp  
next
  case (delayfun i)
  then show ?case
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun tsdropwhile2_delayfun tstickdrop_delayfun)
  apply(case_tac "as=\<bottom>",simp)
  by(simp add: tssnd_h_delayfun_msg tstickdrop_delayfun)
next
  case (mlscons i t)
  then show ?case
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tstickdrop_mlscons tsdropwhile2_delayfun tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  using tssnd_h_rt_h3 apply blast 
  apply(case_tac "as=\<bottom>",simp)
  apply(case_tac "a=ack",simp_all)
  apply(simp add: tstickdrop_mlscons tsdropwhile2_t tssnd_h_mlscons_nack tsabs_mlscons lscons_conv)
  using tssnd_h_rt_h3 apply blast 
  by(simp add: tstickdrop_mlscons tsdropwhile2_f tssnd_h_mlscons_ack tsabs_mlscons lscons_conv)   
qed
  
lemma tssnd_h_rt_h1:"lnsuc\<cdot>0 < #(srcdups\<cdot>(tsAbs\<cdot>as)) \<Longrightarrow> lshd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>as)) = updis ack \<Longrightarrow>
          sprojfst\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(tsSnd_h\<cdot>(tsTickDrop\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr ack)\<cdot>as)\<cdot>(Discr (\<not> ack))))) =
          srt\<cdot>(sprojfst\<cdot>(srcdups\<cdot>(\<up>(t, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>as\<cdot>(Discr ack)))))"
proof(induction as arbitrary: i ack)
  case adm
  then show ?case
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (metis (no_types, lifting) leD lnle_def lub_below monofun_cfun_arg not_less po_class.chain_def)
  apply(rule adm_all)+
  apply(rule adm_imp,simp)+
  by simp    
next
  case bottom
  then show ?case
  by simp
next
  case (delayfun as)
  then show ?case
  apply(rule_tac ts=i in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv tsdropwhile2_delayfun)
  apply(rename_tac i)
  apply(case_tac "i=\<bottom>",simp)
  by(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv tsdropwhile2_delayfun)
next
  case (mlscons as t)
  then show ?case
  apply(case_tac "t=ack",simp_all)
  apply(case_tac "i=\<bottom>",simp)
  apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv tsdropwhile2_t)
  using tssnd_h_rt_h2 apply blast
  apply(simp add: tsabs_mlscons lscons_conv)
  by (metis lshd_updis srcdups_ex updis_eq)    
qed

lemma tssnd_h_rt:"#(tsAbs\<cdot>(tsRemDups\<cdot>as)) > lnsuc\<cdot>0 \<Longrightarrow> lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow> (tsAbs\<cdot>i) \<noteq> \<bottom> \<Longrightarrow>tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(ack))\<cdot>as)\<cdot>(Discr (\<not> ack))))) = srt\<cdot>(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))"
apply(simp add: tsremdups_tsabs tsprojfst_tsabs)
proof(induction i arbitrary: as ack)
  case adm
  then show ?case 
  apply(rule adm_all)+
  apply(rule adm_imp,simp)+
  by simp  
next
  case bottom
  then show ?case 
  by simp
next
  case (delayfun i)
  then show ?case 
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tsdropwhile2_delayfun tsdropfirst3_delayfun)   
  apply(simp add: tssnd_h_delayfun)
  apply(case_tac "as=\<bottom>",simp)
  apply(case_tac "a=ack",simp_all)
  apply(simp add: tsdropfirst3_delayfun tssnd_h_delayfun_msg)
  apply(simp add: tsabs_mlscons lscons_conv)
  by(metis lshd_updis srcdups_ex updis_eq)    
next
  case (mlscons i t)
  then show ?case 
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tsdropfirst3_mlscons tsdropwhile2_delayfun tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  using tssnd_h_rt_h1 apply blast
  apply(case_tac "as=\<bottom>",simp)
  apply(case_tac "a=ack",simp_all)
  apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv tsdropfirst3_mlscons tsdropwhile2_t)
  using tssnd_h_rt_h2 apply blast
  apply(simp add: tsabs_mlscons lscons_conv)
  by (metis lshd_updis srcdups_ex updis_eq)
qed  
  
lemma tssnd_h_hd:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow> (tsAbs\<cdot>i) \<noteq> \<bottom> \<Longrightarrow> slookahd\<cdot>(tsAbs\<cdot>i)\<cdot>(\<lambda> a. \<up>a) = slookahd\<cdot>(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))\<cdot>(\<lambda> a. \<up>a)"
apply(simp only: tsremdups_tsabs tsprojfst_tsabs)
proof(induction i arbitrary: as ack)
  case adm
  then show ?case 
  apply(rule adm_all)+
  apply(rule adm_imp,simp)+
  by simp
next
  case bottom
  then show ?case 
  by simp
next
  case (delayfun i)
  then show ?case 
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun)
  apply(case_tac "as=\<bottom>",simp)    
  by(simp add: tssnd_h_delayfun_msg)    
next
  case (mlscons i t)
  then show ?case
  apply(simp add: tsabs_mlscons lscons_conv)
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  apply (metis (no_types, lifting) lscons_conv shd1 slookahd_scons sprojfst_scons srcdups_ex stream.con_rews(2) up_defined)    
  apply(case_tac "as=\<bottom>",simp)
  apply(case_tac "a=ack",simp_all)
  apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv)    
  apply (metis (no_types, lifting) lscons_conv shd1 slookahd_scons sprojfst_scons srcdups_ex stream.con_rews(2) up_defined)    
  apply(simp add: tsabs_mlscons lscons_conv)
  by (metis lshd_updis srcdups_ex updis_eq)    
qed
  
lemma tssnd_h_shd_i:" #(tsAbs\<cdot>(tsRemDups\<cdot>as)) > lnsuc\<cdot>0 \<Longrightarrow> lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow> (tsAbs\<cdot>i) \<noteq> \<bottom> \<Longrightarrow> \<up>(shd(tsAbs\<cdot>i)) \<bullet> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)\<cdot>(Discr (\<not> ack))))) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))"   
proof -
  assume a1: "tsAbs\<cdot>i \<noteq> \<epsilon>"
  assume a2: "lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack"
  assume a3: "lnsuc\<cdot>0 < #(tsAbs\<cdot>(tsRemDups\<cdot>as))"
  have f4: "tsAbs\<cdot>(tsRemDups\<cdot>as) \<noteq> \<epsilon>"
    using a2 by auto
  then have f5: "Discr (shd (tsAbs\<cdot>(tsRemDups\<cdot>as))) = Discr ack"
    using a2 by (metis (no_types) lshd_updis surj_scons up_eq)
  have "#(tsAbs\<cdot>i) \<noteq> 0"
    using a1 by (meson slen_empty_eq)
  then have "tsAbs\<cdot> (tsProjFst\<cdot> (tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) \<noteq> \<epsilon>"
    using f4 by (metis lnzero_def slen_empty_eq tsprojfst_tsabs_slen tssnd_h_tsabs_nbot)
  then show ?thesis
    using f5 a3 a2 a1 by (metis (no_types) below_shd surj_scons tssnd_h_rt tssnd_prefix_inp)
qed 

lemma tssnd_h_nack_msg:"tsDom\<cdot>as \<subseteq> {ack} \<Longrightarrow> sprojfst\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>as\<cdot>(Discr (\<not> ack))))) = \<up>(t)" 
proof(induction as arbitrary: i ack)
  case adm
  then show ?case 
  apply(rule adm_all)+
  apply(rule adm_imp,simp)
  by simp
next
  case bottom
  then show ?case 
  by simp  
next
  case (delayfun as)
  then show ?case
  apply(case_tac "i=\<bottom>",simp)
  by(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv tsdom_delayfun)
next
  case (mlscons as a)
  then show ?case
  apply(case_tac "i=\<bottom>",simp)
  apply(case_tac "a=ack",simp_all)
  apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv tsdom_mlscons)
  by(simp add: tsdom_mlscons)
qed
  
lemma tssnd_h_acknack_h3:"#\<surd>as = \<infinity> \<Longrightarrow>
          #(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) = lnsuc\<cdot>0 \<Longrightarrow>
          i \<noteq> \<bottom> \<Longrightarrow> as \<noteq> \<bottom> \<Longrightarrow> \<up>t \<bullet> sprojfst\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>as\<cdot>(Discr (\<not> ack))))) = \<up>t \<bullet> \<up>t"
proof-
  assume a0:"#(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) = lnsuc\<cdot>0"
  have h0:"#(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) = lnsuc\<cdot>0 \<Longrightarrow> tsDom\<cdot>as \<subseteq> {ack}"
    apply(induction as,simp_all)
    apply(rule adm_imp)
    apply(rule admI)
    apply(simp add: contlub_cfun_arg contlub_cfun_fun)
    apply (smt Inf'_neq_0 fold_inf lnat.injects lnzero_def lub_eqI lub_finch2 monofun_cfun_arg po_class.chain_def unique_inf_lub)
    apply simp
    apply(simp add: tsdom_delayfun)
    apply(case_tac "t=ack",simp_all)
    apply(simp add: tsdom_mlscons tsabs_mlscons lscons_conv)
    apply(simp add: tsabs_mlscons lscons_conv)
    by (simp add: srcdups_nbot) 
  then show ?thesis
    by (simp add: a0 tssnd_h_nack_msg)
qed  
      
lemma tssnd_h_acknack_h2:"#\<surd> as = \<infinity> \<Longrightarrow>#(tsAbs\<cdot>(tsRemDups\<cdot>(updis( ack)&&\<surd>as))) < #(tsAbs\<cdot>(updis(t)&&\<surd>i)) \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(updis( ack)&&\<surd>as))) = lnsuc\<cdot>0 \<Longrightarrow> 
tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(updis(t)&&\<surd>i)\<cdot>(updis( ack)&&\<surd>as)\<cdot>(Discr ack)))) = stake (Suc (Suc 0))\<cdot>(tsAbs\<cdot>(updis(t)&&\<surd>i))"
  apply(simp add: tsremdups_tsabs tsprojfst_tsabs)
  apply(case_tac "i=\<bottom>",simp)
  apply(case_tac "as=\<bottom>",simp)
  apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv tstickcount_mlscons)
proof(induction i arbitrary: as ack)
  case adm
  then show ?case 
  apply(rule adm_all)
  apply(rule adm_imp,simp)+
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (metis (no_types, lifting) below_bottom_iff lnat.exhaust lub_eq_bottom_iff po_class.chain_def)
  apply(rule adm_all)
  apply(rule adm_imp,simp)+
  by simp
next
  case bottom
  then show ?case
  by simp  
next
  case (delayfun i)
  then show ?case 
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun)
  apply(case_tac "i=\<bottom>",simp)
  apply(case_tac "as=\<bottom>",simp)
  apply(simp add: delayFun_def)
  apply(simp add: delayFun_def)
  apply(case_tac "i=\<bottom>",simp)
  apply(case_tac "as=\<bottom>",simp)
  by(simp add: tssnd_h_delayfun_msg)
next
  case (mlscons i t)
  then show ?case 
  apply(rule_tac ts=as in tscases,simp_all)
  apply(case_tac "as=\<bottom>",simp)
  apply(simp add: delayFun_def)
  apply(simp add: tsabs_mlscons lscons_conv tssnd_h_delayfun_nack)
  apply(simp add: delayFun_def)
  apply (metis inject_scons tssnd_h_acknack_h3)  
  apply(case_tac "a= ack",simp_all)
  apply(case_tac "as=\<bottom>",simp)
  apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv tstickcount_mlscons)
  apply (metis inject_scons tssnd_h_acknack_h3)    
  apply(simp add: tsabs_mlscons lscons_conv)
  by (smt lnat.con_rews lnat.sel_rews(2) lnzero_def lscons_conv slen_empty_eq slen_scons srcdups_nbot srcdups_neq tsabs_mlscons tsmlscons_nbot_rev)
qed
    
lemma tssnd_h_acknack_h:"#\<surd> as = \<infinity> \<Longrightarrow> #(srcdups\<cdot>(tsAbs\<cdot>as)) = lnsuc\<cdot>0 \<Longrightarrow> i \<noteq> \<bottom> \<Longrightarrow> lnsuc\<cdot>0 < #(tsAbs\<cdot>(updis t &&\<surd> i)) \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>(updis(t)&&\<surd>i)) \<Longrightarrow>lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack\<Longrightarrow>
          sprojfst\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>(tsTickDrop\<cdot>as)\<cdot>(Discr ack)))) =
          stake (Suc (Suc 0))\<cdot>(tsAbs\<cdot>(updis t &&\<surd> i))"
proof-
  assume a0:"#\<surd> as = \<infinity> "
  assume a1:"#(srcdups\<cdot>(tsAbs\<cdot>as)) = lnsuc\<cdot>0 "
  assume a2:"lnsuc\<cdot>0 < #(tsAbs\<cdot>(updis t &&\<surd> i))"
  assume a3:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack"
  have h0:"tsAbs\<cdot>as \<noteq> \<bottom>"
    using a1 by auto
  have h1:"#(srcdups\<cdot>(tsAbs\<cdot>(tsTickDrop\<cdot>as))) = lnsuc\<cdot>0"
    by (simp add: a1 tsabs_tstickdrop)
  have h2:"#(tsAbs\<cdot>(tsRemDups\<cdot>(tsTickDrop\<cdot>as))) < #(tsAbs\<cdot>(updis(t)&&\<surd>i))"
    by (simp add: a2 h1 tsremdups_tsabs)
  have h3:"#\<surd> tsDropFirst2\<cdot>as = \<infinity>"
    using a0 h0 tsdropfirst2_inftick by auto
  have h5:"#\<surd> tsDropFirst2\<cdot>as = \<infinity> \<Longrightarrow>#(tsAbs\<cdot>(tsRemDups\<cdot>(updis(ack)&&\<surd>tsDropFirst2\<cdot>as))) < #(tsAbs\<cdot>(updis(t)&&\<surd>i)) \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(updis(ack)&&\<surd>tsDropFirst2\<cdot>as))) = lnsuc\<cdot>0 \<Longrightarrow> 
  tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(updis(t)&&\<surd>i)\<cdot>(updis(ack)&&\<surd>tsDropFirst2\<cdot>as)\<cdot>(Discr ack)))) = stake (Suc (Suc 0))\<cdot>(tsAbs\<cdot>(updis(t)&&\<surd>i))"
    using tssnd_h_acknack_h2 by blast
  then show ?thesis
    by (metis (no_types, lifting) a2 a3 h1 h3 tsprojfst_tsabs tsremdups_tsabs tstickdrop_nempty)
qed
    
lemma tssnd_h_acknack:"#\<surd>as = \<infinity> \<Longrightarrow>#(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>i) \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = lnsuc\<cdot>0 \<Longrightarrow>lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack\<Longrightarrow> 
tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsTickDrop\<cdot>i)\<cdot>(tsTickDrop\<cdot>as)\<cdot>(Discr ack)))) = stake (Suc (Suc 0))\<cdot>(tsAbs\<cdot>i)"
  apply(simp add: tsremdups_tsabs tsprojfst_tsabs)
proof(induction i arbitrary: as ack)
  case adm
  then show ?case
  apply(rule adm_all)
  apply(rule adm_imp,simp)+
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (metis (no_types, lifting) lnle_conv lub_below monofun_cfun_arg not_less po_class.chain_def)
  apply(rule adm_imp,simp)
  apply(rule adm_all)
  apply(rule adm_imp,simp)
  by simp
next
  case bottom
  then show ?case
  by simp
next
  case (delayfun i)
  then show ?case 
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tstickdrop_delayfun)
  apply(simp add: delayFun_def)
  by(simp add: tstickdrop_delayfun)
next
  case (mlscons i t)
  then show ?case 
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tstickdrop_mlscons tstickdrop_delayfun)
  apply (simp add: tsremdups_tsabs tssnd_h_acknack_h tstickcount_delayfun)
  apply(case_tac "a=ack",simp_all)
  apply(case_tac "as=\<bottom>",simp_all)
  apply(simp add: tstickdrop_mlscons)
  apply (metis (no_types, lifting) tsremdups_tsabs tssnd_h_acknack_h tstickdrop_mlscons)
  apply(simp add: tsabs_mlscons lscons_conv)
  by (simp add: lscons_conv tsabs_mlscons tsremdups_tsabs tssnd_h_acknack_h tstickdrop_mlscons)
qed
  
lemma tssnd_ack2trans_51_h3:"\<not> #(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) \<le> lnsuc\<cdot>0 \<Longrightarrow>
            lshd\<cdot>(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) = updis ack \<Longrightarrow>
            lshd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(tsDropWhile2\<cdot>(Discr ack)\<cdot>as))) = updis (\<not> ack)"
  apply(induction as,simp_all)
  apply(rule adm_imp,simp)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (meson lnle_def lub_below monofun_cfun_arg po_class.chain_def)
  apply(rule adm_imp,simp)
  apply simp
  apply(simp add: tsdropwhile2_delayfun)
  apply(case_tac "t=ack",simp_all)
  apply(simp add: tsabs_mlscons lscons_conv tsdropwhile2_t)
  apply(simp add: tsabs_mlscons lscons_conv tsdropwhile2_f)
  by (metis lshd_updis srcdups_ex)
    
lemma tssnd_ack2trans_51_h2:"as \<noteq> \<bottom> \<Longrightarrow>
            lshd\<cdot>(srcdups\<cdot>(tsAbs\<cdot>(updis ack &&\<surd> as))) = updis ack \<Longrightarrow>
            #(srcdups\<cdot>(tsAbs\<cdot>(updis ack &&\<surd> as))) = Fin k \<Longrightarrow> lnsuc\<cdot>(#(srcdups\<cdot>(tsAbs\<cdot>(tsDropWhile2\<cdot>(Discr ack)\<cdot>as)))) = Fin k"
  apply(induction as,simp_all)
  apply(rule adm_imp,simp)+
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (metis (no_types, lifting) Fin_neq_inf l42 monofun_cfun_arg po_class.chain_def unique_inf_lub)
  apply simp
  apply(simp add: tsabs_mlscons tsdropwhile2_delayfun)
  apply(case_tac "as=\<bottom>",simp_all)
  apply(simp add: lscons_conv)
  apply auto[1]
  apply(case_tac "t=ack",simp_all)
  apply(simp add: tsabs_mlscons lscons_conv tsdropwhile2_t)
  by(simp add: tsabs_mlscons lscons_conv tsdropwhile2_f)
  
lemma tssnd_ack2trans_51_h1:" #\<surd> as = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = lnsuc\<cdot>0 \<Longrightarrow> lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>  #(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>i) \<Longrightarrow> 
            tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = stake (Suc (Suc 0))\<cdot>(tsAbs\<cdot>i)"
proof-
  assume a0:"#\<surd> as = \<infinity>"
  assume a1:"#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = lnsuc\<cdot>0"
  assume a3:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack"
  assume a4:"#(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>i)"
  then show ?thesis
    by (smt Fin_02bot Zero_lnless_infty a0 a1 a3 empty_is_shortest le2lnle lnzero_def only_empty_has_length_0 tsprojfst_tsabs tsremdups_tsabs_slen tssnd_h_acknack tssnd_h_tickdrop)
qed     

lemma tssnd_ack2trans_51:"(\<And>(i::'a tstream) as ack.
           lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) = Fin k \<Longrightarrow>
           #\<surd> as = \<infinity> \<Longrightarrow>
           tsAbs\<cdot>as \<noteq> \<epsilon> \<Longrightarrow>
           lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
           #(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>i) \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = stake k\<cdot>(tsAbs\<cdot>i)) \<Longrightarrow>
       lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) = Fin (Suc k) \<Longrightarrow>
       #\<surd> as = \<infinity> \<Longrightarrow>
       tsAbs\<cdot>as \<noteq> \<epsilon> \<Longrightarrow>
       lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
       #(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>(i::'a tstream)) \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = stake (Suc k)\<cdot>(tsAbs\<cdot>i)"
proof(case_tac"#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> (lnsuc\<cdot>0)")
  assume a0:"(\<And>(i::'a tstream) as ack.
           lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) = Fin k \<Longrightarrow>
           #\<surd> as = \<infinity> \<Longrightarrow> (tsAbs\<cdot>as) \<noteq> \<bottom> \<Longrightarrow>
           lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow> 
           #(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>i) \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = stake k\<cdot>(tsAbs\<cdot>i))"
  assume a1:"lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) = Fin (Suc k)"
  assume a2:" #\<surd> as = \<infinity> "
  assume a3:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack"
  assume a4:"(tsAbs\<cdot>as) \<noteq> \<bottom>"
  assume a5:"#(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>i)"
  assume a6:" #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> lnsuc\<cdot>0"
  have h0:"#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = lnsuc\<cdot>0"
    by (metis Fin_02bot Fin_Suc a3 a6 less2eq less2lnleD lnzero_def not_le_zero_eq slen_empty_eq stream.sel_rews(3) up_defined)
  have h1:"k = Suc 0"
    by (metis Fin_0 Fin_Suc a1 h0 lessI less_Suc_eq_0_disj lnat.injects lnsuc_neq_0_rev)
  then show ?thesis
    using a2 a3 a5 h0 tssnd_ack2trans_51_h1 by blast
next
  assume a0:"(\<And>(i::'a tstream) as ack.
           lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) = Fin k \<Longrightarrow>
           #\<surd> as = \<infinity> \<Longrightarrow> (tsAbs\<cdot>as) \<noteq> \<bottom> \<Longrightarrow>
           lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow> 
           #(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>i) \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = stake k\<cdot>(tsAbs\<cdot>i))"
  assume a1:"lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) = Fin (Suc k)"
  assume a2:" #\<surd> as = \<infinity> "
  assume a3:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack"
  assume a4:"(tsAbs\<cdot>as) \<noteq> \<bottom>"
  assume a5:"#(tsAbs\<cdot>(tsRemDups\<cdot>as)) < #(tsAbs\<cdot>i)"
  assume a6:"\<not> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> lnsuc\<cdot>0"
  have h01:"(\<And>(i::'a tstream) ack.
           lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)))) = Fin k \<Longrightarrow>
           #\<surd> (tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as) = \<infinity> \<Longrightarrow> (tsAbs\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)) \<noteq> \<bottom> \<Longrightarrow>
           lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) = updis ack \<Longrightarrow> 
           #(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) < #(tsAbs\<cdot>i) \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)\<cdot>(Discr ack)))) = stake k\<cdot>(tsAbs\<cdot>i))"
    by (insert a0 [of "(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)"], auto)
  have h0:"
           lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)))) = Fin k \<Longrightarrow>
           #\<surd> (tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as) = \<infinity> \<Longrightarrow> (tsAbs\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)) \<noteq> \<bottom> \<Longrightarrow>
           lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) = updis ack \<Longrightarrow> 
           #(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) < #(tsAbs\<cdot>(tsDropFirst3\<cdot>(i::'a tstream))) \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)\<cdot>(Discr ack)))) = stake k\<cdot>(tsAbs\<cdot>(tsDropFirst3\<cdot>i))"
    by (insert h01 [of "ack"], auto)
  have f4: "tsAbs\<cdot>(tsRemDups\<cdot>as) \<noteq> \<epsilon>"
    using a3 by auto
  then have f5: "Discr (shd (tsAbs\<cdot>(tsRemDups\<cdot>as))) = Discr ack"
    using a3 by (metis (no_types) lshd_updis surj_scons up_eq)
  have f7:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) = Fin (Suc k) \<Longrightarrow> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr ack)\<cdot>as)))) = Fin k"
    apply(simp add: tsremdups_tsabs)
    apply(induction as,simp_all)
    apply(rule adm_imp,simp)
    apply(rule adm_imp)
    apply(rule admI)
    apply(simp add: contlub_cfun_arg contlub_cfun_fun)
    apply (metis (no_types, lifting) Fin_neq_inf l42 monofun_cfun_arg po_class.chain_def unique_inf_lub)
    apply simp
    apply(simp add: tsdropwhile2_delayfun)
    apply(case_tac "t=ack",simp_all)
    apply(simp add: tsdropwhile2_t)
    using tssnd_ack2trans_51_h2 apply blast
    apply(simp add: tsabs_mlscons lscons_conv)
    by (metis lshd_updis srcdups_ex updis_eq)
  have h1:"lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)))) = Fin k"
    by (simp add: a1 a3 f5 f7)
  have h2:"\<not> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> lnsuc\<cdot>0 \<Longrightarrow> lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(ack))\<cdot>as))) = updis (\<not>ack)"
    apply(simp add: tsremdups_tsabs)
    apply(induction as,simp_all)
    apply(rule adm_imp,simp)
    apply(rule admI)
    apply(simp add: contlub_cfun_arg contlub_cfun_fun)
    apply (meson lnle_def lub_below monofun_cfun_arg po_class.chain_def)
    apply(rule adm_imp,simp)
    apply simp
    apply(simp add: tsdropwhile2_delayfun)
    apply(case_tac "t=ack",simp_all)
    apply(simp add: tsdropwhile2_t tsabs_mlscons lscons_conv)
    using tssnd_ack2trans_51_h3 apply blast
    apply(simp add: tsabs_mlscons lscons_conv)
    by (metis lshd_updis srcdups_ex updis_eq)  
  have h3:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) = updis (\<not>ack)"
    using a3 a6 f5 local.h2 by blast
  have h4:"#(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) < #(tsAbs\<cdot>(tsDropFirst3\<cdot>i))"
    by (smt a1 a3 a5 dual_order.strict_iff_order empty_is_shortest f5 f7 le_less_trans less_lnsuc lnat.injects lnle2le tsdropfirst3_le tsdropwhile2_le2)
  have h5:"tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)\<cdot>(Discr (\<not> ack))))) = stake k\<cdot>(tsAbs\<cdot>(tsDropFirst3\<cdot>i))"
    by (metis (mono_tags, lifting) a0 a2 a3 a6 f5 h1 h3 h4 stream.sel_rews(1) strict_srcdups tsdropwhile2_inftick tsremdups_tsabs up_defined)
  have h6:"\<up>(shd(tsAbs\<cdot>i)) \<bullet> stake k\<cdot>(tsAbs\<cdot>(tsDropFirst3\<cdot>i)) = stake (Suc k)\<cdot>(tsAbs\<cdot>i)"
    apply(rule_tac x="(tsAbs\<cdot>i)" in scases,simp_all)
    using a5 not_le_zero_eq order.asym apply fastforce
    by(simp add: tsdropfirst3_first)
  then show ?thesis
    by (metis a3 a5 a6 h5 leI not_le_zero_eq only_empty_has_length_0 order.asym slen_empty_eq tssnd_h_shd_i)
qed
  
lemma tssnd_ack2trans_5:"lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) = Fin k \<Longrightarrow> #\<surd>as = \<infinity> \<Longrightarrow> (tsAbs\<cdot>as) \<noteq> \<bottom> \<Longrightarrow> lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow> #(tsAbs\<cdot>(i::'a tstream)) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> 
   (tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))) = stake k\<cdot>((tsAbs\<cdot>(i)))"
  apply(induction k arbitrary: i as ack)
  apply simp
  using tssnd_ack2trans_51 by blast

lemma stake_slen_h:"(\<And>i::'a stream. Fin k < #i \<Longrightarrow> #(stake k\<cdot>i) = Fin k) \<Longrightarrow> Fin (Suc k) < #(i::'a stream) \<Longrightarrow> #(stake (Suc k)\<cdot>i) = Fin (Suc k)"    
proof-
  assume a0:"\<And>(i::'a stream). Fin k < #i \<Longrightarrow> #(stake k\<cdot>i) = Fin k"
  assume a2:"Fin (Suc k) < #i"
  have h0:" Fin k < # (srt\<cdot>i) \<Longrightarrow> #(stake k\<cdot>(srt\<cdot>i)) = Fin k"
    by (insert a0 [of "(srt\<cdot>i)"], auto)
  have h1:"Fin k < # (srt\<cdot>i)"
    by (meson a2 leD leI slen_rt_ile_eq)
  then show ?thesis
    by (metis Fin_Suc a2 empty_is_shortest h0 slen_scons stake_Suc surj_scons)
qed
  
lemma stake_slen:"#i > Fin k \<Longrightarrow>  #(stake k\<cdot>i) = Fin k "
  apply(induction k arbitrary: i,simp_all)
  using stake_slen_h by blast
    
lemma tssnd_h_inf_h2:"(\<And>(i::'a tstream) as ack.
           lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
           #(tsAbs\<cdot>i) = \<infinity> \<Longrightarrow>
           #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<Longrightarrow>
           #(stake k\<cdot>(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))) < #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))) \<Longrightarrow>
       lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
       #(tsAbs\<cdot>(i::'a tstream)) = \<infinity> \<Longrightarrow>
       #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<Longrightarrow>
       #(stake (Suc k)\<cdot>(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))) < #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))"
proof-
  assume a0:"(\<And>(i::'a tstream) as ack.
           lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
           #(tsAbs\<cdot>i) = \<infinity> \<Longrightarrow>
           #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<Longrightarrow>
           #(stake k\<cdot>(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))) < #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))))"
  assume a1:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack"
  assume a2:"#(tsAbs\<cdot>i) = \<infinity>"
  assume a3:"#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity>"
  have h0:"#(tsAbs\<cdot>(tsRemDups\<cdot>as)) > lnsuc\<cdot>0"
    by (simp add: a3 not_le_imp_less)
  have h1:"(tsAbs\<cdot>i) \<noteq> \<bottom>"
    using a2 by auto
  then have f5: "Discr (shd (tsAbs\<cdot>(tsRemDups\<cdot>as))) = Discr ack"
    by (metis Inf'_neq_0_rev a1 a3 lshd_updis slen_empty_eq surj_scons updis_eq)
  have h21:"(lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) = updis ack \<Longrightarrow>
           #(tsAbs\<cdot>(tsDropFirst3\<cdot>(i::'a tstream))) = \<infinity> \<Longrightarrow>
           #(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) = \<infinity> \<Longrightarrow>
           #(stake k\<cdot>(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)\<cdot>(Discr ack)))))) < #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)\<cdot>(Discr ack))))))"
    by (insert a0 [of "(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)"], auto)
  have h22:"\<not> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> lnsuc\<cdot>0 \<Longrightarrow> lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(ack))\<cdot>as))) = updis (\<not>ack)"
    apply(simp add: tsremdups_tsabs)
    apply(induction as,simp_all)
    apply(rule adm_imp,simp)
    apply(rule admI)
    apply(simp add: contlub_cfun_arg contlub_cfun_fun)
    apply (meson lnle_def lub_below monofun_cfun_arg po_class.chain_def)
    apply(rule adm_imp,simp)
    apply simp
    apply(simp add: tsdropwhile2_delayfun)
    apply(case_tac "t=ack",simp_all)
    apply(simp add: tsdropwhile2_t tsabs_mlscons lscons_conv)
    using tssnd_ack2trans_51_h3 apply blast
    apply(simp add: tsabs_mlscons lscons_conv)
    by (metis lshd_updis srcdups_ex updis_eq)
  have h23:"#(tsAbs\<cdot>(tsDropFirst3\<cdot>i)) = \<infinity>"
    using a2 h1 tsdropfirst3_le by fastforce
  have h24:"#(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) = \<infinity>"
    using a1 a3 f5 tsdropwhile2_le2 by fastforce
  have h2:"#(stake k\<cdot>(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(ack))\<cdot>as)\<cdot>(Discr (\<not> ack))))))) < #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(ack))\<cdot>as)\<cdot>(Discr (\<not> ack))))))"
    using a0 a1 f5 h0 h22 h23 h24 leD by blast
  have h3:"\<up>(shd(tsAbs\<cdot>i)) \<bullet> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)\<cdot>(Discr (\<not> ack))))) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))"
    by (simp add: a1 h0 h1 tssnd_h_shd_i)
  have h4:"stake (Suc k)\<cdot>(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))) = \<up>(shd(tsAbs\<cdot>i)) \<bullet> (stake k\<cdot>(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(ack))\<cdot>as)\<cdot>(Discr (\<not> ack))))))) "
  proof -
    have "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) \<noteq> \<epsilon>"
      using h3 by force
    then show ?thesis
      by (metis (no_types) a1 h0 h1 h3 shd1 stake_Suc surj_scons tssnd_h_rt)
  qed
  have h5:"lnsuc\<cdot>(#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)\<cdot>(Discr (\<not> ack))))))) = #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))"
    by (metis h3 slen_scons)
  then show ?thesis
  proof -
    have "\<not> #(tsAbs\<cdot> (tsProjFst\<cdot> (tsRemDups\<cdot> (tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot> (tsDropWhile2\<cdot>(Discr ack)\<cdot>as)\<cdot> (Discr (\<not> ack)))))) < #(stake k\<cdot> (tsAbs\<cdot> (tsProjFst\<cdot> (tsRemDups\<cdot> (tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot> (tsDropWhile2\<cdot>(Discr ack)\<cdot>as)\<cdot> (Discr (\<not> ack)))))))"
      by (meson h2 less_asym')
    then show ?thesis
      by (metis (no_types) f5 h2 h4 h5 leI le_imp_less_or_eq lnsuc_lnle_emb neq_iff slen_scons)
  qed
qed
    
lemma tssnd_h_inf_h:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow> #(tsAbs\<cdot>i) = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))) > #(stake k\<cdot>(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))))"    
  apply(induction k arbitrary: i as ack)
  apply (smt Fin_02bot Fin_Suc Zero_lnless_infty fold_inf gr_0 less2lnleD lnat.sel_rews(2) lnzero_def order_less_le slen_empty_eq slen_scons stake_slen tssnd_h_shd_i)
  using tssnd_h_inf_h2 by blast
    
lemma tssnd_h_inf:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow> #(tsAbs\<cdot>i) = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = \<infinity>"
  by (metis stake2inf tsprojfst_tsabs_slen tssnd_h_inf_h)
  
lemma tssnd_ack2trans_4:"#\<surd> as = \<infinity> \<Longrightarrow>
    lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
     #(tsAbs\<cdot>i) \<ge> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow>
    #(tsAbs\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
  apply(case_tac"#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity>")
  apply (simp add: tssnd_h_inf)
  apply(case_tac "(tsAbs\<cdot>as) = \<bottom>")
  apply (metis leD not_le_zero_eq slen_empty_eq stream.sel_rews(3) tsremdups_tsabs_slen up_defined)
proof-
  assume a0:"#\<surd> as = \<infinity>"
  assume a1:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack"
  assume a2:"lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<le> #(tsAbs\<cdot>i)"
  assume a3:"#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<noteq> \<infinity>"
  assume a4:"tsAbs\<cdot>as \<noteq> \<epsilon>"
  have h0:"\<exists>k. lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) = Fin k"
    by (metis a3 fold_inf inf_ub le_neq_trans lnat.injects lnat_well_h2)
  then show ?thesis
    by (smt a0 a1 a2 a3 a4 fin2stake h0 inf_ub le2lnle order.not_eq_order_implies_strict stake_slen tsprojfst_tsabs_slen tssnd_ack2trans_5)    
qed
  
lemma tssnd_ack2trans_3:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
    (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))) > #(tsAbs\<cdot>i) \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = #(tsAbs\<cdot>i)"
  sorry
  
lemma tssnd_ack2trans_2:"#\<surd>as = \<infinity> \<Longrightarrow>  lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))
     = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
  apply(case_tac  "(lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))) > #(tsAbs\<cdot>i)",simp_all)
  apply(simp add: tssnd_ack2trans_3)
  apply (simp add: min.strict_order_iff)
  by (simp add: tssnd_ack2trans_4 min_absorb2)

lemma snd7:"tsAbs\<cdot>as = \<epsilon> \<Longrightarrow>
          i \<noteq> \<bottom> \<Longrightarrow> (srcdups\<cdot>(\<up>(t, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>as\<cdot>(Discr ack)))) = \<up>(t, ack) "
proof(induction as arbitrary: t ack i)
  case adm
  then show ?case 
  apply(rule adm_imp,simp)
  apply(rule adm_all)+
  apply(rule adm_imp,simp)
  by simp
next
  case bottom
  then show ?case 
  by simp  
next
  case (delayfun as)
  then show ?case
  by (simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)  
next
  case (mlscons as ta)
  then show ?case 
  apply(case_tac "as=\<bottom>",simp_all)
  using tsabs_mlscons by fastforce
qed    
    
lemma snd6:"#\<surd>as = \<infinity> \<Longrightarrow>
          tsAbs\<cdot>as = \<epsilon> \<Longrightarrow>
          i \<noteq> \<bottom> \<Longrightarrow> #(srcdups\<cdot>(\<up>(t, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>as\<cdot>(Discr ack)))) = (lnsuc\<cdot>0)"
  by (metis only_empty_has_length_0 sconc_snd_empty slen_scons snd7)
  
lemma min_lub2:" chain Y \<Longrightarrow> (\<Squnion>i::nat. min (Y i) (x::lnat)) = min (\<Squnion>i::nat. (Y i)) (x)"
proof -
  assume a1: "chain Y"
  have "\<forall>l la. min (l::lnat) la = min la l"
    by (metis min.commute)
  then show ?thesis
    using a1 min_lub by presburger
qed    
    
lemma snd5:"#\<surd>as = \<infinity> \<Longrightarrow>
    tsAbs\<cdot>i \<noteq> \<epsilon> \<Longrightarrow>
    tsAbs\<cdot>as = \<epsilon> \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
apply(simp add: tsremdups_tsabs)
proof(induction i arbitrary: as ack)
  case adm
  then show ?case
  apply(rule adm_all)
  apply(rule adm_imp,simp)+
  apply(rule adm_all)
  apply(rule admI)
  by(simp add: contlub_cfun_arg contlub_cfun_fun min_lub2)
next
  case bottom
  then show ?case by simp
next
  case (delayfun i)
  then show ?case 
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun tslen_delayfun)
  apply(simp add: delayFun_def)
  apply(case_tac "as=\<bottom>", simp_all)
  by(simp add: tssnd_h_delayfun_msg)  
next
  case (mlscons i t)
  then show ?case 
  apply(rule_tac ts=as in tscases,simp_all)
  apply(case_tac "i=\<bottom>",simp_all)
  apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv tslen_mlscons tslen_delayfun)
  apply(simp add: delayFun_def)
  apply(metis below_bottom_iff  lnle_def lnsuc_lnle_emb lnzero_def min_def snd6)
  apply(case_tac "as=\<bottom>",simp_all)
  by(simp add: tsabs_mlscons)
qed 
 
lemma snd4:"tsAbs\<cdot>i = \<epsilon> \<Longrightarrow> tsAbs\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = \<epsilon>"
  by (metis bottomI strict_rev_sprojfst tsprojfst_tsabs tssnd_prefix_inp)    
    
lemma snd3:"#(tsAbs\<cdot>i)\<noteq>0 \<Longrightarrow> #\<surd>as = \<infinity>  \<Longrightarrow> lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))) = updis ack"
apply(simp add: tsremdups_tsabs tsprojsnd_tsabs)
proof(induction i arbitrary: as ack)
  case adm
  then show ?case 
  apply(rule adm_imp,simp)
  apply(rule adm_all)
  apply(rule adm_imp,simp)
  apply(rule adm_all)
  apply(rule admI)
  by(simp add: contlub_cfun_arg contlub_cfun_fun)
next
  case bottom
  then show ?case
  by simp
next
  case (delayfun it)
  then show ?case 
  apply(rule_tac ts= as in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun)
  apply(simp add: delayFun_def)
  apply(case_tac "as=\<bottom>",simp_all)
  by(simp add: tssnd_h_delayfun_msg)
next
  case (mlscons it t)
  then show ?case 
  apply(rule_tac ts= as in tscases,simp_all)
  apply(case_tac "it=\<bottom>",simp_all)
  apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  apply (metis lshd_updis srcdups_ex)
  apply(case_tac "as=\<bottom>",simp_all)
  apply(case_tac "a=ack",simp_all)
  apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv)
  apply (metis lshd_updis srcdups_ex)
  apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv)
  by (metis lshd_updis srcdups_ex)
qed
  
lemma lshd_below: "lshd\<cdot>ys = updis a \<and> xs \<sqsubseteq> ys \<and> xs \<noteq> \<bottom> \<Longrightarrow> lshd\<cdot>xs = updis a"
  using lshd_eq by fastforce  
   
lemma snd1:"#\<surd>as = \<infinity>  \<Longrightarrow> as \<noteq> \<bottom> \<Longrightarrow> #(tsAbs\<cdot>i)\<noteq>0 \<Longrightarrow> #(tsAbs\<cdot>as)\<noteq>0 \<Longrightarrow> tsAbs\<cdot>(tsRemDups\<cdot>as) \<sqsubseteq> tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) \<Longrightarrow> lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack"
proof-
  assume a0:"#(tsAbs\<cdot>i)\<noteq>0"
  assume a1:"as\<noteq>\<bottom>"
  assume a2:"#\<surd>as = \<infinity>"
  assume a3:"tsAbs\<cdot>(tsRemDups\<cdot>as) \<sqsubseteq> tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))"
  assume a4:"#(tsAbs\<cdot>as) \<noteq> 0"
  have h0:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))) = updis ack"
    using a0 a2 snd3 by blast
  have h1:"tsAbs\<cdot>as \<noteq> \<bottom>"
    using a4 by auto
  then show ?thesis
    by (metis a3 h0 lshd_below srcdups_nbot tsremdups_tsabs)
qed
    
lemma tssnd_ack2trans:"#\<surd>as = \<infinity>  \<Longrightarrow> tsAbs\<cdot>(tsRemDups\<cdot>as) \<sqsubseteq> tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) \<Longrightarrow>
   #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))
     = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
  apply(case_tac "as=\<bottom>",simp_all)
  apply(case_tac "#(tsAbs\<cdot>i)\<noteq>0",simp_all)
  apply(case_tac "#(tsAbs\<cdot>as)\<noteq>0",simp_all)
  using snd1 tssnd_ack2trans_2 apply fastforce
  using snd5 apply blast
  using snd4 by blast
  
end