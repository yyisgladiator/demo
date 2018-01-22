theory Sender_OZ
imports Sender 

begin

fixrec tsDropWhileTick :: "'a tstream \<rightarrow> 'a tstream" where
"tsDropWhileTick\<cdot>\<bottom> = \<bottom>" |
"tsDropWhileTick\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) =(tsDropWhileTick\<cdot>ts)" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsDropWhileTick\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = tsMLscons\<cdot>(up\<cdot>t)\<cdot>ts"

lemma tsdropwhiletick_delayfun:"tsDropWhileTick\<cdot>(delayFun\<cdot>msg) = tsDropWhileTick\<cdot>msg"
  by (simp add: delayfun_tslscons)

lemma tsdropwhiletick_mlscons:"ts \<noteq> \<bottom> \<Longrightarrow> tsDropWhileTick\<cdot>(updis t &&\<surd> ts) = updis t &&\<surd> ts"
  by (simp add: tsmlscons_lscons)

lemma tssnd_h_tsdropwhiletick: "tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(updis (ack1) &&\<surd> as)\<cdot>(Discr ack2)) = tsAbs\<cdot>(tsSnd_h\<cdot>(tsDropWhileTick\<cdot>i)\<cdot>(updis (ack1) &&\<surd> as)\<cdot>(Discr ack2))" 
  apply (induction i arbitrary: acka as,simp_all)
  apply (metis (no_types, hide_lams) delayfun_tslscons tsDropWhileTick.simps(2) tsSnd_h.simps(2) tsSnd_h.simps(6) tsabs_delayfun tsmlscons_bot2 tsmlscons_lscons)
  by (simp add: tsmlscons_lscons)

lemma sdropwhile_all:"\<forall>x. x \<in> sdom\<cdot>(as::'a stream) \<longrightarrow> f x \<Longrightarrow> sdropwhile f\<cdot>as = \<epsilon>"
 sorry  
 
lemma stakewhile_sdropwhilel2:"#(stakewhile f\<cdot>x) = \<infinity> \<Longrightarrow> sdropwhile f\<cdot>x = \<epsilon>"
proof-
 assume "#(stakewhile f\<cdot>x) = \<infinity>"
 moreover then have "#x = \<infinity>"
   by (metis inf_less_eq stakewhile_less)
 finally have "#(stakewhile f\<cdot>x) = #x "
   by (simp)
 then have "\<forall>a. a \<in> sdom\<cdot>(x::'a stream) \<longrightarrow> f a"
   by (metis snth_less snths_eq stakewhile_below stakewhile_dom)
 then show ?thesis
   using sdropwhile_all by blast
qed

lemma sdropwhile_well: assumes "ts_well s" shows "ts_well (sdropwhile f\<cdot>s)"
  apply (cases "#(stakewhile f\<cdot>s)" rule: lncases)
  apply (simp add: stakewhile_sdropwhilel2) 
  by (simp add: assms stakewhile_sdropwhilel1)

lemma tsdropwhiletick_sdropwhile: "tsDropWhileTick\<cdot>ts = (Abs_tstream (sdropwhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream ts)))"
  apply (induction ts, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg cont2contlubE)
  apply (smt Abs_tstream_inject Rep_tstream_inverse lub_eq lub_tstream mem_Collect_eq monofun_cfun_arg po_class.chain_def sdropwhile_well ts_well_Rep) 
  apply (metis (mono_tags, lifting) delayFun.abs_eq delayfun_tslscons eta_cfun sdropwhile_t tick_msg tsDropWhileTick.simps(2) tsconc_rep_eq)
  by (metis (mono_tags, lifting) Abs_Rep event.distinct(1) lscons_conv sdropwhile_f tsDropWhileTick.simps(3) tsmlscons_lscons tsmlscons_lscons2)
 
fixrec tsDropFirstMsg :: "'a tstream \<rightarrow> 'a tstream" where
"tsDropFirstMsg\<cdot>\<bottom> = \<bottom>" |
"tsDropFirstMsg\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = delayFun\<cdot>(tsDropFirstMsg\<cdot>ts)" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsDropFirstMsg\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = ts"

lemma tsdropFirstMsg_tsabs: "srt\<cdot>(tsAbs\<cdot>ts) = tsAbs\<cdot>(tsDropFirstMsg\<cdot>ts)"
  apply (induction ts,simp_all)
  apply (metis delayfun_tslscons tsDropFirstMsg.simps(2) tsabs_delayfun)
  by (metis stream.sel_rews(5) tsDropFirstMsg.simps(3) tsabs_mlscons tsmlscons_lscons up_defined)

lemma tsdropfirstmsg_delayfun: "tsDropFirstMsg\<cdot>(delayFun\<cdot>as) = delayFun\<cdot>(tsDropFirstMsg\<cdot>as)"
  by (simp add: delayfun_tslscons) 

lemma tsdropfirstmsg_mlscons: "tsDropFirstMsg\<cdot>(updis a &&\<surd> as) = as"
  by (metis tsDropFirstMsg.simps(1) tsDropFirstMsg.simps(3) tsmlscons_lscons tsmlscons_nbot_rev)

lemma srcdups_step_tsabs: "tsAbs\<cdot>as \<noteq> \<epsilon> \<Longrightarrow> srcdups\<cdot>(tsAbs\<cdot>as) = \<up>(shd (tsAbs\<cdot>as)) \<bullet> srcdups\<cdot>(sdropwhile (\<lambda> x. x= (shd (tsAbs\<cdot>as)))\<cdot>(tsAbs\<cdot>as))"
  by (metis srcdups_eq srcdups_step surj_scons)

lemma nmsg_inftick_h:
 assumes "#\<surd> as = \<infinity>" and "\<exists>n. snth n (Rep_tstream as) \<noteq> \<surd>"
 shows "tsAbs\<cdot>as \<noteq> \<epsilon>"
proof -
 obtain k and m where h0: "snth k (Rep_tstream as) = Msg m" by (meson assms event.exhaust)
 have h2: "Msg m \<in> sdom\<cdot>(Rep_tstream as)" by (metis h0 assms tsInfTicks not_less notinfI3 snth2sdom)
 have h3: "m \<in> tsDom\<cdot>as" using h2 tsdom_insert by auto
 have h4: "m \<in> sdom\<cdot>(tsAbs\<cdot>as)" using h3 by simp
 have h5: "tsAbs\<cdot>as \<noteq> \<epsilon>" using h4 by force
 thus ?thesis using h5 assms by auto
qed

lemma nmsg_inftick: assumes  "tsAbs\<cdot>as = \<epsilon>"  and "#\<surd> as = \<infinity>"
 shows "as = tsInfTick"
proof -
 have h6: "#(Rep_tstream as) = \<infinity>" using assms(2) tsInfTicks by auto
 have h7: "\<forall>n. snth n (Rep_tstream as) = \<surd>" using assms nmsg_inftick_h by auto
 have h10: "Rep_tstream as= Rep_tstream tsInfTick" by (simp add: h6 h7 tstickcount_insert tsInfTick.rep_eq sinf_snt2eq)
show ?thesis using Rep_tstream_inject h10 by auto
qed
  
lemma tssnd_h_msg_inftick:"i \<noteq> \<bottom> \<Longrightarrow> (tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>tsInfTick\<cdot>(Discr ack))) = \<up>(t, ack)\<infinity>"
  by (metis (no_types, lifting) delayfun_nbot lscons_conv s2sinftimes tsabs_delayfun tsabs_mlscons tsinftick_unfold tssnd_h_delayfun_nack)

lemma tssnd_h_inftick_slen:"#(tsAbs\<cdot>i) \<noteq> 0 \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>tsInfTick\<cdot>(Discr ack))) = \<infinity>"  
  apply (induction i arbitrary: ack)
  apply (rule adm_imp,simp+)
  apply (metis tsabs_delayfun tsinftick_unfold tssnd_h_delayfun)
  using tssnd_h_msg_inftick by fastforce

lemma lnsuc_fin: "k \<noteq> 0 \<Longrightarrow> lnsuc\<cdot>n = Fin k \<equiv> n = Fin (k-1)"
  by (induction k,simp_all)

lemma tssnd_h_tsabs: "tsAbs\<cdot>i = \<epsilon> \<Longrightarrow> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)) = \<epsilon>"
  apply (induction i arbitrary: as ack, simp_all)
  apply (metis (no_types, lifting) bottomI srcdups_nbot strict_rev_sprojfst tsabs_delayfun tsprojfst_tsabs tsremdups_tsabs tssnd_prefix_inp)
  by (simp add: tsabs_mlscons)

lemma slen_scons2: "#b \<le> #(a \<bullet> b)" 
  apply (induction b arbitrary: a rule: ind,simp_all) 
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
  by (metis (no_types, lifting) assoc_sconc le_cases lnsuc_lnle_emb sconc_fst_empty slen_scons surj_scons)

lemma slen_tstickcount: "#\<surd>(ts) < \<infinity> \<Longrightarrow> #(Rep_tstream ts) < \<infinity>"
  by simp

lemma tsdropwhiletick_shd: "tsAbs\<cdot>i \<noteq> \<epsilon> \<Longrightarrow> unpackMsg\<cdot>(tsLshd\<cdot>(tsDropWhileTick\<cdot>i)) = (lshd\<cdot>(tsAbs\<cdot>i))" 
  apply (induction i,simp_all)
  apply (simp add: delayfun_tslscons)
  apply (simp add: tsdropwhiletick_mlscons tsabs_mlscons)
  by(simp add: tsmlscons2tslscons unpackMsg_def)

lemma tslshd_tsrt: "ts = tsLshd\<cdot>ts &\<surd> tsRt\<cdot>ts" 
  apply (rule_tac ts=ts in tscases,simp_all)
  apply (metis tslscons_bot tslscons_lshd)
  apply (simp add: delayfun_tslscons tick_eq_discrtick)
  by (metis tslscons_bot tslscons_lshd tslscons_srt tsmlscons_bot2 tsmlscons_lscons)

lemma tslscons_unpackmsg: assumes "a \<noteq> up\<cdot>DiscrTick" shows "a &\<surd> ts = unpackMsg\<cdot>a &&\<surd> ts" 
  proof (cases "a = \<bottom>")
    case True
    then show ?thesis
      by (simp add: unpackMsg_def) 
  next
    case False
    obtain m where "a = updis m"
      using False updis_exists by auto 
    then show ?thesis
      apply (simp add: unpackMsg_def)
      by (metis (no_types, lifting) DiscrTick_def assms event.exhaust event.simps(4) tsmlscons2tslscons) 
  qed

lemma lshd_shd: "s\<noteq>\<epsilon> \<Longrightarrow> lshd\<cdot>s = updis (shd s)"
  by (metis lshd_updis surj_scons)

lemma tsdropwhiletick_tslshd_imp: "tsLshd\<cdot>(tsDropWhileTick\<cdot>i) \<noteq> up\<cdot>DiscrTick"
  apply (induction i,simp_all)
  apply (metis tslscons_nbot3 tslshd_tsrt)
  apply (simp add: tsdropwhiletick_delayfun)
  apply (simp add: tsdropwhiletick_mlscons tsmlscons_lscons)
  by (metis (no_types) tslscons_nbot3 tsmlscons_lscons tsmlscons_nbot_rev)

lemma rep_tstream_delayfun: "Rep_tstream (delay ts) = \<up>\<surd> \<bullet> (Rep_tstream ts)"
  by (simp add: delayFun.rep_eq tsconc_rep_eq) 

lemma tsDropwhileTick_tsrt_nbot: "tsAbs\<cdot>i \<noteq> \<epsilon> \<Longrightarrow> tsRt\<cdot>(tsDropWhileTick\<cdot>i) \<noteq> \<bottom>" 
  apply (induction i,simp_all)
  apply (simp add: tsdropwhiletick_delayfun)
  by (simp add: tsdropwhiletick_mlscons tsmlscons_lscons)

lemma h4_2_h1: "Fin x \<le> #(stakewhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream as)) \<Longrightarrow>
    #(stakewhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream i)) = Fin x \<Longrightarrow>
    tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)) =
    tsAbs\<cdot>(tsSnd_h\<cdot>(Abs_tstream (sdrop x\<cdot>(Rep_tstream i)))\<cdot>(Abs_tstream (sdrop x\<cdot>(Rep_tstream as)))\<cdot>(Discr ack))" 
  apply (induction x arbitrary:as i,simp_all) 
  apply (rule_tac xs=as in tstream_exhaust,simp_all)
  apply (rule_tac xs=i in tstream_exhaust,simp_all)
  apply (simp add: rep_tstream_delayfun tssnd_h_delayfun)
  apply (simp add: tsmlscons_lscons2 lscons_conv)
  by (simp add: tsmlscons_lscons2 lscons_conv)

lemma h4_2_h2: "#(stakewhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream as)) = Fin k \<Longrightarrow> #(stakewhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream as)) <  #(stakewhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream i)) \<Longrightarrow>
   tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)) =  tsAbs\<cdot>(tsSnd_h\<cdot>(Abs_tstream (sdropwhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream i)))\<cdot>
   (Abs_tstream (sdropwhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream as)))\<cdot>(Discr ack))"
  apply (induction k arbitrary:as i,simp_all) 
  apply (rule_tac xs=as in tstream_exhaust,simp_all)
  apply (simp add: rep_tstream_delayfun)
  apply (simp add: tsmlscons_lscons2 lscons_conv)
  apply (subst absts2mlscons2)
  using sConc_fin_well apply blast
  apply (subst  tssnd_h_tsdropwhiletick)
  apply (simp add: tsdropwhiletick_sdropwhile)
  apply (rule_tac xs=as in tstream_exhaust,simp_all)
  apply (rule_tac xs=i in tstream_exhaust,simp_all)
  apply (simp add: rep_tstream_delayfun tssnd_h_delayfun)
  apply (simp add: tsmlscons_lscons2 lscons_conv)
  by (simp add: tsmlscons_lscons2 lscons_conv)

lemma tick_split: "Fin x \<le> #(stakewhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream as)) \<Longrightarrow> 
    as = tsntimes x (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> Abs_tstream (sdrop x\<cdot>(Rep_tstream as))"
  apply (induction x arbitrary:as,simp_all)
  apply (rule_tac xs=as in tstream_exhaust,simp_all)
  apply (simp add: rep_tstream_delayfun)
  apply (metis delayfun_insert tsconc_assoc)
  by (simp add: tsmlscons_lscons2 lscons_conv)

lemma mlscons_conc_delay_bottom: "(updis msg &&\<surd> (delay \<bottom>)) \<bullet>\<surd> ts=  updis msg &&\<surd> delay ts"
  by (simp add: delayFun_def tsconc_mlscons)

lemma h4_2_h3_h: "tsAbs\<cdot>i \<noteq> \<epsilon> \<Longrightarrow>
           tsSnd_h\<cdot>(updis (shd (tsAbs\<cdot>i)) &&\<surd> tsRt\<cdot>(tsDropWhileTick\<cdot>i))\<cdot>(tsntimes x (Abs_tstream (\<up>\<surd>)))\<cdot>(Discr ack) =
           tsntimes x (updis (shd (tsAbs\<cdot>i), ack) &&\<surd> delay \<bottom>)"
  apply (induction x,simp_all)
  by (metis delayfun_insert mlscons_conc_delay_bottom tsDropwhileTick_tsrt_nbot tssnd_h_delayfun_nack)

lemma tsntimes_minus: "x\<noteq>0 \<Longrightarrow> tsntimes x ts = ts \<bullet>\<surd> (tsntimes (x-1) ts)"
  by (metis Suc_diff_1 not_gr_zero tsntimes.simps(2))

lemma h4_2_h3: assumes "tsAbs\<cdot>i \<noteq> \<epsilon>" shows  "(tsSnd_h\<cdot>(tsDropWhileTick\<cdot>i)\<cdot>((tsntimes (x) (Abs_tstream (\<up>\<surd>))) \<bullet>\<surd> as)\<cdot>(Discr ack)) =
            (tsntimes (x) (updis ((shd (tsAbs\<cdot>i)), ack) &&\<surd> delayFun\<cdot>\<bottom>) \<bullet>\<surd> (tsSnd_h\<cdot>(tsDropWhileTick\<cdot>i)\<cdot>as)\<cdot>(Discr ack))"
  using assms apply (induction x arbitrary: as i,simp_all)
  apply (subst tslshd_tsrt)
  apply (subst tslscons_unpackmsg)
  apply (simp add: tsdropwhiletick_tslshd_imp)
  apply (simp add: assms tsdropwhiletick_shd lshd_shd  h4_2_h3_h)
  apply (fold delayFun.rep_eq)
  apply (simp add: tsDropwhileTick_tsrt_nbot tsconc_delayfun tssnd_h_delayfun_nack  mlscons_conc_delay_bottom)
  by (metis (no_types, lifting) lshd_shd tsdropwhiletick_shd tsdropwhiletick_tslshd_imp tslscons_unpackmsg tslshd_tsrt mlscons_conc_delay_bottom tsconc_assoc)

lemma h4_2_h: "#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) \<le> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(updis (\<not> ack) &&\<surd> as)\<cdot>(Discr ack)))"
proof (cases "tsAbs\<cdot>i = \<epsilon>")
  case True
  then show ?thesis by (simp add: tssnd_h_tsabs) 
next
  case False
  then have "\<exists>n. snth n (Rep_tstream i) \<noteq> \<surd>"
    by (metis (mono_tags, lifting) ex_snth_in_sfilter_nempty mem_Collect_eq slen_empty_eq slen_smap tsabs_insert) 
  then obtain n where h1:"#(stakewhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream i)) = Fin n"
    by (metis (mono_tags) inf_ub less_le lncases stakewhile_snth)
  then have h2: "sdropwhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream i) = sdrop n\<cdot>(Rep_tstream i)"
    by (simp add: stakewhile_sdropwhilel1)
  obtain x1 where h31: "x1 = (if (#(stakewhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream as))\<ge> (Fin n)) then (Fin n) else (#(stakewhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream as))))"
    by simp
  then obtain x where h32:"x1 = Fin x"
    by (metis (mono_tags, lifting) inf_ub leI less_le_trans lnat_well_h2)
  then have h3: "tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)) = tsAbs\<cdot>(tsSnd_h\<cdot>(tsDropWhileTick\<cdot>i)\<cdot>(Abs_tstream (sdrop (x)\<cdot>(Rep_tstream as)))\<cdot>(Discr ack))" 
    apply (simp add: h2 h31) 
    apply (case_tac "Fin n \<le> #(stakewhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream as))",simp_all)
    apply (simp add:  tsdropwhiletick_sdropwhile h2)
    using h1 h4_2_h1 apply blast
    by (simp add: h1 h4_2_h2 tsdropwhiletick_sdropwhile stakewhile_sdropwhilel1)
  have h4: "tsSnd_h\<cdot>(tsDropWhileTick\<cdot>i)\<cdot>(updis (\<not> ack) &&\<surd> as)\<cdot>(Discr ack) =  (updis ((shd (tsAbs\<cdot>i)), ack)) &&\<surd> tsSnd_h\<cdot>(tsDropWhileTick\<cdot>i)\<cdot>as\<cdot>(Discr ack)"
    apply (subst tslshd_tsrt [of "tsDropWhileTick\<cdot>i"])
    apply (subst tslscons_unpackmsg)
    apply (simp add: tsdropwhiletick_tslshd_imp)
    using False apply (simp add: tsdropwhiletick_shd)
    apply (case_tac "as = \<bottom>",simp)
    apply (simp add: lshd_shd)
    apply (subst tssnd_h_mlscons_nack)
    apply (simp add: tsDropwhileTick_tsrt_nbot,simp_all)
    apply (subst(2) tslshd_tsrt [of "tsDropWhileTick\<cdot>i"])
    apply (subst tslscons_unpackmsg)
    apply (simp add: tsdropwhiletick_tslshd_imp) 
    by (simp add: tsdropwhiletick_shd  lshd_shd)
  have h5: "as = (tsntimes (x) (Abs_tstream (\<up>\<surd>))) \<bullet>\<surd> (Abs_tstream (sdrop (x)\<cdot>(Rep_tstream as)))" 
    using h32 apply (simp add: h2 h31) 
    apply (case_tac "Fin n \<le> #(stakewhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream as))",simp_all)
    by (simp add: tick_split)+
  have h6: "(tsSnd_h\<cdot>(tsDropWhileTick\<cdot>i)\<cdot>((tsntimes (x) (Abs_tstream (\<up>\<surd>))) \<bullet>\<surd> (Abs_tstream (sdrop (x)\<cdot>(Rep_tstream as))))\<cdot>(Discr ack)) =
            (tsntimes (x) (updis ((shd (tsAbs\<cdot>i)), ack) &&\<surd> delayFun\<cdot>\<bottom>) \<bullet>\<surd> (tsSnd_h\<cdot>(tsDropWhileTick\<cdot>i)\<cdot>(Abs_tstream (sdrop (x)\<cdot>(Rep_tstream as))))\<cdot>(Discr ack))"
    using False h4_2_h3 by blast
  from h3 show ?thesis
    apply simp
    apply (subst tssnd_h_tsdropwhiletick)
    apply (subst h4)
    apply (subst(2) h5)
    apply (subst h6)
    apply (case_tac "tsSnd_h\<cdot>(tsDropWhileTick\<cdot>i)\<cdot>(Abs_tstream (sdrop (x)\<cdot>(Rep_tstream as)))\<cdot>(Discr ack) = \<bottom>",simp)
    apply (subst tsabs_mlscons)
    apply (metis bottomI ts_tsconc_prefix tsconc_fst_empty)
    apply (simp add: lscons_conv)
    apply (subst tsabs_conc)
    apply (rule slen_tstickcount)
    apply (metis Inf'_neq_0 delayFun_dropFirst fintsntms2fin inf_less_eq leI strict_tstickcount tsinftickDrop tstickcount_mlscons)
    using less_lnsuc slen_scons2 trans_lnle by blast
qed
  
lemma h4_2: "#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(tsDropWhile\<cdot>(Discr (\<not> ack))\<cdot>as)\<cdot>(Discr ack))) \<le> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))" 
  apply (induction as arbitrary: i ack, simp_all)
  apply (rule adm_all)+
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
  apply (rule_tac xs=i in tstream_exhaust,simp_all)
  apply (simp add: tsdropwhile_delayfun tssnd_h_delayfun)
  apply (simp add: tsdropwhile_delayfun tssnd_h_delayfun_nack lscons_conv tsabs_mlscons)
  apply (case_tac "t \<noteq> ack")
  apply (simp add: tsdropwhile_t tsabs_mlscons shd_updis)
  apply (meson dual_order.trans h4_2_h)
  by (simp add: tsdropwhile_f)

lemma stakewhile_stimes: 
  "#(stakewhile (\<lambda>x. x=t)\<cdot>z) = Fin n \<longrightarrow> stakewhile (\<lambda>x. x=t)\<cdot>z = sntimes n (\<up>t)"
  apply (induction n arbitrary:z t,simp)
  apply (rule_tac x=z in scases,simp)
  by (case_tac "a = t",simp_all)

lemma smap_shd: "s\<noteq>\<epsilon> \<Longrightarrow> shd (smap f\<cdot>s) = f (shd s)"
  by (simp add: smap_hd_rst) 

lemma sfilter_shd: "s\<noteq> \<epsilon> \<Longrightarrow> shd s \<in> X \<Longrightarrow> shd (X \<ominus> s) = shd s"
  by (rule_tac x=s in scases,simp_all)

lemma sfilter_dwl1_inv: 
  "sfilter X\<cdot>p = sfilter X\<cdot>(sdropwhile (\<lambda>x. x\<notin>X)\<cdot>p)"
by simp

lemma msg_inversmsg: "a \<noteq> \<surd> \<Longrightarrow> \<M> \<M>\<inverse> a = a"
  by (metis (no_types) event.exhaust event.simps(4)) 

lemma h4_1_h: assumes "tsAbs\<cdot>i \<noteq> \<epsilon>" obtains n where "i = (tsntimes n (Abs_tstream (\<up>\<surd>))) \<bullet>\<surd> ((updis (shd (tsAbs\<cdot>i))) &&\<surd> (Abs_tstream (sdrop (n+1)\<cdot>(Rep_tstream i))))"
  proof -
  have "\<exists>n. snth n (Rep_tstream i) \<noteq> \<surd>"
    by (metis (mono_tags, lifting) assms ex_snth_in_sfilter_nempty mem_Collect_eq slen_empty_eq slen_smap tsabs_insert) 
  then obtain n where h0: "#(stakewhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream i)) = Fin n"
    by (metis (mono_tags) inf_ub less_le lncases stakewhile_snth)
  then have h1:"(stakewhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream i)) = (sntimes n (\<up>\<surd>))"
    using stakewhile_stimes by blast
  have h2:"i = Abs_tstream (stakewhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream i) \<bullet> sdropwhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream i))"
    by (simp add: stakewhileDropwhile)
  have h3: "tsntimes n (Abs_tstream (\<up>\<surd>)) = Abs_tstream (sntimes n (\<up>\<surd>))" 
    apply (induction n,simp_all)
    by (metis (no_types, lifting) Abs_Rep Rep_Abs sinftimes_unfold sntimes_stake stake_Suc tick_msg tsInfTick.rep_eq tsInfTick_take tsconc_insert tstake_tick)
  have "snth n (Rep_tstream i) = Msg (shd (tsAbs\<cdot>i))"
    proof - 
      have "Msg (shd (tsAbs\<cdot>i)) = shd (sdropwhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream i))"
        apply (simp add: tsAbs_def )
        apply (subst smap_shd)
        apply (metis Rep_tstream_strict assms strict_sfilter tsabs_bot tsabs_insert)
        apply (subst msg_inversmsg)
        apply (metis (mono_tags, lifting) Rep_tstream_strict assms mem_Collect_eq sfilter_ne_resup strict_sfilter tsabs_bot tsabs_insert)
        apply (subst sfilter_dwl1_inv)        
        apply (subst sfilter_shd,simp_all)
        apply (metis Rep_tstream_strict assms ex_snth_in_sfilter_nempty mem_Collect_eq sconc_snd_empty stakewhileDropwhile stakewhile_snth strict_sfilter tsabs_bot tsabs_insert)
        apply (rule_tac x= "(sdropwhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream i))" in scases,simp_all)
        apply (metis Rep_tstream_strict assms ex_snth_in_sfilter_nempty mem_Collect_eq sconc_snd_empty stakewhileDropwhile stakewhile_snth strict_sfilter tsabs_bot tsabs_insert)
        using sdropwhile_resup by blast  
   then show ?thesis
        by (simp add: h0 snth_def stakewhile_sdropwhilel1)
    qed
  then have "(updis (shd (tsAbs\<cdot>i)) &&\<surd> Abs_tstream (sdrop (Suc n)\<cdot>(Rep_tstream i))) = Abs_tstream (sdrop n\<cdot>(Rep_tstream i))"
    by (metis Abs_tstream_strict absts2mlscons lscons_conv snth_def srt_drop strict_sdrop surj_scons ts_well_Rep ts_well_drop tsmlscons_nbot_rev)
  then have h4: "(updis (shd (tsAbs\<cdot>i)) &&\<surd> Abs_tstream (sdrop (Suc n)\<cdot>(Rep_tstream i))) = Abs_tstream (sdropwhile (\<lambda>x. x=\<surd>)\<cdot>(Rep_tstream i))" 
    using h0 by (simp add: stakewhile_sdropwhilel1)
  have "i = (tsntimes n (Abs_tstream (\<up>\<surd>))) \<bullet>\<surd> ((updis (shd (tsAbs\<cdot>i))) &&\<surd> (Abs_tstream (sdrop (n+1)\<cdot>(Rep_tstream i))))"
    apply (subst h2)
    by (simp add: h3 h4 h1 tsconc_insert h0 stakewhile_sdropwhilel1)
  then show ?thesis
    using that by blast
qed

lemma h4_1_hh_h2: "m \<le> n \<Longrightarrow>
    tsAbs\<cdot>(tsSnd_h\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> i)\<cdot>(tsntimes m (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> as)\<cdot>(Discr ack)) =
    tsAbs\<cdot>(tsSnd_h\<cdot>(tsntimes (n-m) (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> i)\<cdot>as\<cdot>(Discr ack))" 
  apply (induction m arbitrary: i as n,simp_all) 
  apply (subst tsntimes_minus,simp_all)
  apply (fold delayFun.rep_eq)
  by (simp add: tsconc_delayfun tsconc_mlscons tssnd_h_delayfun)

lemma h4_1_hh_h3:  "m > n \<Longrightarrow>
    tsAbs\<cdot>(tsSnd_h\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> i)\<cdot>(tsntimes m (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> as)\<cdot>(Discr ack)) =  
    tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(tsntimes (m-n) (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> as)\<cdot>(Discr ack))"
  apply (induction n arbitrary: i as m,simp_all) 
  apply (subst(2) tsntimes_minus,simp_all)
  apply (fold delayFun.rep_eq)
  by (simp add: tsconc_delayfun tsconc_mlscons tssnd_h_delayfun)

lemma h4_1_hh_h4: "i \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(updis msg &&\<surd> i)\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> as)\<cdot>(Discr ack) = 
  (tsntimes n (updis (msg,ack) &&\<surd> delayFun\<cdot>\<bottom>) \<bullet>\<surd> (tsSnd_h\<cdot>(updis msg &&\<surd> i)\<cdot> as)\<cdot>(Discr ack))"
  apply (induction n arbitrary: i,simp_all)  
  apply (fold delayFun.rep_eq)
  by (simp add: tsconc_delayfun tsconc_mlscons tssnd_h_delayfun_nack)

lemma h4_1_hh_h42: "as \<noteq> \<bottom> \<Longrightarrow> tsAbs\<cdot>(tsSnd_h\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> i)\<cdot>(updis msg &&\<surd> as)\<cdot>(Discr ack)) = 
   tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(updis msg &&\<surd> as)\<cdot>(Discr ack))"
  apply (induction n arbitrary: i,simp_all)  
  apply (fold delayFun.rep_eq)
  by (simp add: tsconc_delayfun tssnd_h_delayfun_msg)

lemma h4_1_hh_h5: "#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)))\<cdot>(Discr ack))) \<le> Fin n"
  apply (induction n arbitrary: i,simp_all)
  apply (fold delayFun.rep_eq) 
  apply (rule_tac xs=i in tstream_exhaust,simp_all)
  apply (metis convert_inductive_asm leD leI tsabs_delayfun tssnd_h_delayfun)
  by (simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)

lemma h4_1_hh_52: "i \<noteq> \<bottom> \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>(updis msg &&\<surd> i)\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)))\<cdot>(Discr ack))) = Fin n"
  apply (induction n arbitrary: i,simp_all)
  apply (fold delayFun.rep_eq) 
  by (simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)

lemma tsntimes_tsabs: "tslen\<cdot>ts < \<infinity> \<Longrightarrow>tsAbs\<cdot>(tsntimes n ts) = sntimes n (tsAbs\<cdot>ts)" 
  apply (induction n,simp_all)
  by (simp add: tsabs_conc tslen_def)

lemma tsntimes_rep_tstream: "Rep_tstream (tsntimes n ts) = sntimes n (Rep_tstream ts)" 
  apply (induction n,simp_all)
  by (metis Abs_Rep ts_well_Rep tsconc_rep_eq)

lemma sntimes_fin: "#s < \<infinity> \<Longrightarrow> #(n \<star> s) < \<infinity>" 
  apply (induction n,simp_all)
  by (metis fold_inf)

lemma h4_1_hh_h7 [simp]:"tsAbs\<cdot>(tsSnd_h\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)))\<cdot>as\<cdot>(Discr ack)) = \<epsilon>"
  apply (induction n arbitrary: as,simp_all)
  apply (fold delayFun.rep_eq) 
  apply (rule_tac xs=as in tstream_exhaust,simp_all)
  apply (simp add: tssnd_h_delayfun)
  by (simp add: tssnd_h_delayfun_msg)

lemma h4_1_hh_h6h: "(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> delay ts) = delay (tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> ts)"
  by (simp add: delayFun_def tsConc_eqts_comm) 

lemma h4_1_hh_h6: "#(tsAbs\<cdot>(tsSnd_h\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> i)\<cdot>(tsDropWhile\<cdot>(Discr ack)\<cdot>as)\<cdot>(Discr (\<not> ack))))
    \<le> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not>ack))))" 
  apply (induction as arbitrary: n i,simp_all)
  apply (rule adm_all)+
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
  apply (rule_tac xs=i in tstream_exhaust,simp_all)
  apply (simp add: h4_1_hh_h6h tsdropwhile_delayfun tssnd_h_delayfun)
  apply (case_tac "n=0",simp)
  apply (smt h4_2)
  apply (subst tsntimes_minus,simp)
  apply (fold delayFun.rep_eq)
  apply (simp add: tsdropwhile_delayfun tsconc_delayfun tssnd_h_delayfun tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  using less_lnsuc order.trans apply blast
  apply (case_tac "t = ack",simp_all)
  apply (simp add: tsdropwhile_t)
  apply (smt dual_order.trans h4_2_h)
  apply (simp add: tsdropwhile_f)
  by (simp add: h4_1_hh_h42)

lemma sconc_scons2: "s1 \<bullet> (s2 \<bullet> s3) = (s1 \<bullet> s2) \<bullet> s3"
  by simp 

lemma h4_1_hh_h8: "n\<star>\<up>a \<bullet> \<up>a = (n+1)\<star>\<up>a"
  by (metis One_nat_def add.right_neutral add_Suc_right sntimes_Suc2)

lemma h4_1_hh_h9h: "n \<noteq> 0 \<Longrightarrow> Fin n = Fin (Suc (n-1))"
  by simp  

lemma h4_1_hh_h9hh: " #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(updis (\<not> ack) &&\<surd> as)\<cdot>(Discr (\<not> ack)))) = Fin k \<Longrightarrow>
       #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> (updis (\<not> ack) &&\<surd> as))\<cdot>(Discr (\<not> ack))))
       \<le> Fin (Suc (n + k))"
  apply (induction n arbitrary: i as k,simp_all)
  apply (fold delayFun.rep_eq)
  apply (rule_tac xs=i in tstream_exhaust,simp_all)
  apply (simp add: tssnd_h_delayfun tsconc_delayfun)
  apply (metis convert_inductive_asm leD leI tsdropwhiletick_delayfun tssnd_h_tsdropwhiletick)
  by (simp add: tssnd_h_delayfun_nack tsconc_delayfun tsabs_mlscons lscons_conv)

lemma h4_1_hh_h9hhh: assumes "#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(updis ack &&\<surd> as)\<cdot>(Discr (\<not> ack)))) = Fin k" obtains k2 where 
  "#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack)))) = Fin k2 "
  by (smt assms h4_2_h inf_less_eq ninf2Fin)

lemma h4_1_hh_h9hhhh: "x \<le> Fin (Suc (n + k2)) \<Longrightarrow> k2 \<le> k \<Longrightarrow> x \<le> Fin (Suc (n + k))"
  by (smt add.assoc dual_order.trans leI le_iff_add less2lnleD less2nat_lemma not_less_eq_eq)

lemma h4_1_hh_h9_h4: assumes "
       (\<And>n i k. (i::'a tstream) \<noteq> \<bottom> \<Longrightarrow>  #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack)))) = Fin k \<Longrightarrow>
                 #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> tsDropWhile\<cdot>(Discr ack)\<cdot>as)\<cdot>(Discr (\<not> ack))))
                 \<le> Fin (Suc (n + k))) " "as \<noteq> \<bottom>" "(i::'a tstream) \<noteq> \<bottom>" "
       #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(updis ack &&\<surd> as)\<cdot>(Discr (\<not> ack)))) = Fin k " shows
"#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> tsDropWhile\<cdot>(Discr ack)\<cdot>as)\<cdot>(Discr (\<not> ack))))
       \<le> Fin (Suc (n + k))"
  proof -
    obtain k2 where h0:"#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack)))) = Fin k2"
      using assms(4) h4_1_hh_h9hhh by blast
    then have h1:"k2 \<le> k"
      by (smt assms(4) h4_2_h less2nat_lemma)
    have h2: "#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> tsDropWhile\<cdot>(Discr ack)\<cdot>as)\<cdot>(Discr (\<not> ack))))
       \<le> Fin (Suc (n + k2))"
      using assms(3) h0 assms(1)[of i] by blast
    then show ?thesis
      using h1 h4_1_hh_h9hhhh by blast 
qed
                          
lemma h4_1_hh_h9: "i \<noteq> \<bottom> \<Longrightarrow>as \<noteq> \<bottom> \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack)))) = Fin k \<Longrightarrow>
  #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> tsDropWhile\<cdot>(Discr ack)\<cdot>as)\<cdot>(Discr (\<not> ack))))
  \<le> lnsuc\<cdot>(Fin (n + k))" 
  apply (induction as arbitrary: n i k,simp_all)
  apply (rule adm_all)+
  apply (rule adm_imp,simp)+
  apply (rule adm_all)
  apply (rule adm_imp,simp_all)
  apply (rule admI)
  apply (smt ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun finChainapprox)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (subst lnle_def)
  apply (rule is_lub_thelub)
  apply (simp add: ch2ch_Rep_cfunR)
  apply (rule ub_rangeI, simp)
  apply (rule_tac xs=i in tstream_exhaust,simp_all)
  apply (simp add: h4_1_hh_h6h tsdropwhile_delayfun tssnd_h_delayfun)
  apply (case_tac "ts=\<bottom>",simp)
  apply (case_tac "as=\<bottom>",simp)
  using convert_inductive_asm h4_1_hh_h5 leD leI apply blast
  apply blast
  apply (case_tac "n=0")
  apply (simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv tsdropwhile_delayfun)
  apply (smt h4_2 less_lnsuc trans_lnle)
  apply (simp add: tsdropwhile_delayfun tsconc_delayfun tssnd_h_delayfun tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  apply (simp add: delayFun_def )
  apply (fold tsConc_eqts_comm)
  apply (fold delayFun.rep_eq)
  apply (simp add: tsdropwhile_delayfun tsconc_delayfun tssnd_h_delayfun tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  apply (case_tac "k=0",simp)
  apply (simp add: lnsuc_fin) 
  apply (subst h4_1_hh_h9h,simp)
  apply (case_tac "as=\<bottom>",simp)
  apply (simp add: h4_1_hh_52)
  apply (smt Nat.add_diff_assoc Suc_leI diff_Suc_eq_diff_pred minus_nat.diff_0 tsdropfirstmsg_mlscons tsmlscons_bot2)
  apply (case_tac "t = ack",simp_all)
  apply (simp add: tsdropwhile_t)
  using h4_1_hh_h9_h4 apply blast 
  by(simp add: tsdropwhile_f h4_1_hh_h9hh)

lemma h4_1_hh: assumes "tsAbs\<cdot>i \<noteq> \<epsilon>" "tsAbs\<cdot>as \<noteq> \<epsilon>" shows    
  "#(tsAbs\<cdot>(tsSnd_h\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> Abs_tstream (sdrop (Suc n)\<cdot>(Rep_tstream i)))\<cdot>
  (tsntimes m (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> tsDropWhile\<cdot>(Discr ack)\<cdot>(Abs_tstream (sdrop (Suc m)\<cdot>(Rep_tstream as))))\<cdot>(Discr (\<not> ack))))
  \<le> #(tsAbs\<cdot>(tsSnd_h\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> (updis msg &&\<surd> Abs_tstream (sdrop (Suc n)\<cdot>(Rep_tstream i))))\<cdot>
  (tsntimes m (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> (updis ack &&\<surd> Abs_tstream (sdrop (Suc m)\<cdot>(Rep_tstream as))))\<cdot>(Discr ack)))" 
 proof (cases "m \<le> n")
   case True
   then show ?thesis
    apply (simp add: h4_1_hh_h2)
    apply (case_tac "Abs_tstream (sdrop (Suc n)\<cdot>(Rep_tstream i)) = \<bottom>",simp)
    apply (case_tac "Abs_tstream (sdrop (Suc m)\<cdot>(Rep_tstream as)) = \<bottom>",simp)
    apply (simp add: h4_1_hh_h42 tssnd_h_mlscons_ack tsabs_mlscons lscons_conv)
    using h4_1_hh_h6 less_lnsuc trans_lnle by blast
    next
   case False
   then show ?thesis 
   apply (simp add: h4_1_hh_h3 h4_1_hh_h4)
   apply (case_tac "Abs_tstream (sdrop (Suc n)\<cdot>(Rep_tstream i)) = \<bottom>",simp)
   apply (case_tac "Abs_tstream (sdrop (Suc m)\<cdot>(Rep_tstream as)) = \<bottom>",simp)
   apply (simp add: h4_1_hh_52 h4_1_hh_h5)
   apply (simp add: h4_1_hh_h4 tssnd_h_mlscons_ack)
   apply (subst tsabs_conc)
   apply (simp add: tsntimes_rep_tstream tsabs_mlscons lscons_conv tsmlscons_lscons2 rep_tstream_delayfun)
   apply (metis fold_inf gr_0 inf_ub less_le lnat.sel_rews(2) lscons_conv slen_scons sntimes_fin strict_slen sup'_def)
   apply (subst tsntimes_tsabs)
   apply (simp add: tslen_def tsmlscons_lscons2 lscons_conv rep_tstream_delayfun)
   apply (simp add: tsabs_mlscons lscons_conv h4_1_hh_h5)
   apply (subst  sconc_scons2) apply (subst h4_1_hh_h8 [of "m-n"])
   apply (case_tac "#(tsAbs\<cdot>(tsSnd_h\<cdot>(Abs_tstream (sdrop (Suc n)\<cdot>(Rep_tstream i)))\<cdot>(Abs_tstream (sdrop (Suc m)\<cdot>(Rep_tstream as)))\<cdot>(Discr (\<not> ack)))) = \<infinity>")
   apply (simp add: slen_sconc_snd_inf)
   using ninf2Fin [of " #(tsAbs\<cdot>
      (tsSnd_h\<cdot>(Abs_tstream (sdrop (Suc n)\<cdot>(Rep_tstream i)))\<cdot>
       (Abs_tstream (sdrop (Suc m)\<cdot>(Rep_tstream as)))\<cdot>
       (Discr (\<not> ack))))"] apply auto
   by (smt h4_1_hh_h9 slen_sconc_all_finite sntimes_len)  
 qed

lemma h4_1: assumes "tsAbs\<cdot>i \<noteq> \<epsilon>" " #\<surd> as = \<infinity>" "shd (tsAbs\<cdot>as) = ack" shows 
  "#(tsAbs\<cdot>(tsSnd_h\<cdot>(tsDropFirstMsg\<cdot>i)\<cdot>(tsDropWhile\<cdot>(Discr ack)\<cdot>as)\<cdot>(Discr (\<not> ack))))\<le> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))" 
  proof (cases "tsAbs\<cdot>as = \<epsilon>")
    case True
    then show ?thesis using assms tssnd_h_inftick_slen nmsg_inftick by fastforce
  next
    case False
     then obtain m where h1: "as = (tsntimes m (Abs_tstream (\<up>\<surd>))) \<bullet>\<surd> ((updis (shd (tsAbs\<cdot>as))) &&\<surd> (Abs_tstream (sdrop (m+1)\<cdot>(Rep_tstream as))))"
       using h4_1_h by blast
     obtain n where h2: "i = (tsntimes n (Abs_tstream (\<up>\<surd>))) \<bullet>\<surd> ((updis (shd (tsAbs\<cdot>i))) &&\<surd> (Abs_tstream (sdrop (n+1)\<cdot>(Rep_tstream i))))"
       using assms(1) h4_1_h by blast
     have h3: "\<forall>ts. tsDropFirstMsg\<cdot>(tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> ts) = tsntimes n (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> tsDropFirstMsg\<cdot>ts"
       apply (induction n,simp)
       by (metis delayFun.rep_eq tsconc_delayfun tsdropfirstmsg_delayfun tsntimes.simps(2))
     have h4: "\<forall>ts. tsDropWhile\<cdot>(Discr ack)\<cdot>(tsntimes m (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> ts) = tsntimes m (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> (tsDropWhile\<cdot>(Discr ack)\<cdot>ts)"
       apply (induction m,simp)
       by (metis (no_types, lifting) delayFun.rep_eq tsconc_delayfun tsdropwhile_delayfun tsntimes.simps(2))
     show ?thesis 
       apply (subst h1)
       apply (subst(3) h1)
       apply (subst h2)
       apply (subst(3) h2)
       apply (simp add: assms(3) h3 h4 tsdropfirstmsg_mlscons tsdropwhile_t)
       using False assms(1) h4_1_hh by blast
  qed
   
lemma h4: assumes "tsAbs\<cdot>i \<noteq> \<epsilon>" " #\<surd> as = \<infinity>" shows "\<exists> (i2::'a tstream) ack2. (#(tsAbs\<cdot>(tsSnd_h\<cdot>(i::'a tstream)\<cdot>as\<cdot>(Discr ack)))
   \<ge> #(tsAbs\<cdot>(tsSnd_h\<cdot>i2\<cdot>(tsDropWhile\<cdot>(Discr (shd (tsAbs\<cdot>as)))\<cdot>as)\<cdot>(Discr ack2)))) \<and> (lnsuc\<cdot>(#(tsAbs\<cdot>i2)) \<ge> #(tsAbs\<cdot>i))"
  apply (case_tac "shd (tsAbs\<cdot>as) = ack",simp_all)
  apply (rule_tac x="tsDropFirstMsg\<cdot>i" in exI)
  apply (rule conjI)
  apply (rule_tac x="(\<not>ack)" in exI)
  apply (simp add: assms h4_1)
  apply (simp add: assms srt_decrements_length tsdropFirstMsg_tsabs)
  apply (rule_tac x="i" in exI)
  apply (rule conjI)
  apply (rule_tac x="ack" in exI)
  by (simp add: h4_2)+  

lemma h6_h:"0 < k \<Longrightarrow> Fin k < #(tsAbs\<cdot>i) \<Longrightarrow> lnsuc\<cdot>(#(tsAbs\<cdot>i2)) \<ge> #(tsAbs\<cdot>i) \<Longrightarrow> Fin (k - Suc 0) < #(tsAbs\<cdot>i2)"
  by (metis Fin_Suc Fin_leq_Suc_leq Suc_pred less_imp_neq less_le_trans lnle2le order.not_eq_order_implies_strict)

lemma h6_hh:"(\<And>acks (is::'a tstream) acka n. s = srcdups\<cdot>(tsAbs\<cdot>acks) \<Longrightarrow> #(srcdups\<cdot>(tsAbs\<cdot>acks)) = Fin n \<Longrightarrow>
           Fin n < #(tsAbs\<cdot>is) \<Longrightarrow> #\<surd> acks = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>is\<cdot>acks\<cdot>(Discr acka))) = \<infinity>) \<Longrightarrow>
       \<up>a \<bullet> s = \<up>(shd (tsAbs\<cdot>as)) \<bullet> srcdups\<cdot>(tsAbs\<cdot>(tsDropWhile\<cdot>(Discr (shd (tsAbs\<cdot>as)))\<cdot>as)) \<Longrightarrow>
       #(srcdups\<cdot>(tsAbs\<cdot>(tsDropWhile\<cdot>(Discr (shd (tsAbs\<cdot>as)))\<cdot>as))) =
       Fin (k - Suc 0) \<Longrightarrow> Fin k < #(tsAbs\<cdot>i) \<Longrightarrow> #\<surd> as = \<infinity> \<Longrightarrow> tsAbs\<cdot>as \<noteq> \<epsilon> \<Longrightarrow> 0 < k \<Longrightarrow>
       #(tsAbs\<cdot>(tsSnd_h\<cdot>(i2::'a tstream)\<cdot>(tsDropWhile\<cdot>(Discr (shd (tsAbs\<cdot>as)))\<cdot>as)\<cdot>(Discr ack2)))
       \<le> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) \<Longrightarrow> lnsuc\<cdot>(#(tsAbs\<cdot>i2)) >= #(tsAbs\<cdot>i) \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = \<infinity>"
  by (metis h6_h inf_less_eq inject_scons tsdropwhile_tstickcount)

lemma h6: "(\<And>acks is acka n. s = srcdups\<cdot>(tsAbs\<cdot>acks) \<Longrightarrow> #(srcdups\<cdot>(tsAbs\<cdot>acks)) = Fin n \<Longrightarrow>
           #(srcdups\<cdot>(tsAbs\<cdot>acks)) < #(tsAbs\<cdot>(is::'a tstream)) \<Longrightarrow> #\<surd> acks = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>is\<cdot>acks\<cdot>(Discr acka))) = \<infinity>) \<Longrightarrow>
       \<up>a \<bullet> s = srcdups\<cdot>(tsAbs\<cdot>as) \<Longrightarrow> #(srcdups\<cdot>(tsAbs\<cdot>as)) = Fin k \<Longrightarrow>
       #(srcdups\<cdot>(tsAbs\<cdot>as)) < #(tsAbs\<cdot>(i::'a tstream)) \<Longrightarrow> #\<surd> as = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = \<infinity>"
  apply (case_tac "tsAbs\<cdot>as = \<epsilon>",simp_all)
  apply (simp add: srcdups_step_tsabs tsdropwhile_tsabs)
  apply (case_tac "k = 0",simp_all)
  apply (simp add: lnsuc_fin [of k])
  using h4[of i as ack] empty_is_shortest  h6_hh by blast

lemma tssnd_fmsg2inftrans: assumes "#(srcdups\<cdot>(tsAbs\<cdot>as)) = Fin k" "#(srcdups\<cdot>(tsAbs\<cdot>as)) < #(tsAbs\<cdot>i)" " #\<surd> as = \<infinity>" shows "#(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = \<infinity>"
  using assms apply(induction "(srcdups\<cdot>(tsAbs\<cdot>as))" arbitrary: i as ack k rule: finind)
  using assms apply simp
  apply (case_tac "tsAbs\<cdot>i = \<epsilon>",simp)
  using tssnd_h_inftick_slen nmsg_inftick srcdups_nbot apply auto[1]
  using h6 by blast

lemma tssnd_nack2inftrans: 
  "#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> #\<surd>as = \<infinity> \<Longrightarrow>  #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = \<infinity>"
  apply (case_tac "#(tsAbs\<cdot>(tsRemDups\<cdot>as)) = \<infinity>",simp)
  using ninf2Fin [of "#(tsAbs\<cdot>(tsRemDups\<cdot>as))"] apply auto
  apply(simp add: tsremdups_tsabs)
  by (simp add: tssnd_fmsg2inftrans)

end