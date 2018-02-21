theory Miscellaneous
imports "../../TStream"

begin

(* ----------------------------------------------------------------------- *)
section {* le *}
(* ----------------------------------------------------------------------- *)

lemma not_le_zero_eq:"\<not> 0 < #x \<Longrightarrow> #x = 0"
  using gr_0 slen_empty_eq srt_decrements_length by blast  


(* ----------------------------------------------------------------------- *)
section {* lnsuc *}
(* ----------------------------------------------------------------------- *)

lemma lnsuc_fin: "k \<noteq> 0 \<Longrightarrow> lnsuc\<cdot>n = Fin k \<equiv> n = Fin (k-1)"
  by (induction k,simp_all)

lemma min_lnsuc:"lnsuc\<cdot>x = min (lnsuc\<cdot>y)(lnsuc\<cdot>z) \<Longrightarrow> x = min y z"
  by (metis inject_lnsuc lnsuc_lnle_emb min_def)

(* ----------------------------------------------------------------------- *)
section {* lub *}
(* ----------------------------------------------------------------------- *)

lemma lub_mono_const_leq: "\<lbrakk>chain (X::nat\<Rightarrow>lnat);  \<And>i. X i \<le> y\<rbrakk> \<Longrightarrow> (\<Squnion>i. X i) \<le> y"
  using lnle_conv lub_below by blast

lemma lub_mono_const_ge: "\<lbrakk>chain (X::nat\<Rightarrow>lnat);  \<And>i. X i > y\<rbrakk> \<Longrightarrow> (\<Squnion>i. X i) > y"
  by (metis inf_ub l42 leD less_le unique_inf_lub)

(* ----------------------------------------------------------------------- *)
section {* slen *}
(* ----------------------------------------------------------------------- *)

lemma slen_scons2: "#b \<le> #(a \<bullet> b)" 
  apply (induction b arbitrary: a rule: ind,simp_all) 
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
  by (metis (no_types, lifting) assoc_sconc le_cases lnsuc_lnle_emb sconc_fst_empty slen_scons 
      surj_scons)

(* ----------------------------------------------------------------------- *)
section {* sdrop *}
(* ----------------------------------------------------------------------- *)

lemma sdrop_empty:"#as \<noteq> \<infinity> \<Longrightarrow> lntake n\<cdot>(#as) = (#as) \<Longrightarrow> sdrop n\<cdot>as = \<epsilon>"
  apply(induction n arbitrary: as)
  apply simp
  using lnzero_def slen_empty_eq apply auto[1]
  by (smt fold_inf inject_lnsuc lntake_more sdrop_forw_rt srt_decrements_length strict_sdrop)

(* ----------------------------------------------------------------------- *)
section {* shd *}
(* ----------------------------------------------------------------------- *)

lemma smap_shd: "s\<noteq>\<epsilon> \<Longrightarrow> shd (smap f\<cdot>s) = f (shd s)"
  by (simp add: smap_hd_rst) 

lemma sfilter_shd: "s\<noteq> \<epsilon> \<Longrightarrow> shd s \<in> X \<Longrightarrow> shd (X \<ominus> s) = shd s"
  by (rule_tac x=s in scases,simp_all)

(* ----------------------------------------------------------------------- *)
section {* lshd *}
(* ----------------------------------------------------------------------- *)

lemma lshd_shd: "s\<noteq>\<epsilon> \<Longrightarrow> lshd\<cdot>s = updis (shd s)"
  by (metis lshd_updis surj_scons)

lemma lshd_below: "lshd\<cdot>ys = updis a \<and> xs \<sqsubseteq> ys \<and> xs \<noteq> \<bottom> \<Longrightarrow> lshd\<cdot>xs = updis a"
  using lshd_eq by fastforce  

(* ----------------------------------------------------------------------- *)
section {* sdropwhile *}
(* ----------------------------------------------------------------------- *)

(* Warum nle? *)
lemma sdropwhile_nle:"#(sdropwhile f\<cdot>as) \<le> #as"
  apply(induction as arbitrary: f,simp_all)
  apply(rule adm_all)
  apply (metis (mono_tags, lifting) admI inf_chainl4 inf_ub lub_eqI lub_finch2)
  by (smt less_lnsuc order_eq_iff sdropwhile_f sdropwhile_t slen_scons stream.con_rews(2) 
      stream.sel_rews(5) surj_scons trans_lnle)

lemma sdropwhile_sfoot_empty:"#s < \<infinity> \<Longrightarrow>  sfoot s = sfoot (sdropwhile f\<cdot>s) \<or> sdropwhile f\<cdot>s = \<epsilon>"
  by (metis inf_ub lnless_def order_less_le sconc_fst_inf sfoot_conc slen_sconc_snd_inf 
      stakewhileDropwhile)
  
lemma sdropwhile_nempty_empty:"#as < \<infinity> \<and>(\<exists>x. as = x \<bullet> \<up>a) 
      \<Longrightarrow> \<exists>t. (sdropwhile f\<cdot>as) = t \<bullet> \<up>a \<or> (sdropwhile f\<cdot>as) = \<epsilon>"
  by (metis fold_inf lnsuc_lnle_emb not_le sdropwhile_sfoot_empty sfoot12 sfoot2 slen_lnsuc)

lemma sdropwhile_le:" #as\<noteq>\<infinity> \<Longrightarrow>  as\<noteq>\<epsilon> \<Longrightarrow> f (shd as) \<Longrightarrow> #(sdropwhile f\<cdot>as) < #as"   
  apply(rule_tac x=as in scases,simp_all)
  by (smt inf_ub leD ln_less order_less_le sdropwhile_nle trans_lnle)

lemma sdropwhile_lub:"\<And>Y. chain Y \<Longrightarrow>\<forall>i. sdropwhile f\<cdot>(Y i) = \<epsilon> \<Longrightarrow> sdropwhile f\<cdot>(\<Squnion>i. Y i) = \<epsilon> "
  by(simp add: contlub_cfun_arg contlub_cfun_fun)

lemma sdropwhile_sdrop:" #as \<noteq> \<infinity> \<Longrightarrow>\<exists>n. sdropwhile f\<cdot>as = sdrop n\<cdot>as"
proof -  
  assume a0:"#as\<noteq> \<infinity>"
  have h0:"\<exists>n. #(stakewhile f\<cdot>as) = Fin n"
    by (meson a0 dual_order.strict_trans2 inf_ub less_le lnat_well_h2 stakewhile_less)
  then show ?thesis
    using stakewhile_sdropwhilel1 by blast
qed

lemma sdropwhile_all_h1:"u \<noteq> \<bottom> \<Longrightarrow> (\<And>f. \<forall>x. x \<in> sdom\<cdot>as \<longrightarrow> f x \<Longrightarrow> sdropwhile f\<cdot>as = \<epsilon>) 
    \<Longrightarrow>  \<forall>x. x \<in> sdom\<cdot>(u && as) \<longrightarrow> f x \<Longrightarrow> sdropwhile f\<cdot>(u && as) = \<epsilon>"    
proof-
  assume a0:"u \<noteq> \<bottom>"
  assume a1:"(\<And>f. \<forall>x. x \<in> sdom\<cdot>as \<longrightarrow> f x \<Longrightarrow> sdropwhile f\<cdot>as = \<epsilon>)"
  assume a2:"\<forall>x. x \<in> sdom\<cdot>(u && as) \<longrightarrow> f x"
  have h0:" \<forall>x. x \<in> sdom\<cdot>as \<longrightarrow> f x \<Longrightarrow> sdropwhile f\<cdot>as = \<epsilon>"
    using a1 by blast
  have h1:"sdropwhile f\<cdot>(u && as) = sdropwhile f\<cdot>(as)"
    by (metis a0 a2 sdropwhile_t sfilter_ne_resup sfilter_sdoml4 stream.con_rews(2) 
        stream.sel_rews(5) surj_scons)
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
    by (smt ex_snth_in_sfilter_nempty lnat.con_rews lnzero_def sdropwhile_all singletonD 
        slen_empty_eq strdw_filter_h)
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
    by (smt ex_snth_in_sfilter_nempty lnat.con_rews lnzero_def sdropwhile_all singletonD 
        slen_empty_eq strdw_filter_h)
  have h4:"#as < \<infinity> \<Longrightarrow> #(sdropwhile f\<cdot>as) < \<infinity> "
    by (meson sdropwhile_nle leD leI trans_lnle)
  then show ?thesis
    using a1 a2 h0 h1 h3 by blast
qed

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
  
lemma ts_well_sdropwhile:assumes "ts_well as" shows "ts_well(sdropwhile f\<cdot>as)"
  apply(simp add: ts_well_def,auto)
  using ts_well_sdropwhile_1 assms apply blast
  using ts_well_sdropwhile_2 assms by blast

(*
lemma sdropwhile_well: assumes "ts_well s" shows "ts_well (sdropwhile f\<cdot>s)"
  apply (cases "#(stakewhile f\<cdot>s)" rule: lncases)
  apply (simp add: stakewhile_sdropwhilel2) 
  by (simp add: assms stakewhile_sdropwhilel1)*)

lemma cont_sdopwhile_tsabs:"cont(\<lambda>as. tsAbs\<cdot>(Abs_tstream ((sdropwhile f\<cdot>(Rep_tstream as)))))"
  by(simp add: ts_well_sdropwhile)

(* helper lemma for sdropwhile_tsabs *)
lemma cont_h:"chain Y \<Longrightarrow> 
  (\<Squnion>i::nat. tsAbs\<cdot>(Abs_tstream (sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)\<cdot>(Rep_tstream (Y i))))) 
  = tsAbs\<cdot>(Abs_tstream (sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)\<cdot>(Rep_tstream (\<Squnion>i::nat. Y i))))"
proof-
  assume a0:"chain Y"
  have h0:"cont(\<lambda>as. tsAbs\<cdot>(Abs_tstream ((sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)
            \<cdot>(Rep_tstream as)))))"
    by (simp add: cont_sdopwhile_tsabs )
  then show ?thesis
    by (smt a0 cont2contlubE lub_eq)
qed

lemma sdropwhile_tsabs: "sdropwhile (\<lambda> x. x=a)\<cdot>(tsAbs\<cdot>(as::'a tstream)) 
      = tsAbs\<cdot>(Abs_tstream (sdropwhile (\<lambda> x. x= Msg a \<or> x=\<surd>)\<cdot>(Rep_tstream as)))"
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

lemma sfilter_dwl1_inv: 
  "sfilter X\<cdot>p = sfilter X\<cdot>(sdropwhile (\<lambda>x. x\<notin>X)\<cdot>p)"
by simp

lemma cont_srt_sdropwhile:"cont(\<lambda>as. (Abs_tstream (srt\<cdot>(sdropwhile f\<cdot>(Rep_tstream as)))))"
  by(simp add: ts_well_sdropwhile)  

(* ----------------------------------------------------------------------- *)
section {* stakewhile *}
(* ----------------------------------------------------------------------- *)

lemma stakewhile_stimes: 
  "#(stakewhile (\<lambda>x. x=t)\<cdot>z) = Fin n \<longrightarrow> stakewhile (\<lambda>x. x=t)\<cdot>z = sntimes n (\<up>t)"
  apply (induction n arbitrary:z t,simp)
  apply (rule_tac x=z in scases,simp)
  by (case_tac "a = t",simp_all)

(* ----------------------------------------------------------------------- *)
section {* sntimes *}
(* ----------------------------------------------------------------------- *)

lemma sntimes_fin: "#s < \<infinity> \<Longrightarrow> #(n \<star> s) < \<infinity>" 
  apply (induction n,simp_all)
  by (metis fold_inf)

(* ----------------------------------------------------------------------- *)
section {* scons *}
(* ----------------------------------------------------------------------- *)

lemma sconc_scons2: "s1 \<bullet> (s2 \<bullet> s3) = (s1 \<bullet> s2) \<bullet> s3"
  by simp 

(* ----------------------------------------------------------------------- *)
section {* stake *}
(* ----------------------------------------------------------------------- *)

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

(* ----------------------------------------------------------------------- *)
section {* srcdups *}
(* ----------------------------------------------------------------------- *)

lemma srcdups_slen_leq: "#(srcdups\<cdot>s) \<le> #(srcdups\<cdot>(\<up>t \<bullet> s))"
  proof(induction s arbitrary: t rule: ind)
    case 1
    then show ?case
    apply (rule adm_all)
    apply (rule admI)
    by (simp add: contlub_cfun_arg lub_mono2)
  next
    case 2
    then show ?case
    by simp
  next
    case (3 u s)
    then show ?case
    by (metis (no_types, lifting) eq_iff slen_scons2 srcdups_eq srcdups_neq)
  qed

lemma srcdups_slen_conc_leq: "#(srcdups\<cdot>(\<up>a \<bullet> s)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> \<up>t \<bullet> s))"
  apply (case_tac "a = t", simp_all)
  proof(induction s arbitrary: a t rule: ind)
    case 1
    then show ?case 
      apply (rule adm_all)+
      apply (rule admI)
      by (simp add: contlub_cfun_arg lub_mono2)
  next
    case 2
    then show ?case
       by (simp add: srcdups_step)
  next
    case (3 b s)
    then show ?case
      proof (cases "t=b")
        case True
        then show ?thesis
        using "3.prems" by auto
      next
        case False
        then show ?thesis
        proof (cases "b=a")
          case True
          then show ?thesis
            by (metis (no_types, lifting) less_lnsuc srcdups_eq srcdups_slen_leq trans_lnle)
        next
          case False
          then show ?thesis
            using srcdups_slen_leq by force
        qed
      qed
  qed      

(* ----------------------------------------------------------------------- *)
section {* mlscons *}
(* ----------------------------------------------------------------------- *)

lemma mlscons_conc_delay_bottom: "(updis msg &&\<surd> (delay \<bottom>)) \<bullet>\<surd> ts=  updis msg &&\<surd> delay ts"
  by (simp add: delayFun_def tsconc_mlscons)

(* ----------------------------------------------------------------------- *)
section {* misc *}
(* ----------------------------------------------------------------------- *)

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
 have h10: "Rep_tstream as= Rep_tstream tsInfTick" by (simp add: h6 h7 tstickcount_insert 
        tsInfTick.rep_eq sinf_snt2eq)
show ?thesis using Rep_tstream_inject h10 by auto
qed

lemma rep_tstream_delayfun: "Rep_tstream (delay ts) = \<up>\<surd> \<bullet> (Rep_tstream ts)"
  by (simp add: delayFun.rep_eq tsconc_rep_eq) 

lemma tick_split: "Fin x \<le> #(stakewhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream as)) \<Longrightarrow> 
    as = tsntimes x (Abs_tstream (\<up>\<surd>)) \<bullet>\<surd> Abs_tstream (sdrop x\<cdot>(Rep_tstream as))"
  apply (induction x arbitrary:as,simp_all)
  apply (rule_tac xs=as in tstream_exhaust,simp_all)
  apply (simp add: rep_tstream_delayfun)
  apply (metis delayfun_insert tsconc_assoc)
  by (simp add: tsmlscons_lscons2 lscons_conv)

lemma msg_inversmsg: "a \<noteq> \<surd> \<Longrightarrow> \<M> \<M>\<inverse> a = a"
  by (metis (no_types) event.exhaust event.simps(4)) 

(* ----------------------------------------------------------------------- *)
section {* tstickcount *}
(* ----------------------------------------------------------------------- *)

lemma slen_tstickcount: "#\<surd>(ts) < \<infinity> \<Longrightarrow> #(Rep_tstream ts) < \<infinity>"
  by simp

(* ----------------------------------------------------------------------- *)
section {* tsabs *}
(* ----------------------------------------------------------------------- *)

lemma tsabs_tsconc_tsinftick:"tsAbs\<cdot>(as \<bullet>\<surd> tsInfTick) = tsAbs\<cdot>(as)"
  apply(induction as)
  apply(rule admI)
  using l42 apply force
  apply simp
  apply (simp add: tsconc_delayfun)
  by (metis below_bottom_iff ts_tsconc_prefix tsabs_mlscons tsconc_mlscons)

(* ----------------------------------------------------------------------- *)
section {* tsntimes *}
(* ----------------------------------------------------------------------- *)

lemma tsntimes_minus: "x\<noteq>0 \<Longrightarrow> tsntimes x ts = ts \<bullet>\<surd> (tsntimes (x-1) ts)"
  by (metis Suc_diff_1 not_gr_zero tsntimes.simps(2))

lemma tsntimes_tsabs: "tslen\<cdot>ts < \<infinity> \<Longrightarrow>tsAbs\<cdot>(tsntimes n ts) = sntimes n (tsAbs\<cdot>ts)" 
  apply (induction n,simp_all)
  by (simp add: tsabs_conc tslen_def)

lemma tsntimes_rep_tstream: "Rep_tstream (tsntimes n ts) = sntimes n (Rep_tstream ts)" 
  apply (induction n,simp_all)
  by (metis Abs_Rep ts_well_Rep tsconc_rep_eq)

(* ----------------------------------------------------------------------- *)
section {* tsLshd *}
(* ----------------------------------------------------------------------- *)

lemma tslshd_tsrt: "ts = tsLshd\<cdot>ts &\<surd> tsRt\<cdot>ts" 
  apply (rule_tac ts=ts in tscases,simp_all)
  apply (metis tslscons_bot tslscons_lshd)
  apply (simp add: delayfun_tslscons tick_eq_discrtick)
  by (metis tslscons_bot tslscons_lshd tslscons_srt tsmlscons_bot2 tsmlscons_lscons)

(* ----------------------------------------------------------------------- *)
section {* tslscons *}
(* ----------------------------------------------------------------------- *)

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
      by (metis (no_types, lifting) DiscrTick_def assms event.exhaust event.simps(4) 
          tsmlscons2tslscons) 
  qed

(* ----------------------------------------------------------------------- *)
section {* tsDropWhileTick *}
(* ----------------------------------------------------------------------- *)

fixrec tsDropWhileTick :: "'a tstream \<rightarrow> 'a tstream" where
"tsDropWhileTick\<cdot>\<bottom> = \<bottom>" |
"tsDropWhileTick\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) =(tsDropWhileTick\<cdot>ts)" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsDropWhileTick\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = tsMLscons\<cdot>(up\<cdot>t)\<cdot>ts"

lemma tsdropwhiletick_delayfun:"tsDropWhileTick\<cdot>(delayFun\<cdot>msg) = tsDropWhileTick\<cdot>msg"
  by (simp add: delayfun_tslscons)

lemma tsdropwhiletick_mlscons:"ts \<noteq> \<bottom> \<Longrightarrow> tsDropWhileTick\<cdot>(updis t &&\<surd> ts) = updis t &&\<surd> ts"
  by (simp add: tsmlscons_lscons)

lemma tsdropwhiletick_sdropwhile: "tsDropWhileTick\<cdot>ts = 
            (Abs_tstream (sdropwhile (\<lambda>x. x = \<surd>)\<cdot>(Rep_tstream ts)))"
  apply (induction ts, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg cont2contlubE)
  apply (smt Abs_tstream_inject Rep_tstream_inverse lub_eq lub_tstream mem_Collect_eq 
          monofun_cfun_arg po_class.chain_def ts_well_sdropwhile ts_well_Rep) 
  apply (metis (mono_tags, lifting) delayFun.abs_eq delayfun_tslscons eta_cfun sdropwhile_t tick_msg 
          tsDropWhileTick.simps(2) tsconc_rep_eq)
  by (metis (mono_tags, lifting) Abs_Rep event.distinct(1) lscons_conv sdropwhile_f 
          tsDropWhileTick.simps(3) tsmlscons_lscons tsmlscons_lscons2)

lemma tsdropwhiletick_shd: "tsAbs\<cdot>i \<noteq> \<epsilon> \<Longrightarrow> unpackMsg\<cdot>(tsLshd\<cdot>(tsDropWhileTick\<cdot>i)) = (lshd\<cdot>(tsAbs\<cdot>i))" 
  apply (induction i,simp_all)
  apply (simp add: delayfun_tslscons)
  apply (simp add: tsdropwhiletick_mlscons tsabs_mlscons)
  by(simp add: tsmlscons2tslscons unpackMsg_def)

lemma tsdropwhiletick_tslshd_imp: "tsLshd\<cdot>(tsDropWhileTick\<cdot>i) \<noteq> up\<cdot>DiscrTick"
  apply (induction i,simp_all)
  apply (metis tslscons_nbot3 tslshd_tsrt)
  apply (simp add: tsdropwhiletick_delayfun)
  apply (simp add: tsdropwhiletick_mlscons tsmlscons_lscons)
  by (metis (no_types) tslscons_nbot3 tsmlscons_lscons tsmlscons_nbot_rev)

lemma tsDropwhileTick_tsrt_nbot: "tsAbs\<cdot>i \<noteq> \<epsilon> \<Longrightarrow> tsRt\<cdot>(tsDropWhileTick\<cdot>i) \<noteq> \<bottom>" 
  apply (induction i,simp_all)
  apply (simp add: tsdropwhiletick_delayfun)
  by (simp add: tsdropwhiletick_mlscons tsmlscons_lscons)

(* ----------------------------------------------------------------------- *)
section {* tsDropFirstMsg *}
(* ----------------------------------------------------------------------- *)

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

lemma srcdups_step_tsabs: "tsAbs\<cdot>as \<noteq> \<epsilon> \<Longrightarrow> srcdups\<cdot>(tsAbs\<cdot>as) 
      = \<up>(shd (tsAbs\<cdot>as)) \<bullet> srcdups\<cdot>(sdropwhile (\<lambda> x. x= (shd (tsAbs\<cdot>as)))\<cdot>(tsAbs\<cdot>as))"
  by (metis srcdups_eq srcdups_step surj_scons)

(* ----------------------------------------------------------------------- *)
section {* tsDropFirst2 *}
(* ----------------------------------------------------------------------- *)

fixrec tsDropFirst2 :: " 'a tstream \<rightarrow> 'a tstream" where
"tsDropFirst2\<cdot>\<bottom> = \<bottom>" |
"tsDropFirst2\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = (tsDropFirst2\<cdot>ts)" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsDropFirst2\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = ts"

lemma tsdropfirst2_mlscons:"i \<noteq> \<bottom> \<Longrightarrow> tsDropFirst2\<cdot>(updis t &&\<surd> i) = i"
  by (simp add: tsmlscons_lscons)
  
lemma tsdropfirst2_delayfun:"tsDropFirst2\<cdot>(delayFun\<cdot>i) = tsDropFirst2\<cdot>i"
  by (simp add: delayfun_tslscons)

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



(* ----------------------------------------------------------------------- *)
section {* tsTickDrop *}
(* ----------------------------------------------------------------------- *)

fixrec tsTickDrop :: " 'a tstream \<rightarrow> 'a tstream" where
"tsTickDrop\<cdot>\<bottom> = \<bottom>" |
"tsTickDrop\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = (tsTickDrop\<cdot>ts)" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsTickDrop\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = tsMLscons\<cdot>(up\<cdot>t)\<cdot>ts"

lemma tstickdrop_mlscons:"i \<noteq> \<bottom> \<Longrightarrow> tsTickDrop\<cdot>(updis t &&\<surd> i) = (updis t &&\<surd> i)"
  by (simp add: tsmlscons_lscons)  

lemma tstickdrop_delayfun:"tsTickDrop\<cdot>(delayFun\<cdot>i) = tsTickDrop\<cdot>i"
  by (simp add: delayfun_tslscons)

lemma tsabs_tstickdrop:"tsAbs\<cdot>(tsTickDrop\<cdot>as) = tsAbs\<cdot>as"
  apply(induction as,simp_all)
  apply(simp add: tstickdrop_delayfun)
  by(simp add: tstickdrop_mlscons)

lemma tstickdrop_nempty:" lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>tsTickDrop\<cdot>as = updis(ack)&&\<surd>tsDropFirst2\<cdot>as" 
  apply(simp add: tsremdups_tsabs tsprojfst_tsabs)
  apply(induction as arbitrary: ack,simp_all)
  apply(simp add: tsdropfirst2_delayfun tstickdrop_delayfun)
  apply(simp add: tsdropfirst2_mlscons tstickdrop_mlscons tsabs_mlscons)
  by (metis stream.sel_rews(4) tsremdups_h_tsabs) 

(* ----------------------------------------------------------------------- *)
section {* tsDropFirst3 *}
(* ----------------------------------------------------------------------- *)

fixrec tsDropFirst3 :: " 'a tstream \<rightarrow> 'a tstream" where
"tsDropFirst3\<cdot>\<bottom> = \<bottom>" |
"tsDropFirst3\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = (tsDropFirst3\<cdot>ts)" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsDropFirst3\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = tsTickDrop\<cdot>ts"

lemma tsdropfirst3_mlscons:"i \<noteq> \<bottom> \<Longrightarrow> tsDropFirst3\<cdot>(updis t &&\<surd> i) = tsTickDrop\<cdot>i"
  by (simp add: tsmlscons_lscons)
  
lemma tsdropfirst3_delayfun:"tsDropFirst3\<cdot>(delayFun\<cdot>i) = tsDropFirst3\<cdot>i"
  by (simp add: delayfun_tslscons)

lemma tsdropfirst3_rt:"(tsAbs\<cdot>(tsDropFirst3\<cdot>i)) = srt\<cdot>(tsAbs\<cdot>i)"
  apply(induction i,simp_all)
  apply(simp add: tsdropfirst3_delayfun)
  by(simp add: tsdropfirst3_mlscons tsabs_mlscons tsabs_tstickdrop)
    
lemma tsdropfirst3_first:"tsAbs\<cdot>i = \<up>a \<bullet> s \<Longrightarrow> (tsAbs\<cdot>(tsDropFirst3\<cdot>i)) = s"
  by (simp add: tsdropfirst3_rt)

lemma tsdropfirst3_le_eq:"#(tsAbs\<cdot>(tsDropFirst3\<cdot>i)) \<le> #(tsAbs\<cdot>i)"
  apply(induction i,simp_all)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (meson lnle_conv lub_mono monofun_cfun_arg po_class.chain_def)  
  apply (simp add: tsdropfirst3_delayfun)
  apply(simp add: tsdropfirst3_mlscons)
  by (metis (no_types, lifting) less_lnsuc lscons_conv slen_scons tsabs_mlscons tsdropfirst3_first tsdropfirst3_mlscons)

lemma tsdropfirst3_le:"(tsAbs\<cdot>i) \<noteq> \<bottom> \<Longrightarrow> lnsuc\<cdot>(#(tsAbs\<cdot>(tsDropFirst3\<cdot>i))) = #(tsAbs\<cdot>i)"
  apply(induction i,simp_all)
  apply(simp add: tsdropfirst3_delayfun)
  apply(simp add: tsdropfirst3_mlscons tsabs_mlscons lscons_conv)
  by (simp add: tsabs_tstickdrop)
  
(* ----------------------------------------------------------------------- *)
section {* tsDropWhile2 *}
(* ----------------------------------------------------------------------- *)

fixrec tsDropWhile2 :: "'a discr \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsDropWhile2\<cdot>a\<cdot>\<bottom> = \<bottom>" |
"tsDropWhile2\<cdot>a\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = tsDropWhile2\<cdot>a\<cdot>ts" |
"ts \<noteq> \<bottom> \<Longrightarrow> tsDropWhile2\<cdot>a\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = 
  (if t = a then tsDropWhile2\<cdot>a\<cdot>ts else tsMLscons\<cdot>(up\<cdot>t)\<cdot>ts)"

lemma tsdropwhile2_delayfun: "tsDropWhile2\<cdot>a\<cdot>(delayFun\<cdot>as) = (tsDropWhile2\<cdot>a\<cdot>as)"
  by (simp add: delayfun_tslscons) 

lemma tsdropwhile2_t: "tsDropWhile2\<cdot>(Discr a)\<cdot>(updis a &&\<surd> as) = tsDropWhile2\<cdot>(Discr a)\<cdot>as"
  by (metis tsDropWhile2.simps(3) tsmlscons_lscons tsmlscons_nbot_rev)

lemma tsdropwhile2_f: "a \<noteq> b \<Longrightarrow>tsDropWhile2\<cdot>(Discr a)\<cdot>(updis b &&\<surd> as) = updis b &&\<surd> as"
  by (metis discr.inject tsDropWhile2.simps(1) tsDropWhile2.simps(3) tsmlscons_lscons tsmlscons_nbot_rev)

lemma tsdropwhile2_strict: "tsDropWhile2\<cdot>a\<cdot>\<bottom> = \<bottom>"
  by simp

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

(* proof needs tsdropwhile2*)
lemma tsdropfirts2_sdropwhile:"(Abs_tstream (srt\<cdot>(sdropwhile (\<lambda> x. x=\<surd>)\<cdot>(Rep_tstream as)))) = tsDropFirst2\<cdot>as"
  apply(induction as,simp_all)
  apply(rule admI)
  apply(simp add: contlub_cfun_arg contlub_cfun_fun tsdropfirst2_sdropwhile_adm_h)
  apply(simp add: tsdropfirst2_delayfun)
  apply (simp add: tsdropwhile2_delayfun delayFun.rep_eq tsconc_rep_eq)
  apply(simp add: tsdropfirst2_mlscons)
  by(simp add: lscons_conv tsmlscons_lscons2)

(* proof needs lemma before *)
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

lemma cont_sdropwhile_tsabs2:"cont(\<lambda>as. (Abs_tstream (sdropwhile f\<cdot>(Rep_tstream as))))"
  by(simp add: ts_well_sdropwhile)    
    
lemma tsdropwhile2_sdropwhile_adm_h:"chain Y \<Longrightarrow> 
(Abs_tstream (sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)\<cdot>(Rep_tstream (\<Squnion>i::nat. Y i)))) =
(\<Squnion>i::nat. (Abs_tstream (sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)\<cdot>(Rep_tstream (Y i))))) "
proof-
  assume a0:"chain Y"
  have h0:"cont(\<lambda>as. (Abs_tstream (sdropwhile (\<lambda>xa::'a event. xa = \<M> x \<or> xa = \<surd>)\<cdot>(Rep_tstream as))))"
    by (simp add: cont_sdropwhile_tsabs2)
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

end