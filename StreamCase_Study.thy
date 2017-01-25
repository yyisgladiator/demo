(*  Title:        StreamCase_Study.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Some Testing with streams 
                  And definition of the "add" function
*)


theory StreamCase_Study


imports Streams
begin



(* sntimes Tests *)

definition K :: "nat \<Rightarrow> nat stream" where (* {\<up>8, \<up>8\<bullet>\<up>8,..} *)
"K = (\<lambda>i. sntimes i (\<up>8))" 

lemma v0: "sntimes i (\<up>8) \<sqsubseteq> \<up>8 \<bullet> sntimes i (\<up>8)"
  apply (induct_tac i)
   apply simp
  by (simp add: monofun_cfun_arg)

lemma v1: "chain K" (* {\<up>8 \<sqsubseteq> \<up>8\<bullet>\<up>8 \<sqsubseteq> ...} *)
  apply (simp add: K_def)
  apply (simp add: chain_def)
  by (simp add: v0)

lemma v2: "\<up>8\<infinity> = (\<Squnion> i. K i)"
  by (simp add: K_def sntimesLub)  (* \<Squnion>{\<up>8 \<sqsubseteq> \<up>8\<bullet>\<up>8 \<sqsubseteq> ...} = \<up>8\<infinity>*)

lemma v3: assumes "chain C"
  shows "chain (\<lambda>i. smap g\<cdot>(C i))"
  using assms by auto (* {\<up>9 \<sqsubseteq> \<up>9\<bullet>\<up>9 \<sqsubseteq> ...} *)

lemma smap1: "smap f\<cdot>(\<up>x) = \<up>(f x)"
  by simp

lemma v4: "\<up>9\<infinity> = (\<Squnion> i. smap Suc\<cdot>(K i))"
  by (metis contlub_cfun_arg numeral_eq_Suc pred_numeral_simps(3) smap1 smap2sinf v1 v2)
 (* \<Squnion>{\<up>9 \<sqsubseteq> \<up>9\<bullet>\<up>9 \<sqsubseteq> ...} = \<up>9\<infinity>*)

(* cont (\<lambda>x. smap Suc\<cdot>x) *)
lemma v5: "\<forall>Y. chain Y \<longrightarrow> smap Suc\<cdot>(\<Squnion> i. Y i) = (\<Squnion> i. smap Suc\<cdot>(Y i))"
  by (simp add: contlub_cfun_arg)

lemma v6: "smap Suc\<cdot>(\<Squnion> i. K i) = (\<Squnion> i. smap Suc\<cdot>(K i))"
  by (simp add: v1 v5)

lemma v7: "smap Suc\<cdot>\<up>8\<infinity> = \<up>9\<infinity>"
  by (simp add: v2 v4 v6)

(*TODO: Generalisiere für alle x: *)
lemma l4: "smap Suc\<cdot>\<up>x\<infinity> = \<up>(Suc x)\<infinity>"
  by simp


(*TODO: Generalisiere für alle x und functionen: *)
lemma l5: "smap g\<cdot>\<up>x\<infinity> = \<up>(g x)\<infinity>"
  by simp

lemma v72: "smap (\<lambda>x. (Suc (Suc x)))\<cdot>(sinftimes (\<up>8)) = (sinftimes (\<up>10))"
  by (simp add: l5)


lemma "smap Suc\<cdot>(<[1,2]>) = (<[2,3]>)"
  by (simp add: eval_nat_numeral(2) numeral_3_eq_3 One_nat_def)


lemma "smap Suc\<cdot>(<[1,2,3]>) = (<[2,3,4]>)"
  by (simp add: eval_nat_numeral(2) numeral_3_eq_3 One_nat_def)

lemma "(map Suc [1, 2, 3, 6, 7, 8]) = [2,3,4,7,8,9]"
  by simp



lemma helperlein: "(map (\<lambda>x. x* 3) [1::nat, 2, 3, 4, 5]) = [3,6,9,12,15]"
  by simp

lemma v8: "smap (\<lambda>x. 3*x)\<cdot>(sinftimes (<[1::nat,2,3,4,5]>)) = (sinftimes (<[3,6,9,12,15]>))"
  by (simp add: smap2sinf)
                






lemma "smap Suc\<cdot>(sinftimes (\<up>13)) = fix\<cdot>(\<Lambda> s. updis 14 && s)"
  by (metis StreamCase_Study.l4 Suc_numeral eta_cfun fix_eq lscons_conv s2sinftimes semiring_norm(5) semiring_norm(8))

lemma "smap Suc\<cdot>(sinftimes (\<up>5)) = sinftimes (\<up>6)"
  by (simp add: smap2sinf)

lemma "smap Suc\<cdot>(\<up>5) = \<up>6"
  by simp



(* Iterate Demos *)

lemma "smap Suc\<cdot>(siterate Suc 0) = (siterate Suc 1)"
  by (smt One_nat_def siterate_smap)

lemma "sdrop 4\<cdot>(siterate Suc 0) = (siterate Suc 4)"
  by (smt add.left_neutral sdrop_siterate)

lemma "smap (\<lambda>x. Suc (Suc x))\<cdot>(siterate Suc 2) = (siterate Suc 4)"
  by (simp add: siterate_smap)

lemma "sdrop 100\<cdot>(siterate Suc 0) = (siterate Suc 100)"
  by (smt add.left_neutral sdrop_siterate)


lemma "sdrop 4\<cdot>(siterate Suc 0) = smap (\<lambda>x. Suc (Suc x))\<cdot>(siterate Suc 2)"
  by (simp add: sdrop_siterate siterate_smap)


lemma "(siterate id 0) = (siterate (\<lambda>x. x ) 0)"
  by (meson id_def)

lemma "sdrop i\<cdot>(siterate id x) = siterate id x"
  by (smt sdrops_sinf siter2sinf)


lemma "siterate (\<lambda>x::nat. 2 *x) 0 = sinftimes (\<up>0)"
  by (smt mult_0_right siter2sinf2)

lemma "siterate (\<lambda>x::nat. x*x) 1 = sinftimes (\<up>1)"
  by (smt nat_1_eq_mult_iff siter2sinf2)


(* Compact Stuff *)

lemma finChainapprox: assumes "chain Y" and "# (\<Squnion>i. Y i) =Fin  k" 
  shows "\<exists>i. Y i = (\<Squnion>i. Y i)"
  using assms(1) assms(2) inf_chainl4 lub_eqI lub_finch2 by fastforce

lemma finCompact: assumes "#s = Fin k"
  shows "compact s"
  proof (rule compactI2)
  fix Y assume as1: "chain Y" and as2: "s \<sqsubseteq> (\<Squnion>i. Y i)"
  show "\<exists>i. s \<sqsubseteq> Y i" by (metis approxl2 as1 as2 assms finChainapprox lub_approx stream.take_below)
qed

lemma "compact \<epsilon>"
  by simp

lemma "compact (\<up>x)"
  by (simp add: sup'_def)

lemma "compact (<[1,2,3,4,5]>)"
  proof (rule finCompact)
  show "#(<[1, 2, 3, 4, 5]>) = Fin 5" by simp
qed


(* nicht so compactes Zeug *)
lemma nCompact: assumes "chain Y" and "\<forall>i. (Y i \<sqsubseteq> x)" and "\<forall>i.  (Y i \<noteq> x)" and "x \<sqsubseteq> (\<Squnion>i. Y i)"
  shows "\<not>(compact x)"
  by (meson assms below_antisym compactD2)

lemma infNCompact: assumes "#s = \<infinity>"
  shows"\<not> (compact s)"
  proof (rule nCompact)
     show "chain (\<lambda>i. stake i\<cdot>s)" by simp
    show "\<forall>i. stake i\<cdot>s \<sqsubseteq> s" by simp
   show "\<forall>i. stake i\<cdot>s \<noteq> s" by (metis Inf'_neq_0 assms fair_sdrop sdropostake strict_slen)
  show "s \<sqsubseteq> (\<Squnion> i. stake i\<cdot>s)" by (simp add: reach_stream)
qed

lemma "\<not> (compact (sinftimes (\<up>x)))"
  by (simp add: infNCompact slen_sinftimes)




definition upApply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a discr u \<rightarrow> 'b discr u" where
"upApply f \<equiv> \<Lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))"


lemma upApply_mono[simp]:"monofun (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
  apply(rule monofunI)
  apply auto[1]
  apply (metis (full_types, hide_lams) Exh_Up discrete_cpo up_below up_inject)
done

lemma upApply_lub: assumes "chain Y"
  shows "((\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))) (\<Squnion>i. Y i))
=(\<Squnion>i. (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))) (Y i))"
apply(rule finite_chain_lub)
apply (simp_all add: assms chfin2finch)
done
 
lemma upApply_cont[simp]:"cont (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
using chfindom_monofun2cont upApply_mono by blast

lemma upApply_rep_eq [simp]: "upApply f\<cdot>(updis a) = updis (f a)"
by(simp add: upApply_def)



fixrec sSuc :: "nat stream \<rightarrow> nat stream" where
"sSuc\<cdot>\<bottom>=\<bottom>" |
"x\<noteq>\<bottom> \<Longrightarrow> sSuc\<cdot>(x&&xs) = (upApply Suc\<cdot>x)&&(sSuc\<cdot>xs)"

lemma sSuc_unfold:  "sSuc\<cdot>(\<up>a \<bullet> as) = \<up>(Suc a) \<bullet> sSuc\<cdot>as"
by (metis lscons_conv sSuc.simps(2) upApply_rep_eq up_defined)

lemma sSuc2smap: "sSuc\<cdot>s = smap Suc\<cdot>s"
  apply(rule ind [of _s])
    apply (simp_all add: sSuc_unfold)
done

lemma "sSuc\<cdot>s = smap Suc\<cdot>s"
  apply(subst rek2smap)
    apply (auto simp add: sSuc_unfold)
done




(* Fingerübung CaseStudy *)

definition fs :: "nat stream" where  (* also fs = 1 2 3 \<dots> *)
"fs = siterate Suc 1"

lemma l9: "<[1,2,3]> = stake 3\<cdot>fs"
  apply(simp add: fs_def One_nat_def)
  by (metis (no_types, lifting) Rep_cfun_strict1 numeral_2_eq_2 numeral_3_eq_3 sconc_snd_empty siterate_scons stake_Suc stream.take_0)

lemma "<[1,2,3]> \<sqsubseteq> fs"
  using l9 by auto

lemma "<[1]> = stake 1\<cdot>(siterate Suc 1)"
  by (metis One_nat_def Rep_cfun_strict1 list2s_0 list2s_Suc lscons_conv siterate_scons stake_Suc stream.take_0)

lemma "<[1,2]> = stake 2\<cdot>(siterate Suc 1)"
  by (metis (no_types, hide_lams) One_nat_def Rep_cfun_strict1 Suc_1 list2s_0 list2s_Suc lscons_conv siterate_scons stake_Suc stream.take_0)

lemma "<[1,2]> \<sqsubseteq> (siterate Suc 1)"
  by (metis Suc_1 list2s_0 list2s_Suc lscons_conv minimal monofun_cfun_arg siterate_scons)












(* Sum3_component fixrec form *)




(* Fingerübung *)

definition natural :: "nat stream" where
"natural = fix\<cdot>(\<Lambda> y. \<up>1 \<bullet> smap (\<lambda>x. x+1)\<cdot>y)"

lemma natural_unfold: "natural = \<up>1 \<bullet> smap Suc\<cdot>natural"
  by (subst natural_def [THEN fix_eq4], auto simp add: One_nat_def)

lemma natural2siter: "natural = siterate Suc 1"
  using natural_unfold rek2siter by blast


lemma snth_natural [simp]: "snth n natural = Suc n"
  by (metis Suc_eq_plus1 natural2siter snth_siterate_Suc)

lemma "shd (srt\<cdot>natural) = 2"
  by (metis numeral_2_eq_2 snth_natural snth_rt snth_shd)




(* Fingerübung 2 *)

definition sum3 :: "nat stream \<rightarrow> nat stream" where
"sum3 \<equiv> sscanl plus 0"


lemma sum3_eps [simp]:"sum3\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: sum3_def)


lemma [simp]: "#(sum3\<cdot>xs) = #xs"
  by(simp add: sum3_def)



lemma sum3_shd [simp]: "shd (sum3\<cdot>as) = shd as"
  apply(simp add: sum3_def)
  by (metis add.left_neutral shd1 sscanl_scons sum3_def sum3_eps surj_scons)

(* O_n = O_n-1 + I_ n *)
lemma sum3_snth: "Fin n < #as \<Longrightarrow> snth (Suc n) (sum3\<cdot>(\<up>a \<bullet> as)) = snth n (sum3\<cdot>as) + a"
  apply(induction n arbitrary: as a)
   apply(simp add: sum3_def sscanl_srt snth_rt)
   apply (metis add.commute add.left_neutral add.right_neutral lnsuc_neq_0_rev shd1 slen_empty_eq sscanl_scons surj_scons)
  by (smt Fin_Suc HOLCF_trans_rules(1) HOLCF_trans_rules(2) add.commute less_lnsuc lnat.sel_rews(2) lnle_def lnless_def lscons_conv monofun_cfun_arg semiring_normalization_rules(25) slen_scons snth_rt sscanl_snth stream.sel_rews(5) sum3_def up_defined)

lemma sum3_snth_inf[simp]: "snth n (sum3\<cdot>(\<up>x\<infinity>)) = (Suc n) * x"
  apply(induction n)
   apply (metis add.commute mult_Suc mult_is_0 shd1 sinftimes_unfold snth_shd sscanl_scons sum3_def)
  by (simp add: sscanl_snth sum3_def)

lemma "(sum3\<cdot>\<up>1\<infinity>) = (siterate Suc 1)"
  apply(rule sinf_snt2eq)
    apply simp
   apply simp
  using natural2siter sum3_snth by auto

lemma siter_snth2[simp]: "snth n (siterate (op + x) a) = a+ (n * x)"
  apply(induction n arbitrary: x)
   apply (simp)
  by (simp add: snth_snth_siter)


lemma sum3_2_siter: "(sum3\<cdot>\<up>x\<infinity>) = (siterate (\<lambda> a. x+a) x)"
  apply(rule sinf_snt2eq)
    by auto

lemma "sum3\<cdot>(\<up>1\<infinity>) = siterate Suc 1"
  using One_nat_def Suc2plus sum3_2_siter by presburger

lemma "sum3\<cdot>(\<up>0\<infinity>) = \<up>0\<infinity>"
  by (simp add: siter2sinf2 sum3_2_siter)

lemma "sum3\<cdot>(<[5,1,0,3]>) = <[5,6,6,9]>"
by(simp add: sum3_def)





  (* sSum takes 2 nat-streams and adds them component-wise *)
definition add:: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" where
"add \<equiv> \<Lambda> s1 s2 . smap (\<lambda> s3. (fst s3) + (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2)"

lemma "add = merge plus"
by(simp add: add_def merge_def)


lemma add_unfold: "add\<cdot>(\<up>x \<bullet> xs)\<cdot>(\<up>y\<bullet> ys) = \<up>(x+y) \<bullet> add\<cdot>xs\<cdot>ys"
  by(simp add: add_def)

lemma add_snth: "Fin n <#xs \<Longrightarrow>Fin n < #ys \<Longrightarrow> snth n (add\<cdot>xs\<cdot>ys) = snth n xs + snth n ys"
  apply(induction n arbitrary: xs ys)
   apply (metis Fin_02bot add_unfold lnless_def lnzero_def shd1 slen_empty_eq snth_shd surj_scons)
  by (smt Fin_Suc Fin_leq_Suc_leq Suc_eq_plus1_left add_unfold inject_lnsuc less2eq less2lnleD lnle_conv lnless_def lnsuc_lnle_emb sconc_snd_empty sdropostake shd1 slen_scons snth_rt snth_scons split_streaml1 stream.take_strict surj_scons ub_slen_stake)

lemma add_eps1[simp]: "add\<cdot>\<epsilon>\<cdot>ys = \<epsilon>"
  by(simp add: add_def)

lemma add_eps2[simp]: "add\<cdot>xs\<cdot>\<epsilon> = \<epsilon>"
  by(simp add: add_def)

lemma [simp]: "srt\<cdot>(add\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>b \<bullet> bs)) = add\<cdot>as\<cdot>bs"
  by (simp add: add_unfold)


lemma add_commu_helper: assumes "\<And>y. add\<cdot>x\<cdot>y = add\<cdot>y\<cdot>x"
  shows "add\<cdot>(\<up>a \<bullet> x)\<cdot>y = add\<cdot>y\<cdot>(\<up>a \<bullet> x)"
  apply(cases "y = \<epsilon>")
   apply auto[1]
  by (metis (no_types, lifting) Groups.add_ac(2) assms add_unfold surj_scons)

lemma add_commutative: "add\<cdot>x\<cdot>y = add\<cdot>y\<cdot>x"
  apply(induction x arbitrary: y)
    apply(simp_all)
  by (metis add_commu_helper stream.con_rews(2) stream.sel_rews(5) surj_scons)


lemma add_len: assumes "xs\<noteq>\<bottom>" and "u\<noteq>\<bottom>"
  shows "#(add\<cdot>xs\<cdot>(u && ys)) = lnsuc\<cdot>(#(add\<cdot>(srt\<cdot>xs)\<cdot>ys))"
  by (metis (no_types, lifting) add_unfold assms(1) assms(2) slen_scons stream.con_rews(2) stream.sel_rews(5) surj_scons)

lemma add_slen_help [simp]: "#xs \<sqsubseteq> #ys \<Longrightarrow> #(add\<cdot>xs\<cdot>ys) = #xs"
  apply(induction xs arbitrary: ys)
    apply(rule admI)
    apply rule+
    apply (smt ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun lub_below_iff lub_eq)
   apply(simp)
  proof -
  fix u
  fix xs ys :: "nat stream"
  assume as1: "u \<noteq> \<bottom>" and as2: "(\<And>ys. #xs \<sqsubseteq> #ys \<Longrightarrow> #(add\<cdot>xs\<cdot>ys) = #xs)" and as3: " #(u && xs) \<sqsubseteq> #ys"
  obtain a where a_def: "updis a = u" by (metis as1 discr.exhaust upE)
  show "#(add\<cdot>(u && xs)\<cdot>ys) = #(u && xs)"
  proof (cases "ys = \<epsilon>")
   case True thus ?thesis using add_eps2 as3 bot_is_0 bottomI strict_slen by auto
  next
  case False
  hence "#(add\<cdot>xs\<cdot>(srt\<cdot>ys)) = #xs" by (metis a_def as2 as3 lnat.inverts lscons_conv slen_scons surj_scons)
  thus ?thesis by (metis False \<open>updis a = u\<close> add_unfold lscons_conv slen_scons surj_scons)
  qed
qed




lemma add_slen [simp]: "#(add\<cdot>x\<cdot>y) = min (#x) (#y)"
  apply(cases "#x\<le>#y")
   apply (metis add_slen_help lnle_def min.commute min_absorb2)
  by (metis add_commutative add_slen_help linear lnle_def min.absorb2)

lemma add_slen_sinf [simp]: 
  shows " #xs = \<infinity> \<Longrightarrow> #(add\<cdot>xs\<cdot>ys) =(#ys)"
  by (simp add: min.absorb2)

lemma snth_add: "Fin n < #ys \<Longrightarrow> snth n (add\<cdot>\<up>x\<infinity>\<cdot>ys) = snth n (smap (\<lambda>z. z + x)\<cdot>ys)"
  apply(induction n arbitrary: ys)
   apply (smt Fin_02bot add.commute add_unfold lnless_def lnzero_def shd1 sinftimes_unfold slen_empty_eq smap_snth_lemma snth_shd surj_scons)
  by (smt Fin_Suc add_slen_sinf add_unfold lnle_conv lnless_def lnsuc_lnle_emb sinftimes_unfold slen_empty_eq slen_scons slen_sinftimes slen_smap smap_snth_lemma snth_scons strict_icycle surj_scons)

lemma add2smap: "add\<cdot>(\<up>x\<infinity>)\<cdot>ys = smap (\<lambda>z. z+x)\<cdot>ys"
  apply(rule snths_eq)
   apply auto[1]
  by (metis add_slen_sinf lnat.con_rews lnzero_def lscons_conv slen_empty_eq slen_scons slen_sinftimes snth_add sup'_def)

lemma add_zero [simp]: "add\<cdot>(sum3\<cdot>s)\<cdot>\<up>0\<infinity> = sum3\<cdot>s"
  apply(rule snths_eq)
   apply simp
  by (auto simp add: add_snth)




definition zed :: "nat stream" where
"zed= fix\<cdot>(\<Lambda> z. add\<cdot>(\<up>1)\<infinity>\<cdot>(\<up>0\<bullet>z))"


lemma zed_unfold : "zed = add\<cdot>(\<up>1)\<infinity>\<cdot>(\<up>0\<bullet>zed)"
  by (subst zed_def [THEN fix_eq4], auto)

lemma zed_unfold2 : "zed = \<up>1 \<bullet> add\<cdot>(\<up>1)\<infinity>\<cdot>zed"
  by (metis One_nat_def Suc_eq_plus1_left add_unfold sinftimes_unfold zed_unfold)

lemma [simp]: "shd zed = 1"
  by (metis shd1 zed_unfold2)

lemma zed_srt: "srt\<cdot>zed = smap Suc\<cdot>zed"
  by (metis One_nat_def add2smap fixrek2siter natural_def natural_unfold rek2siter sdrop_0 sdrop_back_rt sdrop_siter zed_unfold2)

lemma zed2smap: "zed = \<up>1 \<bullet> smap Suc\<cdot>zed"
  by (metis shd1 stream.sel_rews(2) strictI surj_scons zed_srt zed_unfold2)

lemma zed2siter: "zed = siterate Suc 1"
  using rek2siter zed2smap by blast

lemma zed_len[simp]: "#zed = \<infinity>"
  by(simp add: zed2siter)

lemma "snth n zed = Suc n"
  using natural2siter snth_natural zed2siter by auto




definition sum4 :: "nat stream \<rightarrow> nat stream" where
"sum4 \<equiv>  \<Lambda> x. (fix\<cdot>(\<Lambda> z. add\<cdot>x\<cdot>(\<up>0\<bullet>(z))))"

lemma sum4_unfold: "sum4\<cdot>input = add\<cdot>input\<cdot>(\<up>0\<bullet>(sum4\<cdot>input))"
  apply(simp add: sum4_def)
  apply (subst fix_eq)
  by simp

lemma [simp]: "sum4\<cdot>\<epsilon> = \<epsilon>"
  by (subst sum4_unfold, auto)

lemma sum4_shd [simp]: "shd (sum4\<cdot>(\<up>a \<bullet> as)) = a"
  apply (subst sum4_unfold)
  by (simp add: add_unfold)

lemma sum4_one [simp]: "sum4\<cdot>(\<up>a) = \<up>a"
  by (metis add_eps1 add_unfold sconc_snd_empty shd1 sum4_shd sum4_unfold)

lemma sum4_two [simp]: "sum4\<cdot>(\<up>a \<bullet> \<up>b) = \<up>a \<bullet> \<up>(a+b)"
  by (metis (no_types, lifting) Groups.add_ac(2) Nat.add_0_right add_eps1 add_unfold lscons_conv sum4_unfold sup'_def)

lemma sum4_snth0[simp]: "snth 0 (sum4\<cdot>xs) = snth 0 xs"
  by (metis add_eps1 snth_shd sum4_shd sum4_unfold surj_scons)

lemma [simp]: "shd (sum4\<cdot>xs) = shd xs"
  using sum4_snth0 by auto

lemma sum4_unfold2: "sum4\<cdot>(\<up>a \<bullet> as) = \<up>a \<bullet> add\<cdot>as\<cdot>(sum4\<cdot>(\<up>a \<bullet> as))"
  apply(subst sum4_unfold)
  by(simp add: add_unfold)


lemma sum4_snth1: assumes "Fin 1<#xs"
  shows "snth 1 (sum4\<cdot>xs) = snth 1 xs + snth 0 xs"
  by (smt HOLCF_trans_rules(1) HOLCF_trans_rules(2) One_nat_def add.commute add_eps1 add_snth add_unfold assms less_lnsuc lnle_def lnless_def lscons_conv shd1 slen_scons snth_rt snth_shd stream.sel_rews(5) sum4_snth0 sum4_unfold sum4_unfold2 sup'_def surj_scons up_defined)


lemma smapDup2smap: fixes as::"nat stream"
  shows "(smap (\<lambda>z. z + a)\<cdot>(smap (\<lambda>z. z + b)\<cdot>as)) = (smap (\<lambda>z. z + a + b)\<cdot>as)"
  apply(rule Streams.snths_eq)
   apply simp
  apply(rule+)
  by(simp add: smap_snth_lemma)


lemma [simp]: "#as \<sqsubseteq> #(as \<bullet> ys)"
  by (metis minimal monofun_cfun_arg sconc_snd_empty)



thm add_def
thm szip_def
thm slookahd_def
lemma min_rek: assumes  "z = min x (lnsuc\<cdot>z)"
  shows "z = x"
  apply(rule ccontr, cases "x < z")
   apply (metis assms dual_order.irrefl min_less_iff_conj)
  by (metis assms inf_ub ln_less lnle_def lnless_def min_def)


lemma sum4_slen [simp]:" #(sum4\<cdot>as) = #as"
  by (metis add_slen min_rek slen_scons sum4_unfold)

lemma [simp]: "Fin n < #as \<Longrightarrow> Fin n < lnsuc\<cdot>(#as)"
  by (smt below_antisym below_trans less_lnsuc lnle_def lnless_def)

lemma test3: assumes "Fin n < #as" shows
  "snth n (add\<cdot>as\<cdot>(\<up>0 \<bullet> sum4\<cdot>as)) = snth n as + snth n (\<up>0 \<bullet> sum4\<cdot>as)"
  by (smt HOLCF_trans_rules(1) HOLCF_trans_rules(2) add_snth assms less_lnsuc lnle_def lnless_def slen_scons sum4_slen)


lemma test2: "Fin n<#as \<Longrightarrow> snth n (sum4\<cdot>as) = (snth n as) + snth n (\<up>0 \<bullet> sum4\<cdot>as)"
  using sum4_unfold test3 by presburger

lemma [simp]: " #(srt\<cdot>(sum4\<cdot>(\<up>a \<bullet> as))) = #as"
  by (metis (no_types, lifting) add_slen inject_scons less_lnsuc min_absorb1 sconc_scons sconc_scons' sconc_snd_empty slen_scons stream.sel_rews(5) sum4_slen sum4_unfold2 sup'_def up_defined)


lemma sum4_snth: "Fin n < #as \<Longrightarrow> snth (Suc n) (sum4\<cdot>(\<up>a \<bullet> as)) = snth n (sum4\<cdot>as) + a"
  apply(induction n)
   apply (metis Fin_Suc One_nat_def inject_lnsuc lnless_def monofun_cfun_arg shd1 slen_scons snth_scons snth_shd sum4_snth0 sum4_snth1)
  apply(subst test2)
   apply (metis Fin_Suc inject_lnsuc lnless_def monofun_cfun_arg slen_scons)
  apply(simp add: add_snth)
  by (smt Fin_Suc add.assoc below_antisym below_trans less_lnsuc lnle_def lnless_def snth_scons sum4_unfold test3)

lemma assumes "Fin (Suc n) <#s"
  shows "snth (Suc n) (sum4\<cdot>s) = snth (Suc n) s + snth n (sum4\<cdot>s)"
by (simp add: assms test2)

lemma "shd (sum4\<cdot>s) = shd s"
by simp


lemma sum42sum3_helper: "Fin n < #(sum4\<cdot>as) \<Longrightarrow> snth n (sum4\<cdot>as) = snth n (sum3\<cdot>as)"
  apply(induction n arbitrary: as)
   apply(simp)
  by (metis Fin_leq_Suc_leq Suc_n_not_le_n add.commute less2nat_lemma less_le snth_scons sscanl_snth sum3_def sum4_slen test2)



lemma sum42sum3: "sum4\<cdot>as = sum3\<cdot>as"
  apply(rule Streams.snths_eq)
   apply simp
  apply rule+
  using sum42sum3_helper by blast

lemma "sum4 = sum3"
  by (simp add: cfun_eqI sum42sum3)

lemma "sum4\<cdot>(\<up>1\<infinity>) = siterate Suc 1"
  by (metis add2smap rek2siter sum4_unfold zed2siter zed_unfold)

lemma "sum4\<cdot>\<epsilon> = \<epsilon>"
  by simp

lemma "sum4\<cdot>(<[1,1,1]>) = <[1,2,3]>"
  apply (simp add: One_nat_def)
  apply(subst sum4_unfold2)
  by (metis (no_types, lifting) Suc2plus Suc_def2 add_2_eq_Suc' numeral_3_eq_3 sscanl_scons sum3_def sum42sum3 sum4_two sum4_unfold2)


lemma "snth n (sum4\<cdot>(siterate Suc 1)) * 2 = ((Suc n)*((Suc n)+1))"
  apply(induction n)
   apply(simp)
  by(simp add: test2 snth_siterate_Suc)












(* sum5 *)
thm sscanl_def
definition sscanl_fix :: "('o \<Rightarrow> 'i \<Rightarrow> 'o) \<Rightarrow> 'o \<Rightarrow> 'i stream \<rightarrow> 'o stream" where
"sscanl_fix f \<equiv> \<mu> h. (\<lambda> q . (\<Lambda> s. (if s=\<epsilon> then \<epsilon> else (\<up>(f q (shd s)) \<bullet> h (f q (shd s))\<cdot>(srt\<cdot>s)))))"

lemma sscanl_fix_monofun [simp]: "monofun (\<lambda> s. (if s=\<epsilon> then \<epsilon> else (\<up>(f q (shd s)) \<bullet> h (f q (shd s))\<cdot>(srt\<cdot>s))))" (is "monofun ?F")
proof (rule monofunI)
  fix x y :: "'a stream"
  assume "x\<sqsubseteq>y"
  have "?F \<bottom> \<sqsubseteq> ?F y" by simp
  have "x\<noteq>\<epsilon> \<Longrightarrow> (\<up>(f q (shd x)) \<bullet> h (f q (shd x))\<cdot>(srt\<cdot>x)) \<sqsubseteq> (\<up>(f q (shd y)) \<bullet> h (f q (shd y))\<cdot>(srt\<cdot>y))"
    by (metis \<open>(x::'a stream) \<sqsubseteq> (y::'a stream)\<close> lessD monofun_cfun_arg shd1)
  thus "?F x \<sqsubseteq> ?F y"
    using \<open>(x::'a stream) \<sqsubseteq> (y::'a stream)\<close> by auto
qed

lemma sscanl_fix_cont_h:  assumes "chain Y" and "(\<Squnion>i. Y i)\<noteq>\<bottom>"
  shows "(\<Squnion>i. \<up>(f q (shd (Y i))) \<bullet> h (f q (shd (Y i)))\<cdot>(srt\<cdot>(Y i))) = \<up>(f q (shd (\<Squnion>i. Y i))) \<bullet> h (f q (shd (\<Squnion>i. Y i)))\<cdot>(srt\<cdot>(\<Squnion>i. Y i))"
sorry

lemma sscanl_fix_cont [simp]: "cont (\<lambda> s. (if s=\<epsilon> then \<epsilon> else (\<up>(f q (shd s)) \<bullet> h (f q (shd s))\<cdot>(srt\<cdot>s))))" (is "cont ?F")
proof(rule contI)
  fix Y :: "nat \<Rightarrow> 'a stream"
  assume ch_y: "chain Y"
  thus "(range (\<lambda>i. ?F (Y i))) <<| ?F (\<Squnion>i. Y i)" 
  proof(cases "finite_chain Y")
    case True 
    have "monofun ?F" by simp
    hence "?F (\<Squnion>i. Y i) = (\<Squnion>i. (?F (Y i)))" sorry
    thus ?thesis sorry
  next
    case False
    thus ?thesis sorry
qed
qed

lemma sscanl_fix_mono3 [simp]: "monofun (\<lambda> h. \<Lambda> s. (if s=\<epsilon> then \<epsilon> else (\<up>(f q (shd s)) \<bullet> h (f q (shd s))\<cdot>(srt\<cdot>s))))"
  apply (rule monofunI)
  apply(rule cfun_belowI)
  apply auto
  apply (simp add: fun_belowD monofun_cfun_arg monofun_cfun_fun)
done


lemma sscanl_fix_cont3 [simp]: "cont (\<lambda> h. \<Lambda> s. (if s=\<epsilon> then \<epsilon> else (\<up>(f q (shd s)) \<bullet> h (f q (shd s))\<cdot>(srt\<cdot>s))))"
  apply(rule contI2)
   apply simp
  apply auto
  apply(rule cfun_belowI)
  apply (auto simp add: contlub_cfun_fun)
  apply (subst contlub_cfun_fun)
   apply(rule chainI)
   apply(rule cfun_belowI)
   apply (auto)
   apply(rule monofun_cfun_arg)
   apply (simp add: fun_belowD monofun_cfun_fun po_class.chainE)
  by (simp add: ch2ch_fun contlub_cfun_arg contlub_cfun_fun lub_fun)


lemma sscanl_fix_unfold: "sscanl_fix f q\<cdot>s = (if s=\<epsilon> then \<epsilon> else (\<up>(f q (shd s)) \<bullet> sscanl_fix f (f q (shd s))\<cdot>(srt\<cdot>s)))"
by(subst sscanl_fix_def [THEN fix_eq2], simp)

lemma [simp]: "sscanl_fix f q\<cdot>\<epsilon> = \<epsilon>"
by (simp add: sscanl_fix_unfold)

lemma sscanl_fix_unfold2: "sscanl_fix f q\<cdot>(\<up>x \<bullet> xs) = \<up>(f q x) \<bullet> sscanl_fix f (f q x)\<cdot>xs"
by (simp add: sscanl_fix_unfold)


lemma sscaln_fix2sscanl: "sscanl_fix f q\<cdot>s = sscanl f q\<cdot>s"
  apply(induction s arbitrary: q)
    apply simp
   apply simp
  by (metis (no_types, lifting) sscanl_fix_unfold2 sscanl_scons stream.con_rews(2) stream.sel_rews(5) surj_scons)

lemma "sscanl_fix = sscanl"
apply (rule HOL.ext)
apply (rule HOL.ext)
by (simp add: cfun_eqI sscaln_fix2sscanl)
                    
lemma "sscanl_fix plus 0 = sum3"
by (simp add: cfun_eqI sscaln_fix2sscanl sum3_def)







(* Fingerübung: Speck *)

(* schöne definition, einfach zu verwenden *)
definition G :: "nat stream set" where
"G = {s | s. sdom\<cdot>s\<subseteq>{1,2} }"

lemma "adm (\<lambda>s. s\<in>G)"
  by(simp add: G_def)

lemma "\<epsilon>\<in>G"
  by(simp add: G_def)

lemma "\<up>1\<infinity> \<in> G"
  by(simp add: G_def)


(* Hässliche definition, ein albtraum *)
definition F :: "'a set \<Rightarrow> 'a stream set" where
"F A =  fix\<cdot>(\<Lambda> F. { s. s=\<epsilon> \<or> (shd s \<in> A  \<and>  srt\<cdot>s \<in> F)})"

definition f_iter:: "nat \<Rightarrow> 'a set \<Rightarrow> 'a stream set" where
"f_iter n A = iterate n\<cdot>(\<Lambda> F. { s. s=\<epsilon> \<or> (shd s \<in> A  \<and>  srt\<cdot>s \<in> F)})\<cdot>\<bottom>"
(*
definition F :: "'a set \<Rightarrow> 'a stream set" where
"F A = (\<Squnion>n. f_iter n A)" *)

  (*
  (* Hässliche definition, ein albtraum *)
  definition F2 :: "nat stream set" where
  "F2 = fix\<cdot>(\<Lambda> F2. {\<epsilon>} \<union> { s::nat stream | s. shd s \<in> {1 ,2}  \<and>  srt\<cdot>s \<in> F2})"
  *)

lemma f_monofun [simp]: "monofun (\<lambda> F. {s. s=\<epsilon> \<or> (shd s \<in> A  \<and>  srt\<cdot>s \<in> F)})"
  apply(rule monofunI)
  by (smt Ball_Collect SetPcpo.less_set_def mem_Collect_eq subsetCE)


lemma f_cont [simp]: "cont (\<lambda> F. {s. s=\<epsilon> \<or> (shd s \<in> A  \<and>  srt\<cdot>s \<in> F)})"
  apply (rule contI2)
   apply(rule monofunI)
   apply (smt Ball_Collect SetPcpo.less_set_def mem_Collect_eq subsetCE)
  apply rule+
  by(auto simp add: SetPcpo.less_set_def lub_eq_Union)
  

lemma f_unfold: "s\<in>F A \<longleftrightarrow> (s=\<epsilon> \<or> (shd s \<in> A  \<and>  srt\<cdot>s \<in> F A))"
  apply(subst F_def)
  apply(subst fix_eq)
  using F_def f_cont by auto


lemma [simp]: "\<epsilon> \<in> F A"
  using f_unfold by blast

lemma "\<up>1 \<in> F {1}"
  by (metis f_unfold insert_iff sconc_snd_empty shd1 stream.sel_rews(5) sup'_def up_defined)

lemma f_srt: "s\<in>F A \<Longrightarrow> srt\<cdot>s \<in>F A"
by (metis f_unfold stream.sel_rews(2))

lemma f_sdrop: "s\<in>F A \<Longrightarrow> sdrop n\<cdot>s \<in>F A"
by(induction n, simp_all add: sdrop_back_rt f_srt)

lemma stake_suc: "stake (Suc n)\<cdot>s = (stake 1\<cdot>s) \<bullet> stake n\<cdot>(srt\<cdot>s)"
by (metis One_nat_def Suc2plus sdrop_0 sdrop_back_rt stake_add)

lemma f_stake[simp]: "s\<in>F A \<Longrightarrow> stake n\<cdot>s \<in> F A"
  apply(induction n arbitrary: s)
   apply simp
  apply (subst stake_suc)
  apply (simp add: One_nat_def)
  apply(case_tac "s=\<epsilon>")
   apply simp
  by (metis One_nat_def f_unfold lscons_conv shd1 stake_Suc stake_suc stream.sel_rews(5) surj_scons up_defined)

lemma f_snth[simp]: assumes "s\<in>F A" and "Fin n <#s"
  shows "snth n s \<in> A"
  using assms apply(induction n arbitrary: s)
   apply simp
   apply (metis One_nat_def empty_iff f_unfold insertE lnsuc_neq_0_rev strict_slen)
  apply (simp add: snth_rt)
  by (meson f_srt not_less slen_rt_ile_eq)


lemma f_fin_sdom2: "sdom\<cdot>s\<subseteq>A \<Longrightarrow> #s<\<infinity> \<Longrightarrow> s\<in>F A"
  apply(induction s)
    apply(rule admI)
    apply (metis finite_chain_def inf_chainl4 lnless_def maxinch_is_thelub)
   apply auto
  by (smt One_nat_def f_unfold fold_inf inf_ub less_le sdom_subset sfilter_nin sfilter_sdoml3 slen_scons stream.sel_rews(5) subset_trans surj_scons)

lemma f2sdom: "s\<in>F A \<Longrightarrow> sdom\<cdot>s\<subseteq>A"
by (smt f_snth mem_Collect_eq sdom_def2 subsetI)

lemma f_admN [simp]: "adm (\<lambda>s. s\<notin>F A)"
apply(rule admI)
by (metis approxl2 f_stake is_ub_thelub)


(* allgemeine sachen *)
lemma sfoot_dom: assumes "#s = Fin (Suc n)" and "sdom\<cdot>s\<subseteq>A"
  shows "sfoot s\<in>A"
by (metis Suc_n_not_le_n assms(1) assms(2) contra_subsetD leI less2nat_lemma sfoot_exists2 snth2sdom)

lemma sfood_id: assumes"#s = Fin (Suc n)"
  shows "(stake n\<cdot>s) \<bullet> \<up>(sfoot s) = s"
  using assms apply(induction n arbitrary: s)
   apply simp
   apply (metis Fin_02bot Fin_Suc lnat.sel_rews(2) lnsuc_neq_0_rev lnzero_def lscons_conv sfoot_exists2 slen_scons snth_shd strict_slen sup'_def surj_scons)
  apply (subst stake_suc)
  apply simp
  by (smt Fin_02bot Fin_Suc One_nat_def Rep_cfun_strict1 Zero_not_Suc leI lnat.sel_rews(2) lnle_Fin_0 lnzero_def notinfI3 sconc_snd_empty sfoot_sdrop slen_rt_ile_eq slen_scons stake_Suc stream.take_0 strict_slen surj_scons)

lemma f_unfold2: assumes"#s = Fin (Suc n)"
  shows "s\<in>F A \<longleftrightarrow> stake n\<cdot>s\<in>F A \<and> sfoot s\<in>A" (is "?L \<longleftrightarrow> ?R")
proof(rule)
  show "?L \<Longrightarrow> ?R" using assms f2sdom sfoot_dom One_nat_def f_stake by blast
next
  assume "?R"
  hence "sdom\<cdot>(stake n\<cdot>s) \<subseteq> A" using f2sdom by blast
  hence "sdom\<cdot>((stake n\<cdot>s) \<bullet> \<up>(sfoot s)) \<subseteq> A"
    proof -
      have "sdom\<cdot>(\<up>(sfoot s)) \<subseteq> A"
        by (simp add: \<open>stake (n::nat)\<cdot>(s::'a stream) \<in> F (A::'a set) \<and> sfoot s \<in> A\<close>)
      then show ?thesis
        by (meson Un_least \<open>sdom\<cdot>(stake (n::nat)\<cdot>(s::'a stream)) \<subseteq> (A::'a set)\<close> sconc_sdom subset_trans)
    qed
  thus "?L" by (simp add: assms f_fin_sdom2 sfood_id) 
qed

lemma stakeind2: 
  "\<forall>x. (P \<epsilon> \<and> (\<forall>a s. P s \<longrightarrow> P (s \<bullet> \<up>a))) \<longrightarrow> P (stake n\<cdot>x)"
  apply(induction n)
   apply simp
  apply auto
  apply (subst stake_suc)
  by (metis (no_types, lifting) sconc_snd_empty sdrop_back_rt sdropostake split_streaml1 stake_suc surj_scons)


lemma ind2: assumes "adm P" and "P \<epsilon>"  and "\<And>a s. P s  \<Longrightarrow> P (s \<bullet> \<up>a)"
  shows "P x"
by (metis assms(1) assms(2) assms(3) stakeind2 stream.take_induct)


lemma f_iter_Lub: "(\<Squnion>i. f_iter i A)  = F A"
by(simp add: f_iter_def F_def fix_def)

lemma f_iter0 [simp]: "f_iter 0 A={}"
by (simp add: UU_eq_empty f_iter_def)


lemma f_iter_suc: "f_iter (Suc n) A = {s. s = \<epsilon> \<or> (shd s \<in>A) \<and> srt\<cdot>s \<in> f_iter n A}"
by (simp add: f_iter_def)

lemma f_iter1 [simp]: "f_iter 1 A = {\<epsilon>}"
apply(auto simp add: f_iter_def One_nat_def)
by (metis SetPcpo.less_set_def contra_subsetD empty_iff minimal)

lemma f_iter_sdom: "f_iter (Suc n) A = {s. #s \<le> Fin n \<and> sdom\<cdot>s\<subseteq>A}"
apply(induction n)
apply (simp add: f_iter_def)
apply (metis SetPcpo.less_set_def empty_iff f2sdom f_unfold minimal subset_eq)
apply (subst f_iter_suc)
by (metis (mono_tags, lifting) f2sdom f_fin_sdom2 f_unfold inf_ub less_le lnle_def lnzero_def mem_Collect_eq minimal notinfI3 slen_rt_ile_eq strict_slen)

lemma f_iter_len: "x\<in>f_iter (Suc n) A \<Longrightarrow> #x \<le> Fin n"
by (simp add: f_iter_sdom)

lemma f_iter_chain_h: "f_iter (Suc i) A \<subseteq> f_iter (Suc (Suc i)) A"
apply(simp add: f_iter_sdom)
using order.trans by fastforce

lemma f_iter_chain: "chain (\<lambda>i. f_iter i A)"
  apply(rule chainI)
  apply(case_tac "i=0")
   apply simp
   apply (metis UU_eq_empty minimal)
  by (metis SetPcpo.less_set_def f_iter_chain_h list_decode.cases)

lemma f_iter_lub_fin: "x\<in>(\<Squnion>i. f_iter i A) \<Longrightarrow> #x <\<infinity>"
apply(simp add: lub_eq_Union)
by (metis empty_iff f_iter0 f_iter_len inf_less_eq leI nat.exhaust notinfI3)

lemma f_iter_sdom2: "(\<Squnion>i. f_iter i A) = {s. sdom\<cdot>s\<subseteq>A \<and> #s<\<infinity>}"
  apply auto
    using f2sdom f_iter_Lub apply blast
   using f_iter_lub_fin apply blast
  by (simp add: f_fin_sdom2 f_iter_Lub)

lemma f_sdom: "F A = {s. sdom\<cdot>s\<subseteq>A \<and> #s<\<infinity>}"
by (metis (mono_tags, lifting) f_iter_Lub f_iter_sdom2)

lemma "\<up>1\<infinity>\<notin>F {1}"
by(simp add: f_sdom)


lemma sfilterEq2sdom_h: "sfilter A\<cdot>s = s \<longrightarrow> sdom\<cdot>s \<subseteq> A"
  apply(rule ind [of _s])
    apply (smt admI inf.orderI sdom_sfilter)
   apply(simp)
  apply(rule)
  by (smt mem_Collect_eq sdom_def2 sfilterl7 subsetI)

lemma sfilterEq2sdom: "sfilter A\<cdot>s = s \<Longrightarrow> sdom\<cdot>s \<subseteq> A"
  by (simp add: sfilterEq2sdom_h)







(* implementation von stake auf lnat's *)


fixrec take2 ::"lnat \<rightarrow> 'a stream \<rightarrow> 'a stream" where
"take2\<cdot>\<bottom>\<cdot>a = \<bottom>" |
"take2\<cdot>ln\<cdot>\<bottom> = \<bottom>" |
"u\<noteq>\<bottom> \<Longrightarrow> take2\<cdot>(lnsuc\<cdot>ln)\<cdot>(u&&a) = u && (take2\<cdot>ln\<cdot>a)"

lemma [simp]: "take2\<cdot>0\<cdot>s = \<epsilon>"
by (simp add: lnzero_def)

lemma take2unfold: "take2\<cdot>(Fin (Suc n))\<cdot>(\<up>x \<bullet> xs) = \<up>x \<bullet> take2\<cdot>(Fin n)\<cdot>xs"
by (metis Fin_Suc lscons_conv take2.simps(3) up_defined)

lemma take2stake: "take2\<cdot>(Fin n)\<cdot>s = stake n\<cdot>s"
  apply(induction n arbitrary: s)
   apply simp
  by (metis (no_types, hide_lams) Fin_Suc lscons_conv scases stream.take_rews stream.take_strict take2.simps(2) take2.simps(3) up_defined)

lemma take2_inf [simp]: "take2\<cdot>\<infinity>\<cdot>s = s"
  apply(rule ind [of _s])
    apply simp
   apply simp
  by (metis fold_inf lscons_conv take2.simps(3) up_defined)

lemma take_slen[simp]: "take2\<cdot>(#s)\<cdot>s = s"
  apply(rule ind [of _s])
    apply simp
   apply simp
  by (metis lscons_conv slen_scons take2.simps(3) up_defined)

lemma "take2\<cdot>ln\<cdot>s \<sqsubseteq> s"
by (metis inf_ub lnle_def monofun_cfun_arg monofun_cfun_fun take2_inf)

lemma take2len [simp]: "#(take2\<cdot>ln\<cdot>s) = min ln (#s)"
  apply(induction ln arbitrary: s)
    apply(rule admI)
    apply auto
    apply (metis finite_chain_def inf_less_eq maxinch_is_thelub min_def take2_inf unique_inf_lub)
   using eq_bottom_iff lnzero_def apply fastforce
  apply(case_tac "s=\<epsilon>")
   apply auto[1]
  by (metis (no_types, lifting) lnsuc_lnle_emb lscons_conv min_def slen_scons surj_scons take2.simps(3) up_defined)







lemma "chain (\<lambda>i. iterate i\<cdot>H\<cdot>\<bottom>)"
by simp


definition fix_id :: "'a stream \<rightarrow> 'a stream" where
"fix_id \<equiv> fix\<cdot>(\<Lambda> h s. lshd\<cdot>s && h\<cdot>(srt\<cdot>s))"

lemma fix_id_unfold: "fix_id\<cdot>s = lshd\<cdot>s && fix_id\<cdot>(srt\<cdot>s)"
by(subst fix_id_def [THEN fix_eq2], auto)

lemma [simp]: "fix_id\<cdot>\<epsilon> = \<epsilon>"
apply(subst fix_id_unfold)
by simp

lemma "fix_id\<cdot>s = s"
  apply(induction s)
    apply simp
   apply simp
  by (metis fix_id_unfold stream.sel_rews(4) stream.sel_rews(5))

lemma "iterate 0\<cdot>(\<Lambda> h s. lshd\<cdot>s && h\<cdot>(srt\<cdot>s))\<cdot>\<bottom> = \<bottom>"
by simp 

lemma "iterate 1\<cdot>(\<Lambda> h s. lshd\<cdot>s && h\<cdot>(srt\<cdot>s))\<cdot>\<bottom> = (\<Lambda> s. lshd\<cdot>s && \<bottom>)"
by(simp add: iterate_def One_nat_def)

lemma "iterate 2\<cdot>(\<Lambda> h s. lshd\<cdot>s && h\<cdot>(srt\<cdot>s))\<cdot>\<bottom> = (\<Lambda> s. lshd\<cdot>s && lshd\<cdot>(srt\<cdot>s) && \<bottom>)"
by(simp add: iterate_def One_nat_def Num.numerals)

lemma fix_id_take: "iterate n\<cdot>(\<Lambda> h s. lshd\<cdot>s && h\<cdot>(srt\<cdot>s))\<cdot>\<bottom>\<cdot>s = stake n\<cdot>s"
apply(induction n arbitrary: s)
apply simp
apply simp
by (metis (no_types, lifting) lscons_conv lshd_updis stream.con_rews(2) stream.sel_rews(3) stream.take_rews surj_scons)

lemma "iterate n\<cdot>(\<Lambda> h s. lshd\<cdot>s && h\<cdot>(srt\<cdot>s))\<cdot>\<bottom> = stake n"
by (simp add: cfun_eqI fix_id_take)


lemma "(U\<cdot>(fix\<cdot>U)) = (fix\<cdot>U)"
by (metis fix_eq)

lemma assumes "U\<cdot>g = g"
  shows "fix\<cdot>U\<sqsubseteq>g"
by (metis fix_least assms)

lemma assumes "x = \<up>1 \<bullet> x" and "y = \<up>1 \<bullet> y "
  shows "x=y"
using assms(1) assms(2) s2sinftimes by auto

lemma assumes "ln = lnsuc\<cdot>ln"
  shows "ln = \<infinity>"
using assms ninf2Fin by force

(*

--Untimed sum in haskell--
sum :: nat stream => nat stream
sum x = h2 x 0

h2 :: nat stream => nat => nat stream
h2 \<euro> y = \<euro>
h2 x:xs y = (x+y) : h2 xs (x+y)

--Untimed sum in isabelle (zu zeigen: äquivalent mit sum3/sum4)--Typen müssen angepasst

*)

primrec h :: "nat \<Rightarrow> nat stream \<Rightarrow> nat \<Rightarrow> nat stream" where
"h 0 s y = \<epsilon>" | (*maximal one non-variable argument required, so \<epsilon>-case must be encoded in the line below.*)
"h (Suc n) s y = (if s=\<epsilon> then \<epsilon> else \<up>((shd s)+ y )\<bullet> (h n (srt\<cdot> s) ((shd s)+ y)))"

definition h2 :: "nat stream \<Rightarrow> nat \<Rightarrow> nat stream" where  
"h2 s y \<equiv> \<Squnion>i. h i s y"

definition sum5 :: "nat stream \<rightarrow> nat stream" where
"sum5 \<equiv> \<Lambda> x. h2 x 0"

definition sum5_test :: "nat stream" where
"sum5_test= sum5\<cdot> (\<up>1)"


lemma h_eps: "h n \<epsilon> y = \<epsilon>"
by(induct_tac n,auto)


lemma h2_eps[]: "h2 \<epsilon> y = \<epsilon>"
by(simp add: h2_def h_eps)

lemma contlub_h:
  "\<forall>s y. h n s y = h n (stake n\<cdot>s) y"
apply (induct_tac n, auto)
apply (rule_tac x=s in scases)
apply auto
apply (rule_tac x=s in scases)
by auto


lemma chain_h: "chain h"
apply (rule chainI)
apply (subst fun_below_iff)+
apply (induct_tac i, auto)
apply (erule_tac x="x" in allE)
apply (simp add: h_eps)
by (smt monofun_cfun_arg)

(* monotonicity of h *)
lemma mono_h: 
  "\<forall> x y q. x \<sqsubseteq> y \<longrightarrow> h n x q \<sqsubseteq> h n y q"
apply (induct_tac n, auto)
apply (drule lessD, erule disjE, simp)
apply (erule exE)+
apply (erule conjE)+
by (simp, rule monofun_cfun_arg, simp)

lemma cont_lub_h2_helper2:
  "\<forall>s y. stake n\<cdot> (h n s y) = h n s y "
using contlub_h
by(induct_tac n,auto)


lemma sum5_snth_stake_min:
  "snth n (stake m\<cdot> (h m s y)) = snth (min n m) (h m s y)"
using contlub_h
apply (induct_tac n,auto)
using cont_lub_h2_helper2 apply auto[1]
by (metis cont_lub_h2_helper2 min_def sdropostake snth_def stakeostake)

(*lemma helperhelper: "\<Squnion>i. h i s y = h i (\<Squnion>i. s ) y"*)

lemma cont_lub_h2_helper: "\<And>i. cont (\<lambda>s. h i s y)"
apply (simp add: cont_def)

sorry

(* h2 is a continuous function *)
lemma cont_lub_h2: "cont (\<lambda> s. \<Squnion>i. h i s y)" 
apply (rule cont2cont_lub)
apply (rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "y"])
apply (rule chainE)
apply (metis (no_types, lifting) chain_h fun_below_iff po_class.chainE po_class.chainI)
by (simp add: cont_lub_h2_helper)

lemma sum5_scons:"sum5\<cdot>(\<up>a\<bullet>s) = \<up>(a) \<bullet> (h2 s a)"  
apply (simp add: sum5_def h2_def)
apply (subst beta_cfun, rule cont_lub_h2)+
apply (subst contlub_cfun_arg)
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
apply (smt chain_h fun_belowI po_class.chain_def)
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
apply (smt chain_h fun_belowI po_class.chain_def)
by  simp



lemma sum5_unfold_h: "sum5\<cdot> input = h2 input 0"
apply (simp add:sum5_def h2_def)
by (simp add: cont_lub_h2)

lemma sum5_unfold_h2: "h2 input 0 = (\<Squnion>i. h i input 0)"
by (simp add:h2_def)




lemma sum5_empty[simp]: "sum5\<cdot> \<epsilon> = \<epsilon>"
by (simp add: h2_eps sum5_unfold_h)

lemma sum5_shd [simp]: "shd (sum5\<cdot>(\<up>a \<bullet> as)) = a"
by (simp add: sum5_scons)

lemma [simp]: "shd (sum5\<cdot> xs) = shd xs"
using sum5_shd 
by (metis sum5_empty surj_scons)

lemma sum5_snth0[simp]: "snth 0 (sum5\<cdot> xs) = snth 0 xs"
by simp

lemma sum52sum3_helper_helper: "snth 0 (sum5\<cdot> as) = snth 0 (sum4\<cdot> as)"
by simp

lemma sum5_one [simp]: "sum5\<cdot>(\<up>a) = \<up>a"
by (metis h2_eps lscons_conv sum5_scons sup'_def)

lemma sum5_unfold2_h[simp]: "h2 (\<up>a1 \<bullet>  as) 0 = \<up>a1 \<bullet> (h2 as a1)"
using sum5_scons sum5_unfold_h by auto



lemma sum5_unfold_sum5[simp]: "sum5\<cdot>(\<up>0 \<bullet>as) =\<up>0 \<bullet> sum5\<cdot>(as)"
by (simp add: sum5_unfold_h)

lemma sum5_unfoldh2h: "h2 (\<up>a1 \<bullet>  as) 0 = \<up>a1 \<bullet> (\<Squnion>i. h i as a1)"
using sum5_scons sum5_unfold_h sum5_unfold_h2
by (simp add: h2_def)

lemma snth_zero_h[simp]: "snth 0 (\<up>a1 \<bullet> (h2 (\<up>a2 \<bullet>as) a1)) = a1"
by simp

lemma h2_unfold_ite[rule_format]: "as\<noteq>\<epsilon> \<longrightarrow> h2 as a1= \<up>(shd as + a1)\<bullet> h2 (srt\<cdot>as) (shd as + a1)"
apply(induct_tac a1, simp_all)
apply (metis sum5_scons sum5_unfold_h surj_scons)
sorry

lemma snth_one_h[simp]: "snth 1 (\<up>a1 \<bullet> (h2 (\<up>a2 \<bullet>as) a1)) = a2+a1"
apply (simp add: sum5_scons One_nat_def)
using h2_unfold_ite by auto


lemma h2_one_unfold[simp]: "h2 (\<up>a1) n= \<up>(a1+n)"
by (metis h2_unfold_ite lscons_conv shd1 stream.con_rews(2) stream.sel_rews(5) sum5_one sum5_scons sup'_def up_defined)

lemma sum5_two [simp]: "sum5\<cdot>(\<up>a1\<bullet> \<up>a2) = \<up>a1 \<bullet> \<up>(a1+a2)"
apply(simp add: sum5_unfold_h)
by (simp add: add.commute)

lemma sum5_noteps[simp]: "s\<noteq>\<epsilon> \<Longrightarrow> sum5\<cdot>s = \<up>(shd s)\<bullet> h2 (srt \<cdot>s) (shd s)"
using assms
by (metis sum5_unfold2_h sum5_unfold_h surj_scons)

lemma sum5_slen [simp]:" #(sum5\<cdot>as) = #as"
  (*by (metis add_slen min_rek slen_scons sum5_noteps h2_unfold2_h2)*)
sorry

lemma sum5_snth_1_helper: "Fin 0 < #as \<Longrightarrow> snth (Suc 0) (sum5\<cdot>(\<up>a1 \<bullet>\<up>a2 \<bullet>as)) = a2+a1"
using One_nat_def snth_one_h sum5_scons by presburger


lemma sum5_snth_1: "as\<noteq>\<epsilon> \<Longrightarrow> snth (Suc 0) (sum5\<cdot>(\<up>a1\<bullet>as)) = snth (Suc 0) (\<up>a1\<bullet>as) + a1"
by (metis One_nat_def add.commute scases shd1 snth_one_h snth_scons snth_shd sum5_scons)

lemma test[rule_format]: "Fin (Suc n) < #as \<longrightarrow> snth (Suc n) (h2 as a) =snth n (h2 as a) + snth (Suc n) as"
sorry



lemma test2_sum5[rule_format]: "Fin n<#as \<longrightarrow> snth n (sum5\<cdot>as) = snth n as + snth n (sum5\<cdot>(\<up>0 \<bullet>as))"
 using add.left_neutral add_less_cancel_right lessI less_nat_zero_code slen_smap
apply(induction n,simp_all)
sorry

lemma sum5_snth1: assumes "Fin 1<#xs"
  shows "snth 1 (sum5\<cdot>xs) = snth 1 xs + snth 0 xs"
by (metis One_nat_def assms snth_scons snth_shd sum5_snth0 sum5_unfold2_h sum5_unfold_h test2_sum5)



lemma sum5_snth_helper[rule_format]: "Fin n < #as \<longrightarrow> snth n (h2 as a) = snth n (h2 as 0) + a"
apply (induction n, simp_all)
apply (metis Nat.add_0_right h2_unfold_ite lnsuc_neq_0_rev shd1 slen_empty_eq)
apply (simp add: test)
by (metis Fin_leq_Suc_leq linorder_not_less order_less_le)

lemma sum5_snth: "Fin n < #as \<Longrightarrow> snth (Suc n) (sum5\<cdot>(\<up>a \<bullet> as)) = snth n (sum5\<cdot>as) + a"
by (metis snth_scons sum5_scons sum5_snth_helper sum5_unfold_h)


lemma sum52sum4_helper: "Fin n < #(sum5\<cdot>as) \<Longrightarrow> snth n (sum5\<cdot>as) = snth n (sum4\<cdot>as)"
  apply(induction n)
   apply(simp)
using sum4_snth sum5_snth
by (smt Fin_leq_Suc_leq Suc_n_not_le_n less2nat_lemma less_le snth_scons sum5_scons sum5_slen sum5_unfold_h test2 test2_sum5)

lemma sum5_sum3: "sum5\<cdot> as = sum4\<cdot>as"
  apply(rule Streams.snths_eq)
   apply simp
using sum5_slen sum52sum4_helper
by auto

lemma sum52sum3: "sum5 = sum4"
  by (simp add: cfun_eqI sum5_sum3)





(*Für HK*)
(*
--TIMED: analog (try evtl. auch mit sscanl / gibts eine function timed-sscanl? wenn nicht dann definieren)

sum x = sum4 x 0

sum4 \<euro> y = \<euro>
sum4 T:xs y = T : sum4 xs y
sum4 x:xs y = (x+y) : sum4 xs (x+y)

*)


end