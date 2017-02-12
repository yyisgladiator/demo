(*  Title:  Tsum5_HK.thy
    Author: Hendrik Kausch
    e-mail: hendrik.kausch@rwth-aachen.de

    Description:  Definitons and lemmas for tsum5 
*)

theory Tsum5_HK
imports TStream StreamCase_Study
begin

primrec tsh :: "nat \<Rightarrow> nat \<Rightarrow> nat event stream \<Rightarrow> nat event stream" where
"tsh 0 p ts =  \<epsilon>" | (*maximal one non-variable argument required, so \<epsilon>-case must be encoded in the line below.*)
"tsh (Suc n) p ts = (if ts = \<epsilon> then \<epsilon> 
                        else(if shd ts= \<surd> then (\<up>\<surd> \<bullet> (tsh n p (srt\<cdot>ts)))
                                else (\<up>(Msg (p + (THE m. Msg m = shd ts)))) \<bullet> (tsh n (p +(THE m. Msg m = shd ts)) (srt\<cdot> ts))))"


definition tsum5_helper :: " nat \<Rightarrow> nat event stream \<rightarrow> nat event stream" where
"tsum5_helper p \<equiv> \<Lambda> ts. (\<Squnion>i. tsh i p ts)"


definition tsum5:: "nat tstream \<rightarrow> nat tstream" where
"tsum5 \<equiv> \<Lambda> ts. Abs_tstream (tsum5_helper 0\<cdot>(Rep_tstream ts))"



(*Testing tssum5_def*)

lemma tsAbs_bot[simp]: "tsAbs\<cdot>\<bottom> = \<epsilon>"
by(simp add: tsAbs_def)

lemma tsh_bot: "tsh n p \<epsilon> = \<epsilon>"
by(induct_tac n,auto)

lemma tswell2tswell: "Fin n < #ts \<and> ts_well ts \<Longrightarrow> ts_well (sdrop n\<cdot> ts)"
by simp

lemma AbsStsAbs_tick[simp]: "ts_well as \<Longrightarrow> tsAbs\<cdot> (Abs_tstream (\<up>(\<surd>)\<bullet>as)) = tsAbs\<cdot>(Abs_tstream as)"
by(simp add: tsabs_insert)


lemma tsh_tick[simp]: "ts_well as \<Longrightarrow> tsh (Suc n) p ((\<up>\<surd>)\<bullet>as) = (\<up>\<surd>)\<bullet> tsh n p as"
by(simp add: tsh_def)

lemma tsabs_abs_tick[simp]:"tsAbs\<cdot>(Abs_tstream (\<up>\<surd>)) = \<epsilon>"
by(simp add: tsAbs_def)

lemma tswellinftick: "ts_well ((\<up>\<surd>)\<infinity>)"
by (simp add: ts_well_def)


lemma tssum5_helpersinf[simp]: "tsh (Suc n) p (sinftimes(\<up>\<surd>)) = (\<up>\<surd>) \<bullet> tsh n p (sinftimes (\<up>\<surd>))"
by auto

lemma contlub_tsh:
  "\<forall>s p. tsh i p s = tsh i p (stake i\<cdot>s)"
apply (induct_tac i, auto)
apply (rule_tac x=s in scases)
apply auto
apply (metis (no_types, lifting) inject_scons stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis lshd_updis stake_Suc stream.sel_rews(3) surj_scons)
apply (rule_tac x=s in scases)
by auto

lemma chain_tsh_helper: "xa\<noteq>\<epsilon> \<and> shd xa \<noteq>\<surd> \<Longrightarrow> tsh (Suc n) x (xa) = \<up>(Msg (x + (THE m. Msg m = shd xa))) \<bullet> tsh n (x + (THE m. Msg m = shd xa)) (srt\<cdot>xa)"
by simp

lemma chain_tsh: "chain tsh"
apply (rule chainI)
apply (subst fun_below_iff)+
apply (induct_tac i, auto)
apply (erule_tac x="x" in allE)
apply (simp add: tsh_bot)
apply (simp add: tsh_bot)
apply (smt monofun_cfun_arg)
apply (smt monofun_cfun_arg)
apply (simp add: tsh_bot)
apply (simp add: tsh_bot)
proof -
  fix n :: nat and x :: nat and xa :: "nat event stream"
  assume a1: "shd (srt\<cdot>xa) \<noteq> \<surd>"
  assume a2: "srt\<cdot>xa \<noteq> \<epsilon>"
  assume a3: "shd xa = \<surd>"
  assume a4: "\<forall>x xa. tsh n x xa \<sqsubseteq> (if xa = \<epsilon> then \<epsilon> else if shd xa = \<surd> then \<up>\<surd> \<bullet> tsh n x (srt\<cdot>xa) 
                                     else \<up>(Msg (x + (THE m. Msg m = shd xa))) \<bullet> 
                                          tsh n (x + (THE m. Msg m = shd xa)) (srt\<cdot>xa))"
  moreover have "tsh (Suc n) x (srt\<cdot>xa) \<sqsubseteq> \<up>(Msg (x + (THE m. Msg m = shd (srt\<cdot>xa)))) \<bullet> 
                                          tsh n (x + (THE m. Msg m = shd (srt\<cdot>xa))) (srt\<cdot>(srt\<cdot>xa))"
   by (simp add: chain_tsh_helper a1)
  then show "\<up>\<surd> \<bullet> tsh n x (srt\<cdot>xa) \<sqsubseteq> \<up>\<surd> \<bullet> \<up>(Msg (x + (THE m. Msg m = shd (srt\<cdot>xa)))) \<bullet> 
                                          tsh n (x + (THE m. Msg m = shd (srt\<cdot>xa))) (srt\<cdot>(srt\<cdot>xa))"
   by (smt a1 a2 calculation chain_tsh_helper monofun_cfun_arg rev_below_trans)
next
 fix n :: nat and x :: nat and xa :: "nat event stream"
  assume a1: "shd (srt\<cdot>xa) \<noteq> \<surd>"
  assume a2: "srt\<cdot>xa \<noteq> \<epsilon>"
  assume a3: "shd xa \<noteq> \<surd>"
  assume a4: "\<forall>x xa. tsh n x xa \<sqsubseteq>
                     (if xa = \<epsilon> then \<epsilon>
                      else if shd xa = \<surd> then \<up>\<surd> \<bullet> tsh n x (srt\<cdot>xa)
                           else \<up>(Msg (x + (THE m. Msg m = shd xa))) \<bullet> tsh n (x + (THE m. Msg m = shd xa)) (srt\<cdot>xa))"
  then have "tsh (Suc n) x (srt\<cdot>xa) \<sqsubseteq> \<up>(Msg (x + (THE m. Msg m = shd (srt\<cdot>xa)))) \<bullet> 
                                       tsh n (x + (THE m. Msg m = shd (srt\<cdot>xa))) (srt\<cdot>(srt\<cdot>xa))"
    by(simp add: chain_tsh_helper a1)
  then show "\<up>(Msg (x + (THE m. Msg m = shd xa))) \<bullet> tsh n (x + (THE m. Msg m = shd xa)) (srt\<cdot>xa) \<sqsubseteq>
              \<up>(Msg (x + (THE m. Msg m = shd xa))) \<bullet> \<up>(Msg (x + (THE m. Msg m = shd xa) +
              (THE m. Msg m = shd (srt\<cdot>xa)))) \<bullet> 
              tsh n (x + (THE m. Msg m = shd xa) + (THE m. Msg m = shd (srt\<cdot>xa))) (srt\<cdot>(srt\<cdot>xa)) "
   using a2 a1 a3
   by (smt a4 add_left_imp_eq event.inject less_all_sconsD monofun_cfun_arg tsh.simps(2))
qed

lemma mono_tsh_helper: "x \<sqsubseteq> y \<and> x \<noteq> \<epsilon> \<Longrightarrow> shd x = shd y"
using lessD by fastforce

(* monotonicity of tsh *)
lemma mono_tsh: 
  "\<forall> x y q. x \<sqsubseteq> y \<longrightarrow> tsh n q x \<sqsubseteq> tsh n q y"
apply (induct_tac n, auto)
apply (drule lessD, erule disjE, simp)
apply (erule exE)+
apply (erule conjE)+
apply (simp, rule monofun_cfun_arg, simp)
using lessD apply fastforce
using lessD apply fastforce
using mono_tsh_helper
proof -
  fix na :: nat and x :: "nat event stream" and y :: "nat event stream" and q :: nat
  assume a1: "x \<sqsubseteq> y"
  assume a2: "x \<noteq> \<epsilon>"
  assume "\<forall>x y. x \<sqsubseteq> y \<longrightarrow> (\<forall>q. tsh na q x \<sqsubseteq> tsh na q y)"
  then show "\<up>(Msg (q + (THE n. Msg n = shd x))) \<bullet> tsh na (q + (THE n. Msg n = shd x)) (srt\<cdot>x) \<sqsubseteq> \<up>(Msg (q + (THE n. Msg n = shd y))) \<bullet> tsh na (q + (THE n. Msg n = shd y)) (srt\<cdot>y)"
    using a2 a1 by (simp add: mono_tsh_helper monofun_cfun)
qed

lemma cont_lub_tsum5_helper2:
  "\<forall>s y. stake n\<cdot> (tsh n y s) = tsh n y s "
by(induct_tac n,auto)

lemma tsum5_helper_snth_stake_min:
  "snth n (stake m\<cdot> (tsh m p s)) = snth (min n m) (tsh m p s)"
apply (induct_tac n,auto)
using cont_lub_tsum5_helper2 apply auto[1]
by (metis cont_lub_tsum5_helper2 min_def sdropostake snth_def stakeostake)

(* tsum5_helper is a continuous function *)
lemma cont_lub_tsum5_helper: "cont (\<lambda> s. \<Squnion>i. tsh i p s)" 
apply (rule cont2cont_lub)
apply (rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "p"])
apply (rule chainE)
apply (metis (no_types, lifting) chain_tsh)
apply (rule pr_contI)
apply (rule monofunI)
apply (rule mono_tsh [rule_format], assumption)
apply (rule allI)
apply (rule_tac x="i" in exI)
by (rule contlub_tsh [rule_format])

lemma tsum5_helper_scons[simp]:"a\<noteq>\<surd> \<Longrightarrow> tsum5_helper n \<cdot>(\<up>a\<bullet>s) = (\<up>(Msg(n+(THE n. Msg n = a)))) \<bullet> (tsum5_helper (n+(THE n. Msg n = a))\<cdot>s)"  
apply (simp add: tsum5_helper_def)
apply (subst beta_cfun, rule cont_lub_tsum5_helper)+
apply (subst contlub_cfun_arg)
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
by (simp add: chain_tsh_helper)

lemma tsum5_helper_scons_tick[simp]:"tsum5_helper n \<cdot>(\<up>\<surd>\<bullet>s) = \<up>\<surd> \<bullet> (tsum5_helper n \<cdot>s)"
apply (simp add: tsum5_helper_def)
apply (subst beta_cfun, rule cont_lub_tsum5_helper)+
apply (subst contlub_cfun_arg)
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
by (simp add: chain_tsh_helper)

lemma tsum5_empty[simp]: "tsum5_helper p\<cdot>\<epsilon> = \<epsilon>"
by (simp add: cont_lub_tsum5_helper tsh_bot tsum5_helper_def)

lemma tsum5_helper_unfold_h: "tsum5_helper n \<cdot>input = (\<Squnion>i. tsh i n input)"
apply (simp add:tsum5_helper_def)
by (simp add: cont_lub_tsum5_helper)

lemma msg_plus0[simp]:" \<forall>(a:: nat event). a\<noteq>\<surd> \<Longrightarrow>Msg ((THE n. Msg n = a)+0) = a"
by auto

lemma tsum5_helper_shd [simp]: "a\<noteq>\<surd> \<Longrightarrow> shd (tsum5_helper n \<cdot>(\<up>a \<bullet> as)) = Msg ((THE n. Msg n = a)+n)"
by simp

lemma [simp]: "a\<noteq>\<surd> \<Longrightarrow> tsum5_helper n\<cdot>(\<up>a) = (\<up>(Msg(n+(THE n. Msg n = a))))"
by (metis lscons_conv sup'_def tsum5_empty tsum5_helper_scons)

lemma fair2_tsum5_helper: "#x \<le> #(tsum5_helper a\<cdot>x)"
apply (rule spec [where x = a])
apply (rule ind [of _ x], auto)
apply(subst lnle_def, simp del: lnle_conv)
by (smt lnsuc_lnle_emb slen_scons tsum5_helper_scons tsum5_helper_scons_tick)

lemma tsum5_helper_srt_tick: "shd s=\<surd> \<Longrightarrow>srt\<cdot>(tsum5_helper n \<cdot>s) = tsum5_helper n\<cdot> (srt\<cdot>s)"
by (metis (no_types, lifting) inject_scons lshd_updis stream.sel_rews(2) stream.sel_rews(3) surj_scons tsum5_empty tsum5_helper_scons_tick)


lemma tsum5_helper_srt: "shd s\<noteq>\<surd> \<Longrightarrow>srt\<cdot>(tsum5_helper n \<cdot>s) = tsum5_helper (n+(THE n. Msg n = shd s))\<cdot> (srt\<cdot>s)"
apply(cases "s=\<epsilon>")
apply simp
using tsum5_helper_scons
proof -
  assume a1: "s \<noteq> \<epsilon>"
  assume a2: "shd s \<noteq> \<surd>"
  have f3: "\<up>(shd s) \<bullet> srt\<cdot>s = s"
    using a1 by (metis surj_scons)
  have "\<And>e s. updis (e::nat event) \<noteq> \<bottom> \<or> (\<epsilon>::nat event stream) = s"
    by simp
  then show ?thesis
    using f3 a2 a1 by (metis lscons_conv stream.sel_rews(5) tsum5_helper_scons)
qed

lemma fair_tsum5_helper[simp]: "#(tsum5_helper n\<cdot>x) = #x"
apply (rule spec [where x = n])
apply (rule ind [of _ x], auto)
using tsum5_helper_scons
by (metis slen_scons tsum5_helper_scons_tick)

lemma tsum5_helper_test_helper1: "tsum5_helper 0\<cdot>(<[Msg 1,\<surd>,Msg 2,\<surd>,\<surd>,Msg 4]>) =(<[Msg 1,\<surd>,Msg 3,\<surd>,\<surd>,Msg 7]>)"
by simp

lemma tsum5_helper_test_helper2: "tsum5_helper n \<cdot>(sinftimes(\<up>\<surd>)) = sinftimes(\<up>\<surd>)"
by (metis s2sinftimes sinftimes_unfold tsum5_helper_scons_tick)

lemma tsum5_helper_test: "tsum5_helper 0 \<cdot>((<[Msg 1,\<surd>,Msg 2,\<surd>,\<surd>,Msg 4]>) \<bullet> (sinftimes(\<up>\<surd>))) = ((<[Msg 1,\<surd>,Msg 3,\<surd>,\<surd>,Msg 7]>) \<bullet> (sinftimes(\<up>\<surd>)))"
using tsum5_helper_test_helper1 tsum5_helper_test_helper2
by simp

lemma tswell_test: "ts_well ((<[Msg 1,\<surd>,Msg 2,\<surd>,\<surd>,Msg 4]>) \<bullet> (sinftimes(\<up>\<surd>)))"
by(simp add: ts_well_def)

(*
lemma tsum5_helper_tick: "#as1<\<infinity> \<Longrightarrow> \<exists>x. tsum5_helper n \<cdot>(as1\<bullet> (\<up>\<surd>)\<bullet>as2) = (tsum5_helper n\<cdot>as1)\<bullet>(\<up>\<surd>)\<bullet>(tsum5_helper x\<cdot>as2)"
*)

lemma tsum5_unfold: "tsum5\<cdot> ts = Abs_tstream (tsum5_helper 0\<cdot> (Rep_tstream ts))"
using cont_lub_tsum5_helper
sorry

lemma tssum5_test:"tsum5\<cdot> (Abs_tstream ((<[Msg 1,\<surd>,Msg 2,\<surd>,\<surd>,Msg 4]>) \<bullet> (sinftimes(\<up>\<surd>))))
 =(Abs_tstream ((<[Msg 1,\<surd>,Msg 3,\<surd>,\<surd>,Msg 7]>) \<bullet> (sinftimes(\<up>\<surd>))))"
apply(simp add: tsum5_unfold)
apply (subst Rep_Abs)
using tswell_test apply auto
using tsum5_helper_test_helper2 by auto

lemma tsum5_foot_tick[simp]: "#as < \<infinity> \<Longrightarrow>tsum5_helper n \<cdot>(as\<bullet> (\<up>\<surd>)) = (tsum5_helper n\<cdot> as) \<bullet> (\<up>\<surd>)"

sorry

lemma tsum5_helper_filter_tick: "#as <\<infinity> \<Longrightarrow> ts_well (tsum5_helper n \<cdot>(as\<bullet> (\<up>\<surd>)))"
apply(subst tsum5_foot_tick, auto)
apply(simp add: ts_well_def)
by blast

lemma tswell2tsum5_helper: "ts_well ts \<Longrightarrow> ts_well (tsum5_helper n\<cdot>ts)"
apply(subst ts_well_def)
apply(cases "ts=\<epsilon>")
apply simp
apply(cases "#ts<\<infinity>")
apply(cases "sfoot ts=\<surd>")
apply (metis fair_tsum5_helper inf_less_eq leI sconc_fst_inf ts_fin_well tsum5_foot_tick)
using ts_finite_sfoot apply blast
sorry

lemma tsum5_slen[simp]:"#(Rep_tstream (tsum5\<cdot>x)) = #(Rep_tstream x)"
apply (simp add: tsum5_unfold)
apply (subst Rep_Abs)
using tswell2tsum5_helper
by auto

(*
lemma sfilter_tick_eq: "tsum5_helper n\<cdot>(sfilter {e. e \<noteq> \<surd>}\<cdot> s) = sfilter {e. e \<noteq> \<surd>}\<cdot>(tsum5_helper n\<cdot>s)"
apply(cases "s=\<epsilon>")
apply simp
apply(cases "#s<\<infinity>")
using add_sfilter2 tsum5_helper_scons tsum5_helper_scons_tick
sorry


lemma test2_tsum5_helper_helper: "Fin (Suc n)<#(sfilter {e. e \<noteq> \<surd>}\<cdot> as) \<Longrightarrow> snth (Suc n) (sfilter {e. e \<noteq> \<surd>}\<cdot> (tsum5_helper x \<cdot>as))
                                 = Msg((THE n. Msg n = snth (Suc n) (sfilter {e. e \<noteq> \<surd>}\<cdot> as)) 
                                 + (THE n. Msg n = snth n (sfilter {e. e \<noteq> \<surd>}\<cdot> (tsum5_helper x \<cdot>as))))"
apply(induction n arbitrary: x as)
sorry

lemma test2_tsum5_helper: "Fin (Suc n)<#(sfilter {e. e \<noteq>\<surd>} \<cdot>(Rep_tstream as)) \<Longrightarrow> 
                             snth (Suc n) ((sfilter {e. e \<noteq>\<surd>} \<cdot>(Rep_tstream(tsum5\<cdot>as))))
                           = Msg((THE n. Msg n = snth (Suc n) (sfilter {e. e \<noteq>\<surd>}\<cdot>(Rep_tstream as)))
                              + (THE n. Msg n = snth n ((sfilter {e. e \<noteq>\<surd>}\<cdot>(Rep_tstream (tsum5\<cdot>as))))))"
using tsum5_def test2_tsum5_helper_helper
sorry
*)

end