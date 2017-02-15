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


definition tsum5:: "nat tstream \<Rightarrow> nat tstream" where
"tsum5 ts \<equiv> Abs_tstream (tsum5_helper 0\<cdot>(Rep_tstream ts))"



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
apply (rule fun_belowD [of _ _ "a"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "a"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
by (simp add: chain_tsh_helper)

lemma tsum5_helper_scons_tick[simp]:"tsum5_helper n \<cdot>(\<up>\<surd>\<bullet>s) = \<up>\<surd> \<bullet> (tsum5_helper n \<cdot>s)"
apply (simp add: tsum5_helper_def)
apply (subst beta_cfun, rule cont_lub_tsum5_helper)+
apply (subst contlub_cfun_arg)
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "n"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "n"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
by (simp add: chain_tsh_helper)

lemma tsum5_empty[simp]: "tsum5_helper p\<cdot>\<epsilon> = \<epsilon>"
by (simp add: cont_lub_tsum5_helper tsh_bot tsum5_helper_def)

lemma tsum5_helper_unfold_tsh: "tsum5_helper n \<cdot>input = (\<Squnion>i. tsh i n input)"
apply (simp add:tsum5_helper_def)
by (simp add: cont_lub_tsum5_helper)

lemma msg_plus0[simp]:fixes a::"nat event" shows" a\<noteq>\<surd> \<Longrightarrow>Msg (0+(THE n. Msg n = a)) = a"
by (smt add.left_neutral event.exhaust event.inject the1_equality)

lemma tsum5_helper_shd [simp]: "a\<noteq>\<surd> \<Longrightarrow> shd (tsum5_helper n \<cdot>(\<up>a \<bullet> as)) = Msg (n+(THE n. Msg n = a))"
by simp

lemma tsum5_unfold: "tsum5 ts = Abs_tstream (tsum5_helper 0\<cdot> (Rep_tstream ts))"
by(simp add: tsum5_def)

lemma "#({\<surd>} \<ominus> s) = Fin (Suc n) \<Longrightarrow> ({\<surd>} \<ominus> s)= (\<up>\<surd>)\<bullet>(srt\<cdot>({\<surd>} \<ominus> s))"
by (metis Fin_02bot inject_Fin lnzero_def nat.simps(3) sfilter_resl2 singletonD slen_empty_eq surj_scons)



lemma fair2_tsum5_helper: "#x \<le> #(tsum5_helper a\<cdot>x)"
apply (rule spec [where x = a])
apply (rule ind [of _ x], auto)
apply(subst lnle_def, simp del: lnle_conv)
by (smt lnsuc_lnle_emb slen_scons tsum5_helper_scons tsum5_helper_scons_tick)

lemma tsum5_helper_srt_tick[simp]: "shd s=\<surd> \<Longrightarrow>srt\<cdot>(tsum5_helper n \<cdot>s) = tsum5_helper n\<cdot> (srt\<cdot>s)"
by (metis (no_types, lifting) inject_scons lshd_updis stream.sel_rews(2) stream.sel_rews(3) surj_scons tsum5_empty tsum5_helper_scons_tick)


lemma tsum5_helper_srt[simp]: "shd s\<noteq>\<surd> \<Longrightarrow>srt\<cdot>(tsum5_helper n \<cdot>s) = tsum5_helper (n+(THE n. Msg n = shd s))\<cdot> (srt\<cdot>s)"
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
   
lemma [simp]: "a\<noteq>\<surd> \<Longrightarrow> tsum5_helper n\<cdot>(\<up>a) = (\<up>(Msg(n+(THE n. Msg n = a))))"
by (metis lscons_conv sup'_def tsum5_empty tsum5_helper_scons)




lemma tswell_test: "ts_well ((<[Msg 1,\<surd>,Msg 2,\<surd>,\<surd>,Msg 4]>) \<bullet> (sinftimes(\<up>\<surd>)))"
by(simp add: ts_well_def)

lemma tsum5_helper_test_helper1: "tsum5_helper 0\<cdot>(<[Msg 1,\<surd>,Msg 2,\<surd>,\<surd>,Msg 4]>) =(<[Msg 1,\<surd>,Msg 3,\<surd>,\<surd>,Msg 7]>)"
by simp

lemma tsum5_helper_test_helper2: "tsum5_helper n \<cdot>(sinftimes(\<up>\<surd>)) = sinftimes(\<up>\<surd>)"
by (metis s2sinftimes sinftimes_unfold tsum5_helper_scons_tick)

lemma tsum5_helper_test: "tsum5_helper 0 \<cdot>((<[Msg 1,\<surd>,Msg 2,\<surd>,\<surd>,Msg 4]>) \<bullet> (sinftimes(\<up>\<surd>))) = ((<[Msg 1,\<surd>,Msg 3,\<surd>,\<surd>,Msg 7]>) \<bullet> (sinftimes(\<up>\<surd>)))"
using tsum5_helper_test_helper1 tsum5_helper_test_helper2
by simp

lemma tssum5_test:"tsum5 (Abs_tstream ((<[Msg 1,\<surd>,Msg 2,\<surd>,\<surd>,Msg 4]>) \<bullet> (sinftimes(\<up>\<surd>))))
 =(Abs_tstream ((<[Msg 1,\<surd>,Msg 3,\<surd>,\<surd>,Msg 7]>) \<bullet> (sinftimes(\<up>\<surd>))))"
apply(simp add: tsum5_unfold)
apply (subst Rep_Abs)
using tswell_test apply auto
using tsum5_helper_test_helper2 by auto


(*tsAbs(tsum5 ts) = sum5(tsAbs ts)*)


lemma tsum5_helper_scons_2[simp]: "s=\<up>\<surd>\<bullet>as \<Longrightarrow> tsum5_helper n\<cdot>s = (\<up>\<surd>)\<bullet>(tsum5_helper n\<cdot> as)"
by simp

lemma tsum5_tswell:"ts_well s \<Longrightarrow> ts_well (tsum5_helper n\<cdot>s)"
apply(cases "s=\<epsilon>")
apply simp
apply(cases "#s<\<infinity>")
apply(subst ts_well_def)
apply simp
sorry

lemma tsabs_tsum5_helper_tick[simp]: "ts_well as \<Longrightarrow> tsAbs\<cdot>(Abs_tstream(tsum5_helper n \<cdot>(\<up>\<surd>\<bullet>as))) = tsAbs\<cdot>(Abs_tstream(tsum5_helper n\<cdot>as))"
apply(simp)
using AbsStsAbs_tick tsum5_tswell by blast

lemma tsabstsum5_insert:"ts_well as \<Longrightarrow> (tsAbs\<cdot>(Abs_tstream(tsum5_helper n \<cdot>as))) =smap (\<lambda>e. case e of Msg m \<Rightarrow> m)\<cdot>({e. e \<noteq> \<surd>} \<ominus> (tsum5_helper n \<cdot>as))"
by(simp add: tsabs_insert tsum5_tswell)
(*
lemma slen_tsum5helper:"ts_well s \<Longrightarrow> #\<surd>(Abs_tstream((tsum5_helper 0\<cdot>s))) = #\<surd>(Abs_tstream s)"
apply(simp add: tsTickCount_def)
apply(subst Rep_Abs)
using tsum5_tswell apply blast
sorry
*)
lemma slen_tsum5sum5[simp]:"ts_well s \<Longrightarrow> #(tsAbs\<cdot>(Abs_tstream (tsum5_helper 0\<cdot>s))) = #(tsAbs\<cdot>(Abs_tstream s))"
apply(simp add: tsabs_insert)
apply(subst Rep_Abs)
using tsum5_tswell apply blast
sorry

lemma tsAbs_sconc[simp]:"\<forall> a::nat event. a\<noteq>\<surd> \<and>ts_well as \<Longrightarrow> tsAbs\<cdot>(Abs_tstream((\<up>(Msg (n+(THE n. Msg n = a))))\<bullet>as))
                                                               = \<up>(n+(THE n. Msg n = a))\<bullet> tsAbs\<cdot>(Abs_tstream as)"
by auto

lemma tsAbs_tick[simp]: "shd (tsAbs\<cdot>((Abs_tstream(\<up>\<surd>))\<bullet>ts)) = shd (tsAbs\<cdot>ts)"
by auto

lemma sfilter_tick_unfold[simp]:"{e. e \<noteq> \<surd>} \<ominus> (tsum5_helper 0 \<cdot>(\<up>\<surd>\<bullet>ts)) = {e. e \<noteq> \<surd>} \<ominus> (tsum5_helper 0 \<cdot>(ts))"
by simp

lemma sfilter_notick_unfold[simp]:"a\<noteq>\<surd> \<Longrightarrow>{e. e \<noteq> \<surd>} \<ominus> (tsum5_helper 0 \<cdot>(\<up>a\<bullet>ts)) = \<up>a \<bullet> {e. e \<noteq> \<surd>} \<ominus> (tsum5_helper (THE n. Msg n = a) \<cdot>(ts))"
apply(subst tsum5_helper_scons)
apply simp
apply(subst sfilter_in)
apply simp
apply(subst msg_plus0)
apply simp
by simp

lemma sfilter_tsum5_insert:"{e. e \<noteq> \<surd>} \<ominus> (tsum5_helper 0 \<cdot>(ts))=tsum5_helper 0 \<cdot>(({e. e \<noteq> \<surd>} \<ominus> ts))"
sorry

lemma tsAbs_tsum5_insert:"ts_well ts \<Longrightarrow>tsAbs\<cdot>(Abs_tstream(tsum5_helper 0\<cdot>ts)) = smap (\<lambda>e. case e of Msg m \<Rightarrow> m)\<cdot>(tsum5_helper 0 \<cdot>(({e. e \<noteq> \<surd>} \<ominus> ts)))"
apply(simp add: tsabs_insert)
apply(subst Rep_Abs)
using tsum5_tswell apply blast
by(simp add: sfilter_tsum5_insert)


lemma sfilter_shd_nottick:"ts\<noteq>\<epsilon> \<Longrightarrow>shd ({e. e \<noteq> \<surd>} \<ominus> ts)\<noteq>\<surd>"
sorry

lemma sfilter_shd_nottick2:"({e. e \<noteq> \<surd>} \<ominus> ts)\<noteq>\<epsilon> \<Longrightarrow> shd ({e. e \<noteq> \<surd>} \<ominus> ts) \<noteq>\<surd>"
using sfilter_shd_nottick by fastforce 

lemma sfilter_tsum5_sconc:"({e. e \<noteq> \<surd>} \<ominus> ts)\<noteq>\<epsilon> \<Longrightarrow>tsum5_helper n\<cdot>({e. e \<noteq> \<surd>} \<ominus> ts) = (\<up>(Msg (n+ (THE m. Msg m = shd(({e. e \<noteq> \<surd>} \<ominus> ts))))))\<bullet> 
                    (tsum5_helper (n+ (THE m. Msg m = shd(({e. e \<noteq> \<surd>} \<ominus> ts)))) \<cdot>(srt\<cdot>(({e. e \<noteq> \<surd>} \<ominus> ts))))"
using sfilter_shd_nottick2 tsum5_helper_scons
by (metis surj_scons)

lemma sum5_shd_helper:"({e. e \<noteq> \<surd>} \<ominus> ts)\<noteq>\<epsilon> \<Longrightarrow> ({e. e \<noteq> \<surd>} \<ominus> ts) = \<up>(shd({e. e \<noteq> \<surd>} \<ominus> ts)) \<bullet> (srt\<cdot>({e. e \<noteq> \<surd>} \<ominus> ts))"
by (simp add: surj_scons)
(*
lemma shd_tsabs_helper[simp]: "shd ts\<noteq>\<surd> \<and>ts\<noteq>\<epsilon> \<Longrightarrow> shd (tsAbs\<cdot>(Abs_tstream ts)) = (THE m. Msg m = shd ts)"
sorry
*)

lemma[simp]:"ts_well ts \<and>(({e. e \<noteq> \<surd>} \<ominus> ts))\<noteq>\<epsilon>\<Longrightarrow> shd (tsAbs\<cdot>(Abs_tstream ts)) = shd(\<up>(THE m. Msg m = shd ({e. e \<noteq> \<surd>} \<ominus> ts))\<bullet>(tsAbs\<cdot>(Abs_tstream(srt\<cdot>({e. e \<noteq> \<surd>} \<ominus> ts)))))"
sorry

lemma tsum5_shd: "ts_well ts \<Longrightarrow> shd (tsAbs\<cdot>(Abs_tstream(tsum5_helper 0\<cdot> ts))) = shd (tsAbs\<cdot>(Abs_tstream ts))"
apply(cases "ts=\<epsilon>")
apply simp
apply(simp add: tsAbs_tsum5_insert)
apply(cases "({e. e \<noteq> \<surd>} \<ominus> ts) = \<epsilon>")
apply simp
using slen_tsum5sum5 tsAbs_tsum5_insert apply fastforce
by(simp add: sfilter_tsum5_sconc)



lemma tsabs_helper:"shd s=\<surd> \<and> ts_well s \<Longrightarrow>(tsAbs\<cdot>(Abs_tstream(tsum5_helper n \<cdot>s))) =(tsAbs\<cdot>(Abs_tstream(tsum5_helper n \<cdot>(srt\<cdot>s))))"
by (metis stream.sel_rews(2) surj_scons ts_well_drop1 tsabs_tsum5_helper_tick)

lemma tsabs_helper2:"shd s\<noteq>\<surd> \<and> ts_well s \<Longrightarrow>(tsAbs\<cdot>(Abs_tstream(tsum5_helper n \<cdot>s))) =\<up>(n+(THE n. Msg n = shd s))\<bullet>(tsAbs\<cdot>(Abs_tstream(tsum5_helper (n+(THE n. Msg n = shd s)) \<cdot>(srt\<cdot>s))))"
using tsum5_helper_scons
sorry


lemma tsabs_tsum5_helper_srt_tick: "shd s=\<surd> \<and> ts_well s\<Longrightarrow>srt\<cdot>(tsAbs\<cdot>(Abs_tstream(tsum5_helper n \<cdot>s))) = srt\<cdot>(tsAbs\<cdot>(Abs_tstream(tsum5_helper n\<cdot> (srt\<cdot>s))))"
by (simp add: tsabs_helper)


lemma tsabs_tsum5_helper_srt_notick: "shd s\<noteq>\<surd> \<and> ts_well s\<Longrightarrow>srt\<cdot>(tsAbs\<cdot>(Abs_tstream(tsum5_helper n \<cdot>s))) = (tsAbs\<cdot>(Abs_tstream(tsum5_helper (n+(THE n. Msg n = shd s))\<cdot> (srt\<cdot>s))))"
apply(subst tsabs_helper2)
apply simp
by (simp add: natl2)

lemma test2_tsum5_helper_helper: "Fin (Suc n)< #(tsAbs\<cdot>(Abs_tstream as))\<and> ts_well as\<Longrightarrow>
                                    snth (Suc n) (tsAbs\<cdot>(Abs_tstream (tsum5_helper 0 \<cdot>as)))
                                  = snth (Suc n) (tsAbs\<cdot>(Abs_tstream as)) + snth n (tsAbs\<cdot>(Abs_tstream (tsum5_helper 0 \<cdot>as)))"
apply(induction n arbitrary: as)
apply (simp add: tsum5_shd)
sorry


lemma tsum5_helper_snth:"Fin (Suc n) < #(tsAbs\<cdot>as) \<Longrightarrow> snth (Suc n) (tsAbs\<cdot>(tsum5 as)) = snth (Suc n) (tsAbs\<cdot>as) + snth n (tsAbs\<cdot>(tsum5 as))"
apply(simp add: tsum5_unfold)
using test2_tsum5_helper_helper
using Abs_Rep by auto

lemma tsum5_helper_sum5snth:"(Fin n < #(tsAbs\<cdot>(Abs_tstream s)) \<and> ts_well s) \<longrightarrow> snth n (tsAbs\<cdot>(Abs_tstream (tsum5_helper 0\<cdot>s))) = snth n (sum5 \<cdot>(tsAbs\<cdot>(Abs_tstream s)))"
apply(induction n arbitrary: s)
apply simp
using test2_sum5_helper test2_tsum5_helper_helper tsum5_helper_snth
apply (metis snth_shd sum4_snth0 sum52sum4 tsum5_shd)
by (metis Fin_leq_Suc_leq Suc_n_not_le_n less2nat_lemma less_le test2_sum5_helper test2_tsum5_helper_helper)


lemma tsum5_helper2sum5: "ts_well s \<Longrightarrow> tsAbs\<cdot>(Abs_tstream (tsum5_helper 0\<cdot>s)) = sum5 \<cdot>(tsAbs\<cdot>(Abs_tstream s))"
apply(simp add: tsabs_insert)
apply(simp add: tsum5_tswell)
apply(rule snths_eq)
apply (metis slen_tsum5sum5 sum5_slen tsabs_rep_eq tsum5_tswell)
using tsum5_helper_sum5snth
by (metis slen_tsum5sum5 tsabs_rep_eq tsum5_tswell)


thm tsum5_def

lemma tsum52sum5:"tsAbs\<cdot>(tsum5 ts) = sum5\<cdot>(tsAbs\<cdot> ts)"
apply(simp add: tsum5_unfold)
using tsum5_helper2sum5
by (simp add: ts_well_Rep)


(*
lemma tsum5_foot_tick[simp]: "#as < \<infinity> \<Longrightarrow>tsum5_helper n \<cdot>(as\<bullet> (\<up>\<surd>)) = (tsum5_helper n\<cdot> as) \<bullet> (\<up>\<surd>)"
sorry

lemma tsum5_helper_filter_tick: "#as <\<infinity> \<Longrightarrow> ts_well (tsum5_helper n \<cdot>(as\<bullet> (\<up>\<surd>)))"
apply(subst tsum5_foot_tick, auto)
apply(simp add: ts_well_def)
by blast

lemma sdrop_hdtick[simp]:"sdrop (Suc n)\<cdot> (tsum5_helper p\<cdot>(\<up>\<surd>\<bullet>ts)) = sdrop n\<cdot> (tsum5_helper p\<cdot>ts)"
by simp

lemma sdrop_hd[simp]:"a\<noteq>\<surd> \<Longrightarrow> sdrop (Suc n)\<cdot> (tsum5_helper p\<cdot>(\<up>a\<bullet>ts)) = sdrop n\<cdot> (tsum5_helper (p+(THE n. Msg n = a))\<cdot>ts)"
by simp

lemma sum5_sdrop_srt:"shd ts= \<surd> \<Longrightarrow> sdrop n\<cdot>(tsum5_helper p\<cdot> (srt\<cdot>ts)) = srt\<cdot>(sdrop n\<cdot>(tsum5_helper p\<cdot> ts))"
by (metis sdrop_back_rt sdrop_forw_rt tsum5_helper_srt_tick)


lemma snth_tick_tsum5_helper: "snth n ts = \<surd> \<longleftrightarrow> snth n (tsum5_helper p\<cdot>ts) = \<surd>"
apply(induction n)
apply (metis event.simps(3) shd1 snth_shd surj_scons tsum5_empty tsum5_helper_scons_tick tsum5_helper_shd)
using tsum5_helper_scons_tick
apply(simp add: snth_def)
apply(cases "ts=\<epsilon>")
apply simp
sorry

lemma sfiltertick_tsum5_helper:"#({\<surd>} \<ominus> tsum5_helper n\<cdot>ts) = #({\<surd>} \<ominus> ts)"
apply(cases "ts=\<epsilon>")
apply simp
sorry

lemma tswell2tsum5_helper: "ts_well ts \<Longrightarrow> ts_well (tsum5_helper n\<cdot>ts)"
apply(subst ts_well_def)
apply(cases "ts=\<epsilon>")
apply simp
apply(cases "#ts<\<infinity>")
apply(cases "sfoot ts=\<surd>")
apply (metis fair_tsum5_helper inf_less_eq leI sconc_fst_inf ts_fin_well tsum5_foot_tick)
using ts_finite_sfoot apply blast
apply auto
proof -
  fix ts::"nat event stream"
  assume a1: "ts_well ts"
  assume a2: "ts \<noteq> \<epsilon>"
  assume a3: "\<not>#ts < \<infinity>"
  have f4: "#({\<surd>} \<ominus> ts) = \<infinity>"
by (metis Rep_Abs a1 a2 a3 sConc_Rep_fin_fin surj_scons ts_well_drop1)
  then show "#({\<surd>} \<ominus> tsum5_helper n\<cdot>ts) \<noteq> \<infinity> \<Longrightarrow> tsum5_helper n\<cdot>ts = \<epsilon>"
    using f4 a3 a2 a1 sfiltertick_tsum5_helper by auto
qed

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
*)

end