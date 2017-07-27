(*  Title:        TStream_JB.thy
    Author:       Jens Christoph Bürger
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  additional definitions + lemmas over tstreams
                  should be merged later with TStream
*)

theory TStream_JB
  imports Channel OptionCpo TStream

begin

(* ----------------------------------------------------------------------- *)
  section \<open>definitions\<close>
(* ----------------------------------------------------------------------- *)

(* take the first n time slots, uses lnat instead of nat *)
definition tsTakeL :: "lnat \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsTakeL \<equiv> (\<Lambda> l ts. if l = \<infinity> then ts else (ts \<down> (THE n. Fin n = l)))"


(* ----------------------------------------------------------------------- *)
  section \<open>general lemmas\<close>
(* ----------------------------------------------------------------------- *)

   (* important general lemma *)
lemma chain_lub_eqI: assumes "chain (Y::nat \<Rightarrow> 'a::cpo)" and "chain (Z::nat \<Rightarrow> 'a::cpo)"
  and "\<forall> i. \<exists>j. Y i \<sqsubseteq> Z j"
  and "\<forall> j. \<exists>i. Z j \<sqsubseteq> Y i"
shows "(\<Squnion>i. Y i) = (\<Squnion>i. Z i)"
  by (metis (no_types, hide_lams) assms(1) assms(2) assms(3) assms(4) below_trans is_ub_thelub
            lub_below po_eq_conv)

 (* not useful *)
lemma test34: assumes "chain (Y::nat \<Rightarrow> 'a::cpo)"
  shows "\<forall> i. Y i \<sqsubseteq> (\<Squnion> i. Y i)"
  by (simp add: assms is_ub_thelub)

lemma asym_insert: assumes "(a::'a tstream) \<sqsubseteq> b" and "b \<sqsubseteq> a"
  shows "a = b"
  by (simp add: assms(1) assms(2) po_eq_conv)

(* ----------------------------------------------------------------------- *)
  section \<open>lemmas\<close>
(* ----------------------------------------------------------------------- *)

  subsection \<open>tsTakeL\<close>
lemma tstake_mono1: assumes "x \<le> y"
  shows "(ts \<down> x) \<sqsubseteq> (ts \<down> y)"
  by (metis assms tsTake2take tsTake_prefix tstake_less)
    
lemma tstake_belowI: assumes "i \<le> j"
  shows "(ts \<down> i) \<sqsubseteq> (ts \<down> j)"
  by (simp add: assms tstake_mono1)
    
    
subsection \<open>tsTakeL\<close>

  
subsubsection \<open>cont_2nd_arg\<close>
lemma conttsTakeL1[simp]: "cont (\<lambda> ts. if l = \<infinity> then ts else (ts \<down> (THE n. Fin n = l)))"
  by simp

    
subsubsection \<open>cont_1st_arg\<close>    
  
lemma ttsTakeL2_monofun_pre: assumes "x \<sqsubseteq> y"
  shows "(if x = \<infinity> then ts else (ts \<down> THE n. (Fin n = x)) ) 
          \<sqsubseteq> (if y = \<infinity> then ts else (ts \<down> THE n. (Fin n = y)) )"
proof (cases "y = \<infinity>")
  case True
  then show ?thesis
    by auto
next
  case False
  have f1: "y < \<infinity>"
  by (simp add: False less_le)
  obtain j where f2: "y = Fin j"
    by (metis f1 infI neq_iff)
  have f3: "x < \<infinity>"
    using assms f2 less_le by fastforce
  obtain k where f4: "x = Fin k"
    by (metis f3 infI neq_iff)
  have f5: "k \<le> j"
    using assms f2 f4 less2nat_lemma lnle_conv by blast
  then show ?thesis
    apply (simp add: f1 f2 f4)
    by (metis tsTake2take tsTake_prefix tstake_less)
qed

lemma chain_tsTakeL2: assumes "chain Y"
  shows "chain (\<lambda> i. if Y i = \<infinity> then ts else (ts \<down> THE n. (Fin n = Y i)) )"
proof (rule chainI)
  fix i
  have "Y i \<sqsubseteq> Y (Suc i)"
    using assms po_class.chainE by blast
  thus "(if Y i = \<infinity> then ts else (ts \<down> THE n. (Fin n = (Y i))) ) 
          \<sqsubseteq> (if Y (Suc i) = \<infinity> then ts else (ts \<down> THE n. (Fin n = (Y (Suc i)))) )"
    using ttsTakeL2_monofun_pre by blast
qed




lemma chain_tsTakeL23[simp]: assumes "chain Y" and "\<And>i. Y i \<noteq> \<infinity>"
  shows "chain (\<lambda> i. (ts \<down> THE n. (Fin n = Y i)) )"
proof -
  have f1: "\<And> i. (ts \<down> THE n. (Fin n = Y i)) 
                  = (if Y i = \<infinity> then ts else (ts \<down> THE n. (Fin n = (Y i))) )"
    by (simp add: assms)
  show ?thesis
    apply (subst f1)
      by (simp add: chain_tsTakeL2 assms(1))
qed


lemma conttsTakeL2_cont_pre: assumes "chain Y"
  shows "(if (\<Squnion>i. Y i) = \<infinity> then ts else (ts \<down> THE n. (Fin n = (\<Squnion>i. Y i))) )
          \<sqsubseteq> (\<Squnion>i. if Y i = \<infinity> then ts else (ts \<down> THE n. (Fin n = Y i)) )"
proof (cases "\<forall>i. Y i \<noteq> \<infinity>")
  case True
  have x1: "\<forall> i. \<exists> j. (Fin j) = (Y i)"
  proof -
    fix i
    have "(Y i) < \<infinity>"
      by (simp add: True less_le)
    thus ?thesis
      by (metis True infI)
  qed


  have t1: "(\<Squnion>i. if Y i = \<infinity> then ts else (ts \<down> THE n. (Fin n = Y i)))
            = (\<Squnion>i. (ts \<down> THE n. (Fin n = Y i)))"
      by (simp add: True)
    show ?thesis
      proof (cases "(\<Squnion>i. Y i) = \<infinity>")
        case True
        (* no chain element is \<infinity> but lub is \<infinity> *)
        have t100: "\<And>j::nat. \<exists>i::nat.  j  \<le> ( THE n::nat. Fin n = Y i)"
          proof -
            fix j::nat
              obtain k where t102: "Fin j \<sqsubseteq> Y k"
                by (metis LNat.inf_chainl3 True assms finite_chainE inf_ub lnle_def 
                          maxinch_is_thelub)
              obtain l where t103: "Y k = (Fin l)"
                by (metis x1)
              have t104: "j \<le> l"
                proof -
                  have "Fin j \<sqsubseteq> Fin l"
                    using t102 t103 by auto
                  thus ?thesis
                    by simp
                qed
              hence "j \<le> (THE n::nat. Fin n = Y k)"
                by (subst t103, simp)
              thus "\<exists> i. j  \<le> ( THE n::nat. Fin n = Y i)"
                by auto
          qed

        have t10: "(\<Squnion>i. (ts \<down> THE n. (Fin n = Y i))) = (\<Squnion>i. (ts \<down> i ) )"
          apply(rule chain_lub_eqI, simp_all add: assms)
            apply (metis Fin_neq_inf assms chain_tsTakeL23 x1)
            apply auto[1]
            using t100 tstake_mono1 x1 by blast

        show ?thesis
          apply (simp only: t1 True)
          by (subst t10, simp)
      next
        case False
          (* neither lub nor chain element is \<infinity> *)
          obtain j where b1: "Y j = (\<Squnion>i. Y i)"
            using False assms l42 unique_inf_lub by fastforce
          obtain k where b3: "Y j = Fin k"
            by (metis True infI)
          have b2: "(\<Squnion>i. (ts \<down> THE n. (Fin n = Y i))) = (ts \<down> THE n. (Fin n = Y j) )"
            apply (rule lub_chain_maxelem, simp_all)
            apply (subst tstake_mono1, simp_all)
            apply (simp add: b3)
          proof -
            fix i
            have b5: "Y i \<sqsubseteq> Y j"
              using assms b1 is_ub_thelub by fastforce
            obtain k2 where b4: "Y i = Fin k2"
              using True infI by blast
            thus "(THE n. Fin n = Y i) \<le> k"
                using b5 b3 b4 by auto
          qed
        then show ?thesis
          by (simp only: t1 False b2 b1, simp)
      qed

next
  case False
    (* a chain element is \<infinity> *)
    obtain j where f1: "Y j = \<infinity>"
        using False by auto
    have f2: "(\<Squnion>i. Y i) = \<infinity>"
      by (metis False assms inf_less_eq is_ub_thelub lnle_conv)
    moreover
    have f3: "(\<Squnion>i. if Y i = \<infinity> then ts else (ts \<down> THE n. (Fin n = Y i)) )
                = (if Y j = \<infinity> then ts else (ts \<down> THE n. (Fin n = Y j)))"
      apply (rule po_class.below_antisym)
      using assms chain_tsTakeL2 f1 lub_below tsTake_prefix apply fastforce
      using assms below_lub chain_tsTakeL2 by blast
    ultimately
    show ?thesis
      by (simp add: f1)
qed

lemma conttsTakeL2[simp]: "cont (\<lambda> l. \<Lambda> ts. if l = \<infinity> then ts else (ts \<down> (THE n. Fin n = l)))"
  apply (rule cont2cont_LAM, simp_all)
  apply (rule contI2)
   apply (rule monofunI, simp only: ttsTakeL2_monofun_pre)
    using conttsTakeL2_cont_pre by blast

  subsubsection \<open>more\<close>


  
lemma tstakel_zero[simp]: "tsTakeL\<cdot>0\<cdot>ts = \<bottom>"
  by (simp add: tsTakeL_def)
    
lemma tstakel_bot[simp]: "tsTakeL\<cdot>n\<cdot>\<bottom> = \<bottom>"
  by (simp add: tsTakeL_def)
    
lemma [simp]: "Fin 2 = lnsuc\<cdot>(lnsuc\<cdot>(Fin 0))"
  using Fin_Suc numeral_2_eq_2 by presburger
    
lemma nat_lnat_suc: assumes "Fin na = n"
  shows "Fin (Suc na) = lnsuc\<cdot>n"
  using assms by auto
    
lemma nat_lnat_suc2: assumes "Fin n1 = lnsuc\<cdot>n" and "Fin n2 = n"
  shows "Suc (n2) = n1"
  by (metis assms(1) assms(2) inject_Fin nat_lnat_suc)
    
lemma test10:
shows "(THE na::nat. Fin na = lnsuc\<cdot>(Fin n)) = Suc (THE nb::nat. Fin nb = (Fin n))"
  by simp
  
    
lemma test11: assumes "n < \<infinity>"
  shows "\<exists> na.  n = Fin na"
  by (metis assms infI neq_iff)

   
    
lemma tsTakeL_def2: assumes "n < \<infinity>"
shows "tsTakeL\<cdot>(lnsuc\<cdot>n)\<cdot>ts = (tsTakeFirst\<cdot>ts) \<bullet> (tsTakeL\<cdot>n\<cdot>(tsDropFirst\<cdot>ts))"
    proof -
    obtain j where f1: "n = Fin j"
      by (metis assms infI neq_iff)
    hence "(THE na::nat. Fin na = lnsuc\<cdot>n) = Suc (THE na::nat. Fin na = n)"
      by (simp)
    thus ?thesis
      by (simp add: tsTakeL_def f1, simp add: tsTake_def2)
qed

lemma tstakeL_below [simp]: "tsTakeL\<cdot>(n)\<cdot>ts \<sqsubseteq> tsTakeL\<cdot>(lnsuc\<cdot>n)\<cdot>ts"
  using less_lnsuc lnle_def monofun_cfun_arg monofun_cfun_fun by blast
    
lemma tstakeL_inf_below [simp]: "tsTakeL\<cdot>(Fin i)\<cdot>ts \<sqsubseteq> tsTakeL\<cdot>(\<infinity>)\<cdot>ts"
  by (simp add: monofun_cfun)
    
lemma tstakeL_chain [simp]: "chain (\<lambda>i. tsTakeL\<cdot>(Fin i)\<cdot>ts)"
  by (metis (no_types, lifting) Fin_Suc po_class.chain_def tstakeL_below)
    
lemma tstake_noteq: "(tsTakeL\<cdot>(Fin i)\<cdot>ts) \<noteq> ts \<Longrightarrow> (tsTakeL\<cdot>(Fin i)\<cdot>ts) \<noteq> (tsTakeL\<cdot>(Fin (Suc i))\<cdot>ts)"
  apply (induction i arbitrary: ts)
   apply(simp add: tsTakeL_def)
    using tstake_bot apply auto[1]
    apply (simp add: tsTakeL_def)
    by (simp add: tstake_noteq)
      
lemma tstakeL_drop [simp]: "tsTakeL\<cdot>(Fin i)\<cdot>ts \<bullet> (tsDrop i\<cdot>ts) = ts"
  by (simp add: tsTakeL_def)
    
lemma tstakeL_prefix [simp]: "tsTakeL\<cdot>n\<cdot>ts \<sqsubseteq> ts"
proof (cases "n \<noteq> \<infinity>")
  case True
    have f1: "n < \<infinity>" 
      by (simp add: True less_le)
    obtain j where f2: "n = Fin j"
    by (metis f1 infI neq_iff)
  then show ?thesis
    by (metis ts_tsconc_prefix tstakeL_drop)
next
  case False
  then show ?thesis
    by (simp add: tsTakeL_def)
qed
  
lemma tstakeL_len [simp]: "#\<surd> (tsTakeL\<cdot>n\<cdot>ts) = min (#\<surd> ts) (n)"
proof (cases "n \<noteq> \<infinity>")
  case True
  have f1: "n < \<infinity>" 
    by (simp add: True less_le)
  obtain j where f2: "n = Fin j"
    by (metis f1 infI neq_iff)
  then show ?thesis
    by (simp add: tsTakeL_def)
next
  case False
  then show ?thesis
    by (simp add: tsTakeL_def)
qed
  
lemma tstakeL_fin: assumes "n = #\<surd>ts" 
shows "(tsTakeL\<cdot>n\<cdot>ts) = ts"
  by (simp add: assms tstake_below_eq)

lemma tstakeL_fin2: assumes "(tsTakeL\<cdot>n\<cdot>ts) = ts"  
  shows "(tsTakeL\<cdot>(lnsuc\<cdot>n)\<cdot>ts) = ts"
proof (cases "n \<noteq> \<infinity>")
  case True
  then show ?thesis
    by (metis tstakeL_len assms dual_order.trans less_lnsuc min_def tstakeL_prefix tstake_below_eq)
next
  case False
  then show ?thesis
    by (simp add: tsTakeL_def)
qed
  
lemma tstakeL_fin3: assumes "(tsTakeL\<cdot>i\<cdot>ts) = ts"  and "i\<le>j"
  shows "(tsTakeL\<cdot>(lnsuc\<cdot>j)\<cdot>ts) = ts"
proof (cases "j \<noteq> \<infinity>")
  case True
  thus ?thesis
    by (metis assms(1) assms(2) dual_order.trans less_lnsuc min_def tstakeL_len tstakeL_prefix 
              tstake_below_eq)
next
  case False
  thus ?thesis
    by (simp add: False tsTakeL_def)
qed
  
lemma tstakeL_inf [simp]: "(tsTakeL\<cdot>\<infinity>\<cdot>ts) = ts"
  by (simp add: tstake_below_eq)
  
lemma tsTakeL_maxinchain: assumes "Fin n = #\<surd>ts"
  shows "max_in_chain n (\<lambda>i. tsTakeL\<cdot>(Fin i)\<cdot>ts)"
  by (metis (no_types, lifting) assms less2nat max_in_chainI min_def 
            tstakeL_len tstakeL_prefix tstake_below_eq)
          

lemma assumes "x \<sqsubseteq> y" and "#\<surd> x = #\<surd> y"
  shows " x = y"
  by (simp add: assms(1) assms(2) tstake_below_eq)
    
subsection \<open>tsTake\<close>
  
lemma tsTake_more_ticks_eq: assumes "#\<surd> (ts:: 'a tstream) = Fin n" and "n < (m::nat)"
  shows "ts \<down> m = ts"
  by (metis assms(1) assms(2) less2nat_lemma min.strict_order_iff not_less tsTake_prefix 
      tstake_below_eq tstake_len)
    
(*
lemma tstake_pref: assumes "ts1 \<sqsubseteq> ts2" and "#\<surd> ts1 \<ge> Fin n"
  shows "ts1 \<down> n = ts2 \<down> n"
  using assms(1) assms(2) tstake_less_below by blast
*)



subsection \<open>delayFun\<close>    
    
lemma delayfun_fix_tsInftick_below: assumes "delayFun\<cdot>z = z" 
 shows "tsInfTick \<sqsubseteq> z"
proof -
  have f1: "z = (Abs_tstream (\<up>\<surd>)) \<bullet> z"
    by (metis assms delayFun.rep_eq)
  have f2: "\<And> n. tsNth n\<cdot>z = (Abs_tstream (\<up>\<surd>))"
  proof -
    fix n :: nat
    have "z = tsInfTick"
      by (metis (no_types) Rep_Abs f1 s2sinftimes tick_msg tsInfTick_def tsconc_insert 
                           tsconc_rep_eq)
    then show "tsNth n\<cdot>z = Abs_tstream (\<up>\<surd>)"
      by (meson tsInfTick_tsNth)
  qed
  have "z = tsInfTick"
    apply (rule ts_tsnth_eq)
    by (simp add: f2 tsInfTick_tsNth)    
  thus ?thesis
    by simp
qed
      
lemma "fix\<cdot>delayFun = tsInfTick"
  by (simp add: delayfun_fix_tsInftick_below fix_eqI)
    
end