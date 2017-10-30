(*  Title:        Sender.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Sender Component of the ABP on Timed Streams
*)

chapter {* Sender of the Alternating Bit Protocol *}
                                                            
theory Sender_DS
imports Sender

begin
default_sort countable

(* minimum and lub  *)
lemma min_lub:" chain Y \<Longrightarrow> (\<Squnion>i::nat. min (x::lnat) (Y i)) = min (x) (\<Squnion>i::nat. (Y i))"
  apply(case_tac "x=\<infinity>", simp_all)
  apply(case_tac "finite_chain Y")
proof -
  assume a1: "chain Y"
  assume a2: "finite_chain Y"
  then have "monofun (min x)"
    by (metis (mono_tags, lifting) lnle_conv min.idem min.semilattice_order_axioms monofunI
                                                   semilattice_order.mono semilattice_order.orderI)
  then show ?thesis
    using a2 a1 by (metis (no_types) finite_chain_lub)
next
  assume a0:"chain Y"
  assume a1:"\<not> finite_chain Y"
  assume a2:"x \<noteq> \<infinity>"
  have h0:"\<forall>i. \<exists>j\<ge>i. Y i \<sqsubseteq> Y j"
  by blast  
  then have"(\<Squnion>i. min x (Y i)) = x"
  proof -
    have f1: "\<And>n. min x (Y n) \<sqsubseteq> x"
      by (metis (lifting) lnle_def min.bounded_iff order_refl)
    then have f2: "\<And>n. min x (Y n) = x \<or> Y n \<sqsubseteq> x"
      by (metis (lifting) min_def)
    have f3: "\<infinity> \<notsqsubseteq> x"
      by (metis (lifting) a2 inf_less_eq lnle_def) 
    have "Lub Y = \<infinity>"
      by (meson a0 a1 unique_inf_lub)
    then obtain nn :: "(nat \<Rightarrow> lnat) \<Rightarrow> lnat \<Rightarrow> nat" where
      f4: "min x (Y (nn Y x)) = x \<or> \<infinity> \<sqsubseteq> x"
      using f2 by (metis (no_types) a0 lub_below_iff)
    have "\<forall>f n. \<exists>na. (f (na::nat)::lnat) \<notsqsubseteq> f n \<or> Lub f = f n"
      by (metis lub_chain_maxelem)
    then show ?thesis
      using f4 f3 f1 by (metis (full_types))
    qed
  then show ?thesis
    by (simp add: a0 a1 unique_inf_lub)
qed
  
lemma min_lub_rev:"chain Y \<Longrightarrow>  min (x) (\<Squnion>i::nat. (Y i)) = (\<Squnion>i::nat. min (x::lnat) (Y i)) "
  using min_lub by auto

lemma tssnd_tstickcount_adm_h1: "\<And>x. adm (\<lambda>a. \<not>(tslen\<cdot>a \<le> tslen\<cdot>x))"
  by (smt admI ch2ch_Rep_cfunR contlub_cfun_arg dual_order.trans is_ub_thelub lnle_def)

lemma tssnd_tstickcount_adm_h2: "\<And>x xa. adm (\<lambda>a. #\<surd>a \<le> #\<surd> tsSnd_h\<cdot>a\<cdot>x\<cdot>(Discr xa))"
  apply (rule admI)
  by (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)

lemma tssnd_tstickcount_adm:
  "adm (\<lambda>a. \<forall>x. tslen\<cdot>a \<le> tslen\<cdot>x \<longrightarrow> (\<forall>xa. #\<surd>a \<le> #\<surd> tsSnd_h\<cdot>a\<cdot>x\<cdot>(Discr xa)))"
  apply(rule adm_all)
  apply(rule adm_imp)
  by (auto simp add: tssnd_tstickcount_adm_h1 tssnd_tstickcount_adm_h2)

lemma tssnd_tstickcount2_adm_h1: "\<And>x xa Y. chain Y \<Longrightarrow> \<forall>i. min (#\<surd> x) (#\<surd> Y i) = #\<surd> tsSnd_h\<cdot>x\<cdot>(Y i)\<cdot>(Discr xa) 
                \<Longrightarrow> min (#\<surd> x) (\<Squnion>i. #\<surd> Y i) \<le> (\<Squnion>i. #\<surd> tsSnd_h\<cdot>x\<cdot>(Y i)\<cdot>(Discr xa))"
  apply (simp add: chain_def)
  by (metis (mono_tags, lifting) eq_imp_below lnle_def lub_eq min_lub monofun_cfun_arg po_class.chain_def)

lemma tssnd_tstickcount2_adm_h2: "chain Y \<Longrightarrow> \<forall>i. min (#\<surd> x) (#\<surd> Y i) < #\<surd> tsSnd_h\<cdot>x\<cdot>(Y i)\<cdot>(Discr xa) 
                \<Longrightarrow> min (#\<surd> x) (\<Squnion>i. #\<surd> Y i) \<le> (\<Squnion>i. #\<surd> tsSnd_h\<cdot>x\<cdot>(Y i)\<cdot>(Discr xa))"
  apply (simp add: chain_def)
  apply (case_tac "(#\<surd>x)=\<infinity>", simp_all)
  apply (case_tac "finite_chain Y")

sorry

lemma tssnd_tstickcount2_adm: "adm (\<lambda>a. \<forall>x xa. min (#\<surd> x) (#\<surd> a) \<le> #\<surd> tsSnd_h\<cdot>x\<cdot>a\<cdot>(Discr xa))"
  apply (rule adm_all)+
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun min_lub_rev)
  (* Fallunterscheidung nach Minimum?
  using ord_eq_le_trans 
  apply (simp add: min_lub_tstickcount)*)
  sorry

lemma tssnd_tstickcount2_h:
  "\<And>msg ack. min (#\<surd> msg) (#\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack) \<Longrightarrow>
   min (#\<surd> delay msg) (#\<surd> (a &&\<surd> acks)) \<le> #\<surd> tsSnd_h\<cdot>(delay msg)\<cdot>(a &&\<surd> acks)\<cdot>(Discr ack)"
  proof (induction acks arbitrary: msg ack, simp_all)
    case adm
    then show ?case sorry
  next
    case (delayfun acks)
    then show ?case sorry
  next
    case (mlscons acks t)
    then show ?case sorry
  qed

lemma tssnd_tstickcount2_msg: "min (#\<surd>msg) (#\<surd>acks) = #\<surd>msg \<Longrightarrow> #\<surd>msg \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
  apply (induction acks arbitrary: msg ack, simp_all)
  apply (rule adm_all)
  apply (rule adm_imp)
  apply (rule admI)
  apply (simp add: chain_def contlub_cfun_arg lub_mono2)
oops

lemma tssnd_tstickcount2_acks: "min (#\<surd>msg) (#\<surd>acks) = #\<surd>acks \<Longrightarrow> #\<surd>acks \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
  apply (induction acks arbitrary: msg ack, simp_all)
  apply (rule adm_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
oops

lemma tssnd_tstickcount2_v2: "min (#\<surd>msg) (#\<surd>acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
  apply (induction msg arbitrary: acks ack, simp_all)
  apply (rule adm_all)+
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
oops

lemma tssnd_tstickcount2: "min (#\<surd>msg) (#\<surd>acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
proof (induction acks arbitrary: msg ack, simp_all)
  case adm
  thus ?case
    by (simp add: tssnd_tstickcount2_adm)
next
  case (delayfun acks)
  assume ind_hyp: "\<And>msg ack. min (#\<surd> msg) (#\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
  thus ?case
    proof (cases rule: tstream_exhaust [of msg], simp_all)
      case (delayfun ts)
      thus "min (#\<surd> delay ts) (#\<surd> delay acks) \<le> #\<surd> tsSnd_h\<cdot>(delay ts)\<cdot>(delay acks)\<cdot>(Discr ack)"
        using ind_hyp
        by (metis delayfun.IH delayfun_insert lnsuc_lnle_emb min_le_iff_disj tssnd_h_delayfun 
            tstickcount_tscons)
    next
      case (mlscons t ts)
      assume ts_nbot: "ts \<noteq> \<bottom>"
      thus "min (#\<surd> updis t &&\<surd> ts) (#\<surd> delay acks)
              \<le> #\<surd> tsSnd_h\<cdot>(updis t &&\<surd> ts)\<cdot>(delay acks)\<cdot>(Discr ack)"
        by (smt
            ind_hyp delayfun.IH delayfun_insert less_lnsuc lnle_def lnsuc_lnle_emb lnzero_def
            min.coboundedI2 min_def min_le_iff_disj minimal strict_tstickcount tssnd_h_delayfun_nack
            tstickcount_mlscons tstickcount_tscons)
    qed
next
  case (mlscons acks t)
  assume ind_hyp: "\<And>msg ack. min (#\<surd> msg) (#\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
  assume acks_nbot: "acks \<noteq> \<bottom>"
  thus "min (#\<surd> msg) (#\<surd> updis t &&\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>(updis t &&\<surd> acks)\<cdot>(Discr ack)"
    proof (cases rule: tstream_exhaust [of msg], simp_all)
      case (delayfun ts)
      thus "min (#\<surd> delay ts) (#\<surd> updis t &&\<surd> acks) 
              \<le> #\<surd> tsSnd_h\<cdot>(delay ts)\<cdot>(updis t &&\<surd> acks)\<cdot>(Discr ack)"
        apply (simp add: tssnd_h_delayfun_msg tstickcount_delayfun)
        by (metis (no_types, lifting)
            mlscons.IH tssnd_tstickcount2_h tstickcount_delayfun)
    next
      case (mlscons ta ts)
      assume ts_nbot: "ts \<noteq> \<bottom>"
      thus "min (#\<surd> updis ta &&\<surd> ts) (#\<surd> updis t &&\<surd> acks) 
              \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> ts)\<cdot>(updis t &&\<surd> acks)\<cdot>(Discr ack)"
        using ind_hyp acks_nbot
        by (smt mlscons.IH tssnd_h_mlscons_ack tssnd_h_mlscons_nack tstickcount_mlscons updis_eq)
    qed
qed

lemma tssnd_tstickcount: "tslen\<cdot>msg \<le> tslen\<cdot>acks \<Longrightarrow> #\<surd>msg \<le> #\<surd>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack))"
proof (induction acks arbitrary: msg ack)
  case adm
  then show ?case sorry
next
  case bottom
  then show ?case using tslen_smaller_nbot by auto
next
  case (delayfun acks)
  assume ind: "\<And>msg ack. tslen\<cdot>msg \<le> tslen\<cdot>acks \<Longrightarrow> #\<surd> msg \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
  assume len: "tslen\<cdot>msg \<le> tslen\<cdot>(delay acks)"
  have len_delay: "tslen\<cdot>(delay acks) = lnsuc\<cdot>(tslen\<cdot>acks)"
    by (simp add: tslen_delay)
  then show ?case proof (cases rule: tstream_exhaust [of msg])
    case bottom
    then show ?thesis
      by simp
  next
    case (delayfun ts)
    then have "tsSnd_h\<cdot>(delay ts)\<cdot>(delay acks)\<cdot>(Discr ack) = delay (tsSnd_h\<cdot>ts\<cdot>acks\<cdot>(Discr ack))"
      by (simp add: delayfun_tslscons)
    then show ?thesis
      by (metis
          delayFun_dropFirst delayfun delayfun.IH delayfun_nbot len lnsuc_lnle_emb
          tsdropfirst_len tslen_delay)
  next
    case (mlscons t ts)
    then have "ts \<noteq> \<bottom>"
      by (simp add: mlscons(2))
    then have "#\<surd> tsSnd_h\<cdot>msg\<cdot>(delay acks)\<cdot>(Discr ack) = lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack))"
      sorry
    then show ?thesis sorry
  qed
next
  case (mlscons acks t)
  then show ?case sorry
qed

lemma tssnd_tsabs_slen:
  "#(Rep_tstream msg) \<le> #(Rep_tstream acks) \<Longrightarrow> #(tsAbs\<cdot>msg) \<le> #(tsAbs\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack))"
oops

lemma tssnd_inftick: "acks\<noteq>\<bottom> \<Longrightarrow> tsSnd_h\<cdot>tsInfTick\<cdot>acks\<cdot>ack = tsInfTick"
proof (induction acks arbitrary: ack)
  case adm
  then show ?case by (rule adm_imp, simp_all)
next
  case bottom
  then show ?case using bottom.prems by blast
next
  case (delayfun acks)
  have delay_inftick: "delay (Abs_tstream \<up>(\<surd>::'a event)\<infinity>) = tsInfTick"
    by (metis (no_types)
        Rep_Abs delayFun.rep_eq sinftimes_unfold tick_msg tsInfTick.abs_eq tsInfTick.rep_eq
        tsconc_insert)
  have inftick_delay: "tsInfTick = delay tsInfTick" by simp
  have delay_both: "\<forall>msg acks' ack'. acks' = \<bottom> \<or>
        tsSnd_h\<cdot>(delay (msg::'a tstream))\<cdot>(delay (acks'::bool tstream))\<cdot>ack' = delay (tsSnd_h\<cdot>msg\<cdot>acks'\<cdot>ack')"
    using tssnd_h_delayfun by blast
  assume ind: "\<And>ack. acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>tsInfTick\<cdot>acks\<cdot>ack = tsInfTick"
  have delay_nbot: "delay acks \<noteq> \<bottom>" by simp
  show ?case
    apply (subst inftick_delay)
    (*apply (case_tac "acks = \<bottom>", simp_all)*)
    apply (subst tssnd_h_delayfun)
    sorry
next
  case (mlscons acks t)
  have inftick_delay: "tsInfTick = delay tsInfTick" by simp
  have delay_msg: "\<forall>msg acks' ack1' ack2'. acks' = \<bottom> \<or>
        tsSnd_h\<cdot>(delay (msg::'a tstream))\<cdot>(tsMLscons\<cdot>(updis (ack1'::bool))\<cdot>(acks'::bool tstream))\<cdot>ack2' =
        delay (tsSnd_h\<cdot>msg\<cdot>(tsMLscons\<cdot>(updis ack1')\<cdot>acks')\<cdot>ack2')"
    by (metis delayfun_tslscons tsSnd_h.simps(6) tsmlscons_lscons)
  show ?case
    by (smt delayFun.rep_eq delay_msg inftick_delay mlscons.hyps s2sinftimes tick_msg tsconc_insert
            tsconc_rep_eq)
qed
    
end
