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

lemma min_lub:" chain Y \<Longrightarrow> (\<Squnion>i::nat. min (x::lnat) (Y i)) = min (x) (\<Squnion>i::nat. (Y i))"
  apply (case_tac "x=\<infinity>", simp_all)
  apply (case_tac "finite_chain Y")
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

lemma tssnd_h_tstickcount_adm_h1: "\<And>x. adm (\<lambda>a. \<not>(tslen\<cdot>a \<le> tslen\<cdot>x))"
  by (smt admI ch2ch_Rep_cfunR contlub_cfun_arg dual_order.trans is_ub_thelub lnle_def)

lemma tssnd_h_tstickcount_adm_h2: "\<And>x xa. adm (\<lambda>a. #\<surd>a \<le> #\<surd> tsSnd_h\<cdot>a\<cdot>x\<cdot>(Discr xa))"
  apply (rule admI)
  by (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)

lemma tssnd_h_tstickcount2_adm:
  "adm (\<lambda>a. \<forall>x. tslen\<cdot>a \<le> tslen\<cdot>x \<longrightarrow> (\<forall>xa. #\<surd>a \<le> #\<surd> tsSnd_h\<cdot>a\<cdot>x\<cdot>(Discr xa)))"
  apply (rule adm_all)
  apply (rule adm_imp)
  by (auto simp add: tssnd_h_tstickcount_adm_h1 tssnd_h_tstickcount_adm_h2)

lemma tssnd_tstickcount2: "tslen\<cdot>msg \<le> tslen\<cdot>acks \<Longrightarrow> #\<surd>msg \<le> #\<surd>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack))"
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
oops



lemma lub_mono3: "\<lbrakk>chain (X::nat\<Rightarrow>lnat); chain (Y::nat\<Rightarrow>lnat); \<And>i. min x (X i) \<le> Y i\<rbrakk>
    \<Longrightarrow> min x (\<Squnion>i. X i) \<le> (\<Squnion>i. Y i)"
  by (metis dual_order.trans is_ub_thelub lnle_def lub_mono2 min_le_iff_disj)

lemma lub_mono4: "\<lbrakk>chain (X::nat\<Rightarrow>lnat); chain (Y::nat\<Rightarrow>lnat); \<And>i. min (X i) y \<le> Y i\<rbrakk>
    \<Longrightarrow> min (\<Squnion>i. X i) y \<le> (\<Squnion>i. Y i)"
  by (metis dual_order.trans is_ub_thelub lnle_def lub_mono2 min_le_iff_disj)

lemma tssnd_h_tstickcount_h: "acks \<noteq> \<bottom> \<Longrightarrow> 
  min (#\<surd> delay as) (#\<surd> updis t &&\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>(delay as)\<cdot>(updis t &&\<surd> acks)\<cdot>(Discr ack)"
  apply (simp add: tstickcount_delayfun tstickcount_mlscons tssnd_h_delayfun_msg)
  apply (induction as arbitrary: acks t ack, simp_all)
  apply (rule adm_all)+
  apply (rule adm_imp, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono4)
  apply (smt less_lnsuc lnsuc_lnle_emb min.coboundedI1 min.coboundedI2 min_def tssnd_h_delayfun_msg 
         tstickcount_delayfun)
  apply (case_tac "ta=ack", simp_all)
  apply (simp add: tssnd_h_mlscons_ack tstickcount_mlscons)
  sorry

lemma tssnd_h_tstickcount:
  "min (#\<surd>msg) (#\<surd>acks) \<le> #\<surd>tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
  apply (induction acks arbitrary: msg ack, simp_all)
  apply (rule adm_all)+
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono3)
  apply (rule_tac ts=msg in tscases, simp_all)
  apply (metis (no_types, lifting) delayfun_insert lnsuc_lnle_emb min_def tssnd_h_delayfun 
         tstickcount_tscons)
  apply (smt le_less le_less_linear lenmin less_lnsuc lnsuc_lnle_emb min.coboundedI2 min.orderI 
         min_absorb2 min_def not_less strict_tstickcount tssnd_h_delayfun_nack tstickcount_delayfun
         tstickcount_mlscons)
  apply (rule_tac ts=msg in tscases, simp_all)
  (* unproved *)
  using tssnd_h_tstickcount_h apply blast
  by (smt le_less lenmin min.cobounded1 min.orderI min_def strict_tstickcount tssnd_h_mlscons_ack 
      tssnd_h_mlscons_nack tstickcount_mlscons)
    
end
