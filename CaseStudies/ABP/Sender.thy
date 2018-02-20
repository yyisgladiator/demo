(*  Title:        Sender.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Sender Component of the ABP on Timed Streams
*)

chapter {* Sender of the Alternating Bit Protocol *}
                                                            
theory Sender
imports "../../TStream" Miscellaneous


begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition *}
(* ----------------------------------------------------------------------- *)

text {* input: msg from the user, acks from the receiver, ack buffer for the expected ack 
        output: msg and expected ack for the receiver *}
fixrec tsSnd_h :: "'a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> ('a \<times> bool) tstream" where
  (* bottom case *)
"tsSnd_h\<cdot>\<bottom>\<cdot>acks\<cdot>ack = \<bottom>" |
"tsSnd_h\<cdot>msg\<cdot>\<bottom>\<cdot>ack = \<bottom>" |

  (* if an input and ack from the receiver *)
"msg \<noteq> \<bottom> \<Longrightarrow> acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack = 
  (* ack for the current msg \<Longrightarrow> send next msg *)
  (if (a = ack) then tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack))))
  (* wrong ack for the current msg \<Longrightarrow> send msg again *)
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if an input and ack is a tick \<Longrightarrow> send msg again plus a tick
     if transmission starts with tick \<Longrightarrow> #\<surd>acks = \<infinity> *)
"msg \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack 
  = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(delayFun\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if input is a tick \<Longrightarrow> send tick *)
"tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack
   = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack)" |

"acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack
  = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>(tsMLscons\<cdot>(up\<cdot>a)\<cdot>acks)\<cdot>ack)"

definition tsSnd :: "'a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream" where
"tsSnd \<equiv> \<Lambda> msg acks. delay (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr True))"

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

lemma tssnd_insert: "tsSnd\<cdot>msg\<cdot>acks = delay (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr True))"
  by (simp add: tsSnd_def)

lemma tssnd_h_strict [simp]:
"tsSnd_h\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>ack = \<bottom>"
"tsSnd_h\<cdot>\<bottom>\<cdot>acks\<cdot>ack = \<bottom>"
"tsSnd_h\<cdot>msg\<cdot>\<bottom>\<cdot>ack = \<bottom>"
  by (fixrec_simp)+

lemma tssnd_h_delayfun_nack:
  "msg \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>acks)\<cdot>(Discr ack) 
  = tsMLscons\<cdot>(updis (m, ack))\<cdot>(delayFun\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>acks\<cdot>(Discr ack)))"
  by (simp add: delayfun_tslscons tsmlscons_lscons)

lemma tssnd_h_delayfun_bot:
  "msg \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>\<bottom>)\<cdot>(Discr ack) 
     = tsMLscons\<cdot>(updis (m, ack))\<cdot>(delayFun\<cdot>\<bottom>)"
  by (simp add: tssnd_h_delayfun_nack)

lemma tssnd_h_mlscons_ack: "msg \<noteq> \<bottom> \<Longrightarrow> acks \<noteq> \<bottom> \<Longrightarrow>
   tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr a) 
     = tsMLscons\<cdot>(updis (m, a))\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>a)))"
  by (simp add: tsmlscons_lscons)

lemma tssnd_h_mlscons_nack: "msg \<noteq> \<bottom> \<Longrightarrow> acks \<noteq> \<bottom> \<Longrightarrow> a \<noteq> ack \<Longrightarrow>
   tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr ack) 
     = tsMLscons\<cdot>(updis (m, ack))\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>acks\<cdot>(Discr ack))"
  by (simp add: tsmlscons_lscons)

lemma tssnd_h_delayfun:
  "tsSnd_h\<cdot>(delayFun\<cdot>msg)\<cdot>(delayFun\<cdot>acks)\<cdot>ack = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack)"
  by (simp add: delayfun_tslscons)
    
lemma tssnd_h_delayfun_msg:
  "acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(delayFun\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>acks)\<cdot>ack 
                      = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>acks)\<cdot>ack)"
  by (simp add: delayfun_tslscons tsmlscons_lscons)

lemma tssnd_h_nbot2 [simp]: "msg \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>msg\<cdot>(delayFun\<cdot>acks)\<cdot>(Discr ack) \<noteq> \<bottom>"
  apply (induction msg arbitrary: acks ack)
  apply (simp_all)
  apply (simp add: delayfun_tslscons)
  by (simp add: tssnd_h_delayfun_nack)

lemma tssnd_h_nbot [simp]: "msg \<noteq> \<bottom> \<Longrightarrow> acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack) \<noteq> \<bottom>"
  apply (induction acks arbitrary: msg ack)
  apply (simp_all)
  apply (rule_tac ts=msg in tscases, simp_all)
  apply (simp add: delayfun_tslscons tsmlscons_lscons)
  apply (case_tac "t=ack", simp_all)
  apply (metis tsmlscons_bot2 tsmlscons_nbot tssnd_h_mlscons_ack up_defined)
  by (metis tsmlscons_bot2 tsmlscons_nbot tssnd_h_mlscons_nack up_defined)

(* tstickcount lemma for sender *)
lemma tssnd_h_tstickcount_hhh:"min (#\<surd> msg) (#\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>(updis a &&\<surd> acks)\<cdot>(Discr ack) 
    \<Longrightarrow> min (lnsuc\<cdot>(#\<surd> msg)) (#\<surd> acks) \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>msg\<cdot>(updis a &&\<surd> acks)\<cdot>(Discr ack))"
  apply(case_tac "min (#\<surd> msg) (#\<surd> acks) = (#\<surd> acks)",simp)
  apply (metis (no_types, lifting) leD le_less_trans less_lnsuc lnsuc_lnle_emb min_le_iff_disj 
    not_le_imp_less)
  apply (simp add: min_def min.coboundedI1)
  proof -
    assume a1: "(if #\<surd> msg \<le> #\<surd> acks then #\<surd> msg else #\<surd> acks) \<noteq> #\<surd> acks"
    assume "(if #\<surd> msg \<le> #\<surd> acks then #\<surd> msg else #\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>(updis a &&\<surd> acks)\<cdot> (Discr ack)"
    then have "#\<surd> msg \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>(updis a &&\<surd> acks)\<cdot> (Discr ack)"
    using a1 by presburger
    then show "(lnsuc\<cdot>(#\<surd> msg) \<le> #\<surd> acks \<longrightarrow> #\<surd> msg \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>(updis a &&\<surd> acks)\<cdot> (Discr ack)) \<and> (\<not> lnsuc\<cdot>(#\<surd> msg) \<le> #\<surd> acks \<longrightarrow> #\<surd> acks \<le> lnsuc\<cdot> (#\<surd> tsSnd_h\<cdot>msg\<cdot>(updis a &&\<surd> acks)\<cdot> (Discr ack)))"
      using a1 by (meson antisym lnle2le not_le_imp_less)
  qed
  
lemma tssnd_h_tstickcount_hh:"(\<And>acks ack. min (#\<surd> msg) (#\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)) 
    \<Longrightarrow> msg \<noteq> \<bottom> \<Longrightarrow> min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> msg)\<cdot>as\<cdot>(Discr ack)"
proof(induction as arbitrary:msg ack)
  case adm
  then show ?case 
  apply(rule adm_all)+
  apply(rule adm_imp,simp)
  apply(rule adm_imp,simp)
  apply(rule adm_all)
  apply(rule admI)
  by (simp add: contlub_cfun_arg contlub_cfun_fun lub_min_mono)
next
  case bottom
  then show ?case 
  by simp
next
  case (delayfun as)
  then show ?case
  apply (simp add: tssnd_h_delayfun_nack tstickcount_delayfun tstickcount_mlscons min_le_iff_disj)
  using less_lnsuc trans_lnle by blast
next
  case (mlscons as t)
  then show ?case
  apply (simp add: tstickcount_mlscons tssnd_h_mlscons_ack tssnd_h_mlscons_nack)
  proof -
    assume a1: "as \<noteq> \<bottom>"
    assume a2: "msg \<noteq> \<bottom>"
    assume a3: "\<And>acks ack. min (#\<surd> msg) (#\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
    assume "\<And>msg ack. \<lbrakk>\<And>acks ack. min (#\<surd> msg) (#\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot> (Discr ack); msg \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot> (updis ta &&\<surd> msg)\<cdot> as\<cdot> (Discr ack)"
    then have f4: "\<And>b. min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> msg)\<cdot>as\<cdot> (Discr b)"
      using a3 a2 by blast
    then have "\<exists>b. b \<and> min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> msg)\<cdot> (updis b &&\<surd> as)\<cdot> (Discr ack)"
      using a3 a2 a1 by (metis (no_types) tssnd_h_mlscons_ack tssnd_h_mlscons_nack tstickcount_mlscons)
    moreover
    { assume "\<not> t"
      then have "\<exists>b. min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> msg)\<cdot> (updis b &&\<surd> as)\<cdot> (Discr ack) \<and> \<not> t \<and> \<not> b"
        using f4 a3 a2 a1 by (metis (no_types) tssnd_h_mlscons_ack tssnd_h_mlscons_nack tstickcount_mlscons)
      then have "min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> msg)\<cdot> (updis t &&\<surd> as)\<cdot> (Discr ack)"
        by force }
    ultimately show "min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> msg)\<cdot> (updis t &&\<surd> as)\<cdot> (Discr ack)"
      by fastforce
  qed
qed

text{* Count of ticks in sender output is greater than the minimum of ticks in msg and acks. *}  
lemma tssnd_h_tstickcount:
  "min (#\<surd>msg) (#\<surd>acks) \<le> #\<surd>tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
proof(induction msg arbitrary: acks ack)
  case adm
  then show ?case
  apply(rule adm_all)+
  apply(rule admI)
  by (simp add: contlub_cfun_arg contlub_cfun_fun lub_min_mono2)
next
  case bottom
  then show ?case by simp
next
  case (delayfun msg)
  then show ?case 
  apply(rule_tac ts=acks in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun)
  apply(simp add: delayFun_def)
  apply (simp add: min_le_iff_disj)
  apply(case_tac "as=\<bottom>",simp_all)
  apply(simp add:tssnd_h_delayfun_msg tstickcount_mlscons)
  apply(simp add: delayFun_def)
  by (metis (no_types, lifting) tssnd_h_tstickcount_hhh tstickcount_mlscons)
next
  case (mlscons msg t)
  then show ?case
    apply(rule_tac ts=acks in tscases,simp_all)
    apply(simp add: tssnd_h_delayfun_nack tstickcount_mlscons)
    apply(simp add: delayFun_def)
    apply (metis (no_types, lifting) tssnd_h_delayfun_nack tssnd_h_tstickcount_hh tstickcount_delayfun tstickcount_mlscons)
    apply(case_tac "as=\<bottom>",simp)
    apply(case_tac "a=ack",simp_all)
    apply(simp add: tssnd_h_mlscons_ack tstickcount_mlscons)
    apply(simp add: tssnd_h_mlscons_nack tstickcount_mlscons)
    by(simp add: tssnd_h_tstickcount_hh)
qed

lemma tssnd_tstickcount:
  "min (#\<surd>msg) (#\<surd>acks) < \<infinity> \<Longrightarrow> min (#\<surd>msg) (#\<surd>acks) < #\<surd>tsSnd\<cdot>msg\<cdot>acks"
  by (metis (no_types, lifting) leI le_less_trans less_lnsuc ln_less tssnd_h_tstickcount 
      tssnd_insert tstickcount_delayfun)

lemma tssnd_h_inftick_inftick: "tsSnd_h\<cdot>tsInfTick\<cdot>tsInfTick\<cdot>ack = tsInfTick" 
  by (metis (no_types, lifting) Rep_Abs delayfun_insert s2sinftimes sinftimes_unfold tick_msg 
      tsInfTick.rep_eq tsInfTick_def tsconc_insert tsconc_rep_eq tssnd_h_delayfun)

(* ----------------------------------------------------------------------- *)
section {* additional properties *}
(* ----------------------------------------------------------------------- *)

text {* lemmata for sender, see BS01, page 103 
   fds = stream of transmitted messages
   fb = corresponding stream of bits
   fas = stream of received acknowledgments
   i = input stream
   as = acks stream
   ds = output stream
*}

(* ToDo: additional properties lemmata for sender *)

text {* fds \<sqsubseteq> i where fds = map(\<alpha>.ds, \<Pi>1) 
        fds is a prefix of i *}
lemma tssnd_prefix_inp_h4:"(\<And>tb ack as. sprojfst\<cdot>(srcdups\<cdot>(\<up>(tb, ack) \<bullet> 
          tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack))))) \<sqsubseteq>\<up>tb \<bullet> tsAbs\<cdot>i) \<Longrightarrow>\<up>ta \<bullet> 
          sprojfst\<cdot>(srcdups\<cdot>(\<up>(tb, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) \<sqsubseteq> \<up>ta \<bullet> \<up>tb \<bullet> tsAbs\<cdot>i"
  proof(induction as arbitrary: ta tb ack i)
    case adm
    then show ?case
    by(simp)  
  next
    case bottom
    then show ?case
    by(simp add: monofun_cfun_arg)  
  next
    case (delayfun as)
    then show ?case
      apply(rule_tac ts = i in tscases, simp_all)
      apply(simp add: tssnd_h_delayfun)
      apply (metis tsabs_delayfun tssnd_h_delayfun)
      apply (case_tac "as = \<bottom>", simp_all)
      apply(simp add: tssnd_h_delayfun_nack lscons_conv tsabs_mlscons)
    proof -
      fix a :: 'a and i :: "'a tstream"
      assume a1: "\<And>tb ack as. sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, ack) \<bullet> 
               tsAbs\<cdot> (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot>i)\<cdot> as\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
      assume a2: "i \<noteq> \<bottom>"
      have "ack = ack"
        by auto
      then have f0:"\<And> ack. sprojfst\<cdot> (srcdups\<cdot> (\<up>(a,  ack) \<bullet> 
     tsAbs\<cdot> (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> i)\<cdot> (delayFun\<cdot>as)\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        using a1 by auto
      then have f3: "sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, \<not> ack) \<bullet> 
         tsAbs\<cdot> (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> i)\<cdot> (delayFun\<cdot>as)\<cdot> (Discr ack)))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        by (insert f0 [of "\<not>ack"], auto)
      have "tsAbs\<cdot> (tsSnd_h\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>i)\<cdot> (delayFun\<cdot>as)\<cdot> (Discr ack)) = updis (a, ack) && 
          tsAbs\<cdot> (tsSnd_h\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>i)\<cdot>as\<cdot> (Discr ack))"
        by (simp add: a2 tsabs_mlscons tssnd_h_delayfun_nack)
      then have "srcdups\<cdot> (\<up>(a, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> i)\<cdot> (delayFun\<cdot>as)\<cdot> 
                                   (Discr ack))) = \<up>(a, \<not> ack) \<bullet> srcdups\<cdot> (\<up>(a, ack) \<bullet> 
                                  tsAbs\<cdot> (tsSnd_h\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>i)\<cdot> as\<cdot> (Discr ack)))"
        by (simp add: lscons_conv)
      then have "\<up>a \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, ack) \<bullet> tsAbs\<cdot> 
                          (tsSnd_h\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>i)\<cdot>as\<cdot> (Discr ack)))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        using f3 by simp
      then show "\<up>ta \<bullet> \<up>tb \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, ack) \<bullet> 
              tsAbs\<cdot> (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot>i)\<cdot> as\<cdot> (Discr ack)))) \<sqsubseteq> \<up>ta \<bullet> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        by (meson less_all_sconsD monofun_cfun_arg)
    qed
  next
    case (mlscons as t)
    then show ?case
    apply(rule_tac ts = i in tscases, simp_all)
    apply(simp add: tssnd_h_delayfun_msg)defer
    apply(case_tac "as=\<bottom>", simp_all)
    apply(case_tac "t= ack", simp_all)
    apply(simp add: tssnd_h_mlscons_ack lscons_conv tsabs_mlscons)defer
    apply(simp add: tssnd_h_mlscons_nack lscons_conv tsabs_mlscons)
    proof -
      fix a :: 'a and i :: "'a tstream" and as :: "bool tstream"
      assume a1: "\<And>tb ack as. sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, ack) \<bullet> 
                tsAbs\<cdot> (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot>i)\<cdot> as\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
      assume a2: "as \<noteq> \<bottom>"
      assume a3: "i \<noteq> \<bottom>"
      have "ack = ack"
        by auto
      then have f0: "\<And>ack as. sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb,  ack) \<bullet> 
                tsAbs\<cdot> (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> i)\<cdot> as\<cdot> (Discr (\<not>ack))))) \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        using a1 by blast
      then have "sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> i)\<cdot> 
                                     (tsMLscons\<cdot>(updis ack)\<cdot>as)\<cdot>(Discr ack)))) \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        by (insert f0 [of "\<not>ack"], auto)
      then have "\<up>tb \<bullet> sprojfst\<cdot> (srcdups\<cdot> ( \<up>(a,  ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack))))) 
                 \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        by (simp add: a2 a3 lscons_conv tsabs_mlscons tssnd_h_mlscons_ack)
      then show "\<up>ta \<bullet> \<up>tb \<bullet> sprojfst\<cdot>(srcdups\<cdot>(\<up>(a, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack))))) 
                    \<sqsubseteq> \<up>ta \<bullet> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        using monofun_cfun_arg by blast
    next
      fix a :: 'a and i :: "'a tstream"
      assume a1: "\<And>tb ack as. sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, ack) \<bullet> tsAbs\<cdot> 
                      (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot>i)\<cdot> as\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
      assume a2: "i \<noteq> \<bottom>"
      have "ack = ack"
        by auto
      then have f0:"\<And>ack. sprojfst\<cdot> (srcdups\<cdot> (\<up>(a,  ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> i)\<cdot> 
                        (delayFun\<cdot>as)\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        using a1 by blast
      then have "sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> i)\<cdot> 
                 (delayFun\<cdot>as)\<cdot> (Discr ack)))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        by (insert f0 [of "\<not>ack"], auto) 
      then have "\<up>a \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>i)\<cdot>as\<cdot> 
                   (Discr ack)))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        using a2 by (simp add: lscons_conv tsabs_mlscons tssnd_h_delayfun_nack)
      then show "\<up>ta \<bullet> \<up>tb \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot> (tsMLscons\<cdot>(updis a)\<cdot>i)\<cdot> 
                as\<cdot> (Discr ack)))) \<sqsubseteq> \<up>ta \<bullet> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>i"
        by (meson less_all_sconsD monofun_cfun_arg)
    next
      fix i :: "'a tstream"
      assume a1: "\<And>tb ack as. sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>(delayFun\<cdot>i)\<cdot>as\<cdot> 
                    (Discr (\<not> ack))))) \<sqsubseteq> \<up>tb \<bullet> tsAbs\<cdot>i"
      have "ack = ack"
        by auto
      then have f0: "\<And>ack . sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>(delayFun\<cdot>i)\<cdot>(delayFun\<cdot> 
                    (tsMLscons\<cdot>(updis t)\<cdot> as))\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>tb \<bullet> tsAbs\<cdot>i"
        using a1 by auto
      then have "sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>(delayFun\<cdot>i)\<cdot> 
                        (delayFun\<cdot> (tsMLscons\<cdot>(updis t)\<cdot> as))\<cdot> (Discr ack)))) \<sqsubseteq> \<up>tb \<bullet> tsAbs\<cdot>i"
        by (insert f0 [of "\<not>ack"], auto)
      then show "\<up>ta \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>i\<cdot> (tsMLscons\<cdot>(updis t)\<cdot>as)\<cdot> 
                   (Discr ack)))) \<sqsubseteq> \<up>ta \<bullet> \<up>tb \<bullet> tsAbs\<cdot>i"
        by (simp add: monofun_cfun_arg tssnd_h_delayfun)
    qed
  qed

lemma tssnd_prefix_inp_h3:"(\<And>ta ack as. sprojfst\<cdot>(srcdups\<cdot>(\<up>(ta, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>
           (Discr (\<not> ack))))) \<sqsubseteq> \<up>ta \<bullet> tsAbs\<cdot>i) \<Longrightarrow> i \<noteq> \<bottom> \<Longrightarrow> \<up>ta \<bullet> sprojfst\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack)
            \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>i)\<cdot>as\<cdot>(Discr (\<not> ack))))) \<sqsubseteq> \<up>ta \<bullet> \<up>t \<bullet> tsAbs\<cdot>i"
  apply(induction as arbitrary: ta t ack i,simp_all)
  apply(simp add: monofun_cfun_arg)
  apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  apply(case_tac "t=ack")
  apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv)
  by(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv tssnd_prefix_inp_h4)  
    
lemma tssnd_prefix_inp_h2:"sprojfst\<cdot>(srcdups\<cdot>(updis (ta, ack) && tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack)))))
                         \<sqsubseteq> updis ta && tsAbs\<cdot>i"
  proof(induction i arbitrary: ta ack as)
    case adm
    then show ?case 
    by simp
  next
    case bottom
    then show ?case
    by(simp add: lscons_conv)
  next
    case (delayfun iss)
    then show ?case
    apply(rule_tac ts = as in tscases, simp_all)
    apply(simp add: lscons_conv)    
    apply(simp add: tssnd_h_delayfun)
    apply(case_tac "as=\<bottom>")    
    apply(simp add: lscons_conv)    
    by(simp add: tssnd_h_delayfun_msg)
  next
    case (mlscons iss t)
    then show ?case
    apply(rule_tac ts=as in tscases, simp_all)
    apply(simp add: lscons_conv)  
    apply(simp add: tssnd_h_delayfun_nack lscons_conv tsabs_mlscons tssnd_prefix_inp_h3)
    apply(case_tac "as=\<bottom>",simp)
    apply(simp add:lscons_conv)
    apply(case_tac "a=ack")
    apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv tssnd_prefix_inp_h3) 
    apply(simp add: tssnd_h_mlscons_ack lscons_conv tsabs_mlscons)
    proof -
      fix a :: bool and as :: "bool tstream"
      assume a1: "\<And>ta ack as. sprojfst\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>iss\<cdot>as\<cdot> 
                    (Discr (\<not> ack))))) \<sqsubseteq> \<up>ta \<bullet> tsAbs\<cdot>iss"
      have "ack = ack"
        by auto
      then have f0: "\<And>ack . sprojfst\<cdot> (srcdups\<cdot> (\<up>(t, ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>iss\<cdot>as\<cdot> (Discr (\<not> ack))))) 
                   \<sqsubseteq> \<up>t \<bullet> tsAbs\<cdot>iss"
        using a1 by auto    
      then have "sprojfst\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>iss\<cdot>as\<cdot> (Discr ack)))) 
                \<sqsubseteq> \<up>t \<bullet> tsAbs\<cdot>iss"
        by (insert f0 [of "\<not>ack"], auto)
      then show "\<up>ta \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>iss\<cdot>as\<cdot>(Discr ack)))) 
              \<sqsubseteq> \<up>ta \<bullet> \<up>t \<bullet> tsAbs\<cdot>iss"
        using monofun_cfun_arg by blast
      qed
  qed
    
lemma tssnd_prefix_inp_h1: "i \<noteq> \<bottom> \<Longrightarrow>
    sprojfst\<cdot>
    (srcdups\<cdot>( \<up>(t, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>i)\<cdot>as\<cdot>(Discr ack)))) \<sqsubseteq>
    \<up>t \<bullet> tsAbs\<cdot>i"
  apply(induction as arbitrary: t ack i, simp_all)
  apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  apply(case_tac "t\<noteq>ack")
  apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv)
  apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv)
  by (metis lscons_conv tssnd_prefix_inp_h2)

lemma tssnd_prefix_inp: "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) \<sqsubseteq> tsAbs\<cdot>i"
  apply(simp add: tsremdups_tsabs tsprojfst_tsabs)
  proof(induction as arbitrary: i ack,simp_all)
    fix i:: "'a tstream" and as:: "bool tstream" and ack:: "bool discr"
    case (delayfun as)
  then show ?case
    apply(rule_tac ts = i in tscases, simp_all)
    apply(simp add: tssnd_h_delayfun)
    apply(case_tac "as=\<bottom>")    
    apply(simp add: lscons_conv)    
    by(simp add: tssnd_h_delayfun_nack lscons_conv tsabs_mlscons tssnd_prefix_inp_h1)
  next
    case (mlscons as t)
    then show ?case
    proof(induction i arbitrary: t as ack)
    case adm
      then show ?case by simp
    next
      case bottom
      then show ?case by simp
    next 
      case (delayfun i)
      then show ?case
      by(simp add: tssnd_h_delayfun_msg)
    next
      case (mlscons i ta)
      then show ?case
      apply(case_tac "t\<noteq>ack")
      apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv tssnd_prefix_inp_h1)
      by(simp add: tssnd_h_mlscons_ack tsabs_mlscons tssnd_prefix_inp_h2)
    qed
  qed  
    
text {* \<alpha>.fb = fb  where fb = map(\<alpha>.ds, \<Pi>2)
        each new data element from i is assigned a bit different from the bit assigned to 
        the previous one*}
  
lemma tssnd_alt_bit_h5:"(\<And>ack t as. srcdups\<cdot>(\<up>ack \<bullet> sprojsnd\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack) \<bullet> 
      tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))) = \<up>ack \<bullet> sprojsnd\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>
 (Discr ack))))) \<Longrightarrow> i\<noteq>\<bottom> \<Longrightarrow> \<up>ack \<bullet> srcdups\<cdot>(\<up>(\<not> ack) \<bullet> sprojsnd\<cdot>(srcdups\<cdot>(\<up>(ta, ack) \<bullet> 
  tsAbs\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(updis ta)\<cdot>i)\<cdot>as\<cdot>(Discr ack))))) = \<up>ack \<bullet> \<up>(\<not> ack) \<bullet> 
    sprojsnd\<cdot>(srcdups\<cdot>(\<up>(ta, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(updis ta)\<cdot>i)\<cdot>as\<cdot>(Discr ack))))"
  apply(induction as arbitrary: ta ack i,simp_all)
  apply(subst srcdups_def [THEN fix_eq2],simp)
  apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  apply(case_tac "t\<noteq>ack")
  apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv)
  apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv)
  proof -
    fix as :: "bool tstream"  and ta :: 'a and ack :: bool and i :: "'a tstream"
    assume a1: "\<And>ack t as. srcdups\<cdot> (\<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>i\<cdot>as\<cdot>
      (Discr ack))))) = \<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))"
    then have"srcdups\<cdot> (\<up>(\<not> ack) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>i\<cdot>as\<cdot> 
       (Discr (\<not> ack)))))) = \<up>(\<not> ack) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>i\<cdot>as\<cdot> 
            (Discr (\<not> ack)))))"
      by (insert a1 [of "\<not>ack"], auto)
    then show "\<up>ack \<bullet> srcdups\<cdot> (\<up>(\<not> ack) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>
   (Discr (\<not> ack)))))) = \<up>ack \<bullet> \<up>(\<not> ack) \<bullet> sprojsnd\<cdot>(srcdups\<cdot> (\<up>(ta, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot> 
             (Discr (\<not> ack)))))"
      by simp
  qed

lemma tssnd_alt_bit_h4:
          "srcdups\<cdot>(\<up>ack \<bullet> sprojsnd\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))) 
                          = \<up>ack \<bullet> sprojsnd\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))"
  proof(induction i arbitrary: ack t as)
    case adm
    then show ?case
    by simp
  next
    case bottom
    then show ?case 
    by(subst srcdups_def [THEN fix_eq2],simp)
  next
    case (delayfun iss)
    then show ?case
      apply(rule_tac ts= as in tscases, simp_all)
      apply(subst srcdups_def [THEN fix_eq2],simp)
      apply(simp add: tssnd_h_delayfun)
      apply(case_tac "as=\<bottom>", simp_all)
      apply(subst srcdups_def [THEN fix_eq2],simp)
      by(simp add: tssnd_h_delayfun_msg)
  next
    case (mlscons iss ta)
    then show ?case
    apply(rule_tac ts= as in tscases, simp_all)
    apply(subst srcdups_def [THEN fix_eq2],simp)
    apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv tssnd_alt_bit_h5)
    apply(case_tac "as=\<bottom>", simp)
    apply(subst srcdups_def [THEN fix_eq2],simp_all)
    apply(case_tac "a\<noteq>ack", simp_all)
    apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv tssnd_alt_bit_h5)    
    apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv)
    proof -
      fix a :: bool and as :: "bool tstream"
      assume a1: "\<And>ack t as. srcdups\<cdot> (\<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>iss\<cdot>as\<cdot>
       (Discr ack))))) = \<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>iss\<cdot>as\<cdot>(Discr ack))))"
      then have"srcdups\<cdot> (\<up>(\<not> ack) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>iss\<cdot>as\<cdot> 
                               (Discr (\<not> ack)))))) =  \<up>(\<not> ack) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> 
                                tsAbs\<cdot> (tsSnd_h\<cdot>iss\<cdot>as\<cdot> (Discr (\<not> ack)))))"
        by (insert a1 [of "\<not>ack"], auto)
      then show "\<up>ack \<bullet> srcdups\<cdot> (\<up>(\<not> ack) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> tsAbs\<cdot> (tsSnd_h\<cdot>iss\<cdot>as\<cdot> 
           (Discr (\<not> ack)))))) = \<up>ack \<bullet> \<up>(\<not> ack) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> 
                           tsAbs\<cdot> (tsSnd_h\<cdot>iss\<cdot>as\<cdot> (Discr (\<not> ack)))))"
      by simp
    qed
  qed     
    
lemma tssnd_alt_bit_h3:"i \<noteq> \<bottom> \<Longrightarrow> srcdups\<cdot>
    (\<up>ack \<bullet> sprojsnd\<cdot>
            (srcdups\<cdot>
             (\<up>(ta, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(updis ta)\<cdot>i)\<cdot>as\<cdot>(Discr (\<not> ack)))))) =
    \<up>ack \<bullet> sprojsnd\<cdot>
           (srcdups\<cdot>(\<up>(ta, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(updis ta)\<cdot>i)\<cdot>as\<cdot>(Discr (\<not> ack)))))"
  apply(induction as arbitrary: ack ta i,simp_all)
  apply(subst srcdups_def [THEN fix_eq2], simp)
  apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  apply(case_tac "t=ack")
  apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv)
  by(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv tssnd_alt_bit_h4)

lemma tssnd_alt_bit_h2:"
       srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(\<up> (t, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not>ack)))))) =
       sprojsnd\<cdot>(srcdups\<cdot>(\<up> (t, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not>ack)))))"
  proof(induction i arbitrary: as ack t )
    case adm
    then show ?case
    by simp
  next
    case bottom
    then show ?case
    by(simp add:lscons_conv)
  next
    case (delayfun asa)
    then show ?case
    apply(rule_tac ts=as in tscases, simp_all) 
    apply(simp add: tssnd_h_delayfun)
    apply(case_tac "as=\<bottom>", simp_all)
    by(simp add: tssnd_h_delayfun_msg)
  next
    case (mlscons asa ta)
    then show ?case
    apply(rule_tac ts=as in tscases, simp_all) 
    apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
    using tssnd_alt_bit_h3 apply blast
    apply(case_tac "as=\<bottom>",simp_all)
    apply(case_tac "a=(\<not> ack)")
    apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv)
    using tssnd_alt_bit_h4 apply blast
    apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv)
    by (simp add: lscons_conv tsabs_mlscons tssnd_alt_bit_h3 tssnd_h_mlscons_nack)  
  qed

lemma tssnd_alt_bit_h1:"i\<noteq>\<bottom> \<Longrightarrow> srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(\<up> (t, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>
      (tsMLscons\<cdot>(updis t)\<cdot>i)\<cdot>as\<cdot>(Discr ack))))) = sprojsnd\<cdot>(srcdups\<cdot>(\<up> (t, ack) \<bullet> tsAbs\<cdot>(tsSnd_h\<cdot>
      (tsMLscons\<cdot>(updis t)\<cdot>i)\<cdot>as\<cdot>(Discr ack))))"
  apply(induction as arbitrary: i ack t, simp_all)
  apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv)
  apply(rename_tac ta i ack t )  
  apply(case_tac "ta\<noteq>ack")
  apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv)
  by(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv tssnd_alt_bit_h2)

lemma tssnd_alt_bit:
  "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))"
  apply(simp add: tsremdups_tsabs tsprojsnd_tsabs)
  proof(induction i arbitrary: as ack, simp_all)
    case (delayfun i)
    then show ?case
    apply(rule_tac ts=as in tscases,simp_all)
    apply(simp add: tssnd_h_delayfun)
    apply(case_tac "as=\<bottom>",simp_all)
    by(simp add: tssnd_h_delayfun_msg)  
  next
    case (mlscons i t)
    then show ?case
    apply(rule_tac ts=as in tscases,simp_all)
    apply(simp add: tssnd_h_delayfun_nack tsabs_mlscons lscons_conv tssnd_alt_bit_h1)
    apply(case_tac "as=\<bottom>",simp_all)
    apply(case_tac "a=ack")
    apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons lscons_conv tssnd_alt_bit_h2)
    by(simp add: tssnd_h_mlscons_nack tsabs_mlscons lscons_conv tssnd_alt_bit_h1)
  qed  

text {* #fds = min{#i, #fas+1} where fds = map(\<alpha>.ds, \<Pi>1), fas = \<alpha>.as 
        when an acknowledgment is received then the next data next data element will eventually
        be transmitted given that there are more data elements to transmit *}
lemma tssnd_ack2trans: 
  "tsAbs\<cdot>(tsRemDups\<cdot>as) \<sqsubseteq> tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) \<Longrightarrow> 
   #\<surd>as = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))
                  = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
  oops

text {* #i > #fas \<Longrightarrow> #ds = \<infinity> where fas = \<alpha>.as
        if a data element is never acknowledged despite repetitive transmission by the sender 
        then the sender never stops transmitting this data element *}
lemma tssnd_nack2inftrans: "#\<surd>as = \<infinity> \<Longrightarrow> 
  #(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))) = \<infinity>"
  oops
  
lemma tssnd_as_inftick_h9:"(i::'a tstream) \<noteq> \<bottom> \<Longrightarrow>
    (\<And>(ack::bool) (i::'a tstream) ta::'a.
        #(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(lnsuc\<cdot>(#(tsAbs\<cdot>i))) \<Longrightarrow>
        i \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> i)\<cdot>as\<cdot>(Discr (\<not> ack)))) \<Longrightarrow>
    as \<noteq> \<bottom> \<Longrightarrow>#(srcdups\<cdot>(\<up>(\<not> ack) \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(lnsuc\<cdot>(#(tsAbs\<cdot>i))) \<Longrightarrow> 
    #\<surd> as \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>as\<cdot>(Discr ack))"  
proof -
  assume a0:"(i::'a tstream) \<noteq> \<bottom>"
  assume a1:"(\<And>ack (i::'a tstream) ta.
        #(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(lnsuc\<cdot>(#(tsAbs\<cdot>i))) \<Longrightarrow>
        i \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> i)\<cdot>as\<cdot>(Discr (\<not> ack))))"
  assume a2:"#(srcdups\<cdot>(\<up>(\<not> ack) \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(lnsuc\<cdot>(#(tsAbs\<cdot>i)))"
  have h0:"#(srcdups\<cdot>(\<up>(\<not> ack) \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(lnsuc\<cdot>(#(tsAbs\<cdot>(i::'a tstream)))) \<Longrightarrow>i \<noteq> \<bottom> \<Longrightarrow>  #\<surd> as \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>as\<cdot>(Discr ack))"
    by (insert a1 [of "\<not> ack"], auto)
  then show ?thesis
    using a0 a2 by blast
qed
      
lemma tssnd_as_inftick_h8:" (\<And>ack (i::'a tstream) ta.
        #(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(lnsuc\<cdot>(#(tsAbs\<cdot>i))) \<Longrightarrow>
        i \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> i)\<cdot>as\<cdot>(Discr (\<not> ack)))) \<Longrightarrow>
    as \<noteq> \<bottom> \<Longrightarrow> #(srcdups\<cdot>(\<up>(\<not> ack) \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>(i::'a tstream))) \<Longrightarrow> i \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))"
proof(induction i arbitrary: ack as)
  case adm
  then show ?case 
  apply(rule adm_all)+
  apply(rule adm_imp,simp)+
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: not_less contlub_cfun_arg contlub_cfun_fun)
  apply(meson lnle_def lub_below monofun_cfun_arg not_le po_class.chain_def)
  apply(rule adm_imp,simp)
  apply(rule admI)
  by(simp add: contlub_cfun_arg contlub_cfun_fun lub_sml_eq)
next
  case bottom
  then show ?case
  by simp  
next
  case (delayfun i)
  then show ?case 
  apply(rule_tac ts=as in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun tssnd_h_delayfun_nack tstickcount_mlscons)
  apply(simp add: delayFun_def)
  apply(case_tac "as=\<bottom>", simp_all)
  apply(case_tac "i=\<bottom>",simp_all)
  apply (metis below_bottom_iff lnle2le lnle_def lnsuc_neq_0_rev lnzero_def slen_empty_eq slen_scons srcdups_nbot)
  apply(case_tac "as=\<bottom>",simp_all)
  apply(simp add: tssnd_h_delayfun_msg tstickcount_mlscons tsabs_mlscons lscons_conv)
  apply(simp add: delayFun_def)
   apply(case_tac "i=\<bottom>",simp_all)
  apply (metis below_bottom_iff lnat.con_rews lnle2le lnle_def lnzero_def slen_scons srcdups_ex)
  by (smt delayfun.prems(2) dual_order.trans less_lnsuc lscons_conv tsabs_mlscons tstickcount_mlscons)
next
  case (mlscons i t)
  then show ?case
  apply(simp add: tsabs_mlscons lscons_conv)
  using tssnd_as_inftick_h9 by blast
qed

lemma tssnd_as_inftick_h7:"#(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(lnsuc\<cdot>(#(tsAbs\<cdot>i))) \<Longrightarrow>
    i \<noteq> \<bottom> \<Longrightarrow> as \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> i)\<cdot>as\<cdot>(Discr (\<not> ack)))"
proof(induction as arbitrary: i ack ta)
  case adm
  then show ?case 
  apply(rule adm_all)+
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: not_less contlub_cfun_arg contlub_cfun_fun)
  apply(meson below_lub lnle_def monofun_cfun_arg po_class.chain_def)
  apply(rule adm_imp,simp)
  apply(rule adm_imp,simp)
  apply(rule admI)
  by(simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
next
  case bottom
  then show ?case by simp
next
  case (delayfun as)
  then show ?case 
  apply(simp add: tssnd_h_delayfun_nack tstickcount_mlscons)
  apply(simp add: delayFun_def)
  by fastforce  
next
  case (mlscons as t)
  then show ?case
  apply(case_tac "t=ack",simp_all)
  apply(simp add: tssnd_h_mlscons_nack tsabs_mlscons tstickcount_mlscons lscons_conv)
  apply(simp add: tssnd_h_mlscons_ack tsabs_mlscons tstickcount_mlscons lscons_conv)
  using tssnd_as_inftick_h8 by blast
qed
    
lemma tssnd_as_inftick_h6:"i \<noteq> \<bottom> \<Longrightarrow>
    #(srcdups\<cdot>(\<up>(\<not> ack) \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>i)) \<Longrightarrow>
    (\<And>(ack::bool) i::'a tstream.
        #(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>i)) \<Longrightarrow> i \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> #\<surd> tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack))) \<Longrightarrow>
    as \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>(i::'a tstream)\<cdot>as\<cdot>(Discr ack))"    
proof(-)
  assume a0:" i \<noteq> \<bottom> "
  assume a1:" \<And>ack i::'a tstream. #(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>i)) \<Longrightarrow> i \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> #\<surd> tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack))"
  assume a2:" #(srcdups\<cdot>(\<up>(\<not> ack) \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>i))"
  have h0:"#(srcdups\<cdot>(\<up>(\<not> ack) \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>i)) \<Longrightarrow> i \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> #\<surd> tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)"
    by (insert a1 [of "\<not>ack"], auto)
  then show ?thesis
    using a0 a2 less_lnsuc trans_lnle by blast
qed
  
lemma tssnd_as_inftick_h5:"#(srcdups\<cdot>(\<up>ack \<bullet> \<up>t \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>i)) \<Longrightarrow>
         (\<And>ack i::'a tstream. #(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>i)) \<Longrightarrow> i \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> #\<surd> tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not> ack))) \<Longrightarrow>
         as \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> #\<surd> delay (tsSnd_h\<cdot>(i::'a tstream)\<cdot>(updis t &&\<surd> as)\<cdot>(Discr (\<not> ack)))"
proof(induction i arbitrary: ack t as)
  case adm
  then show ?case
  apply(rule adm_all)+
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: not_less contlub_cfun_arg contlub_cfun_fun)
  apply(meson lnle_def lub_below monofun_cfun_arg not_le po_class.chain_def)
  apply(rule adm_imp,simp)
  apply(rule admI)
  by(simp add: contlub_cfun_arg contlub_cfun_fun lub_sml_eq)
next
  case bottom
  then show ?case
  apply simp
  by (metis Fin_02bot Fin_Suc lnat.con_rews lnzero_def neq02Suclnle not_less slen_empty_eq slen_scons srcdups_nbot)  
next
  case (delayfun i)
  then show ?case 
  apply(simp add: tssnd_h_delayfun_msg tstickcount_delayfun)
  using dual_order.trans less_lnsuc by blast
next
  case (mlscons i ta)
  then show ?case 
  apply(case_tac "t=ack",simp_all)
  apply(simp add: tssnd_h_mlscons_nack)
  apply(simp add: delayFun_def tstickcount_mlscons tsabs_mlscons lscons_conv)
  using tssnd_as_inftick_h7 apply blast
  apply(simp add: tssnd_h_mlscons_ack)
  apply(simp add: delayFun_def tstickcount_mlscons tsabs_mlscons lscons_conv)
  using tssnd_as_inftick_h6 by blast
qed 
    
lemma tssnd_as_inftick_h4:"#(srcdups\<cdot>(\<up>ack \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>i)) \<Longrightarrow>
            i \<noteq> \<bottom> \<Longrightarrow> as \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> #\<surd> tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr (\<not>ack))"
proof(induction as arbitrary: i ack)
  case adm
  then show ?case
  apply(rule adm_all)+
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: not_less contlub_cfun_arg contlub_cfun_fun)
  apply(meson below_lub lnle_def monofun_cfun_arg po_class.chain_def)
  apply(rule adm_imp,simp)
  apply(rule adm_imp,simp)
  apply(rule admI)
  by(simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
next
  case bottom
  then show ?case by simp
next
  case (delayfun as)
  then show ?case
  apply(rule_tac ts= i in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun)
  apply(simp add: delayFun_def)
  apply(rename_tac m)
  apply (case_tac "m=\<bottom>")
  apply (metis bottomI lnle2le lnle_def lnzero_def slen_empty_eq srcdups_nbot srcdupsimposs2_h2 strictI tsabs_bot)
  (*  "min (#\<surd>msg) (#\<surd>acks) \<le> #\<surd>tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)" *) 
  apply (smt below_bottom_iff lnle2le lnle_def lnsuc_neq_0_rev lnzero_def slen_empty_eq slen_scons srcdups_nbot strict_slen strict_tstickcount tsSnd_h.simps(2) tsabs_bot)
  apply(rename_tac i)
  apply(case_tac "i=\<bottom>",simp_all)
  apply(simp add: tssnd_h_delayfun_nack tstickcount_mlscons)
  apply(simp add: delayFun_def)
  by fastforce
next
  case (mlscons as t)
  then show ?case
  apply(rule_tac ts= i in tscases,simp_all)
  apply(simp add: tssnd_h_delayfun_msg tstickcount_mlscons tsabs_mlscons lscons_conv)defer
  apply(rename_tac i)
  apply(case_tac "i=\<bottom>",simp_all)
  apply(case_tac "t=ack",simp_all)
  apply(simp add: tssnd_h_mlscons_nack tstickcount_mlscons tsabs_mlscons lscons_conv)
  apply(simp add: tssnd_h_mlscons_ack tstickcount_mlscons tsabs_mlscons lscons_conv)
  apply fastforce
  apply(rename_tac i)
  using tssnd_as_inftick_h5 by blast
qed     
    
lemma tssnd_as_inftick_h3:"#(srcdups\<cdot>(\<up>True \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>i)) \<Longrightarrow>
            i \<noteq> \<bottom> \<Longrightarrow> as \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> #\<surd> tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr False)"
using tssnd_as_inftick_h4 by force
  
lemma tssnd_as_inftick_h2:" #(srcdups\<cdot>(\<up>False \<bullet> tsAbs\<cdot>as)) < lnsuc\<cdot>(#(tsAbs\<cdot>i)) \<Longrightarrow>
            i \<noteq> \<bottom> \<Longrightarrow> as \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> #\<surd> tsSnd_h\<cdot>(updis a &&\<surd> i)\<cdot>as\<cdot>(Discr True)"
proof(induction as arbitrary: i a)
  case adm
  then show ?case 
  apply(rule adm_all)
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: not_less contlub_cfun_arg contlub_cfun_fun)
  apply(meson below_lub lnle_def monofun_cfun_arg po_class.chain_def)
  apply(rule adm_imp,simp)
  apply(rule adm_imp,simp)
  apply(rule admI)
  by(simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
next
  case bottom
  then show ?case 
  by simp  
next
  case (delayfun as)
  then show ?case
  apply(simp add: tssnd_h_delayfun_nack tstickcount_mlscons)
  apply(simp add: delayFun_def)
  by fastforce
next
  case (mlscons as t)
  then show ?case 
  apply(case_tac "t= True",simp_all)
  apply(simp add: tssnd_h_mlscons_ack tstickcount_mlscons tsabs_mlscons lscons_conv)
  apply (meson dual_order.trans less_lnsuc not_le tssnd_as_inftick_h3)
  by(simp add: tssnd_h_mlscons_nack tstickcount_mlscons tsabs_mlscons lscons_conv)
qed
    
lemma tssnd_as_inftick_h:"#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>as)) < #(tsAbs\<cdot>i) \<Longrightarrow>
          as \<noteq> \<bottom> \<Longrightarrow> #\<surd> as \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>i\<cdot>(updis t &&\<surd> as)\<cdot>(Discr True))"
proof(induction i arbitrary: as t)
  case adm
  then show ?case 
  apply(rule adm_all)
  apply(rule adm_all)
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: not_less contlub_cfun_arg contlub_cfun_fun)
  apply(meson lnle_def lub_below monofun_cfun_arg not_le po_class.chain_def)
  apply(rule adm_imp,simp)
  apply(rule admI)
  by(simp add: contlub_cfun_arg contlub_cfun_fun lub_sml_eq)
next
  case bottom
  then show ?case 
  apply simp
  by (metis below_bottom_iff lnless_def lnzero_def)
next
  case (delayfun i)
  then show ?case 
  apply(simp add: tssnd_h_delayfun_msg)
  apply(simp add: delayFun_def)
  using dual_order.trans less_lnsuc by blast
next
  case (mlscons i ta)
  then show ?case 
  apply(case_tac "i=\<bottom>",simp_all)
  apply(case_tac "t=True",simp_all)
  apply(simp add: tssnd_h_mlscons_ack tstickcount_mlscons tsabs_mlscons lscons_conv)
  apply (meson less_lnsuc trans_lnle tssnd_as_inftick_h3) 
  apply(simp add: tssnd_h_mlscons_nack tstickcount_mlscons tsabs_mlscons lscons_conv)
  using less_lnsuc trans_lnle tssnd_as_inftick_h2 by blast    
qed     
    
lemma tssnd_as_inftick: "#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> lnsuc\<cdot>(#\<surd>as) \<le> #\<surd>(tsSnd\<cdot>i\<cdot>as)"
apply(simp add: tsSnd_def)
apply(simp add: delayFun_def)
apply(simp add: tsremdups_tsabs)
proof(induction as arbitrary: i)
  case adm
  then show ?case
  apply(rule adm_all)
  apply(rule adm_imp)
  apply(rule admI)
  apply(simp add: not_less contlub_cfun_arg contlub_cfun_fun)
  apply(meson below_lub lnle_def monofun_cfun_arg po_class.chain_def)
  apply(rule admI)
  by(simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
next
  case bottom
  then show ?case by simp
next
  case (delayfun as)
  then show ?case 
  apply(rule_tac ts = i in tscases,simp_all)
  apply(metis below_bottom_iff lnless_def lnzero_def)
  apply(simp add: tssnd_h_delayfun)
  apply(simp add: delayFun_def)
  apply(case_tac "as=\<bottom>",simp_all)
  apply(metis below_bottom_iff lnless_def lnzero_def)
  apply(simp add: tssnd_h_delayfun_nack tstickcount_mlscons)
  by(simp add: delayFun_def)
next
  case (mlscons as t)
  then show ?case
  apply(rule_tac ts = i in tscases,simp_all)
  apply (metis below_bottom_iff lnless_def lnzero_def)
  apply(rename_tac it) 
  apply(case_tac "as=\<bottom>",simp_all)
  apply(simp add: tssnd_h_delayfun_msg tstickcount_mlscons tsabs_mlscons lscons_conv)
  apply(simp add: delayFun_def)
  using tssnd_as_inftick_h apply blast
  apply(case_tac "as=\<bottom>",simp_all)
  apply(metis below_bottom_iff lnless_def lnzero_def)
  apply(case_tac "t=True",simp_all)    
  apply(simp add: tssnd_h_mlscons_ack)
  apply(simp add: tsabs_mlscons lscons_conv tstickcount_mlscons)
  using tssnd_as_inftick_h3 apply blast
  by(simp add: tssnd_h_mlscons_nack tstickcount_mlscons tsabs_mlscons lscons_conv tssnd_as_inftick_h2)
qed

(* ----------------------------------------------------------------------- *)
section {* tssnd_nack2inftrans *}
(* ----------------------------------------------------------------------- *)

lemma tssnd_h_tsdropwhiletick: "tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>(updis (ack1) &&\<surd> as)\<cdot>(Discr ack2)) 
      = tsAbs\<cdot>(tsSnd_h\<cdot>(tsDropWhileTick\<cdot>i)\<cdot>(updis (ack1) &&\<surd> as)\<cdot>(Discr ack2))" 
  apply (induction i arbitrary: acka as,simp_all)
  apply (metis (no_types, hide_lams) delayfun_tslscons tsDropWhileTick.simps(2) tsSnd_h.simps(2) 
        tsSnd_h.simps(6) tsabs_delayfun tsmlscons_bot2 tsmlscons_lscons)
  by (simp add: tsmlscons_lscons)
 
lemma tssnd_h_msg_inftick:"i \<noteq> \<bottom> 
          \<Longrightarrow> (tsAbs\<cdot>(tsSnd_h\<cdot>(updis t &&\<surd> i)\<cdot>tsInfTick\<cdot>(Discr ack))) = \<up>(t, ack)\<infinity>"
  by (metis (no_types, lifting) delayfun_nbot lscons_conv s2sinftimes tsabs_delayfun tsabs_mlscons
      tsinftick_unfold tssnd_h_delayfun_nack)

lemma tssnd_h_inftick_slen:"#(tsAbs\<cdot>i) \<noteq> 0 \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>tsInfTick\<cdot>(Discr ack))) = \<infinity>"  
  apply (induction i arbitrary: ack)
  apply (rule adm_imp,simp+)
  apply (metis tsabs_delayfun tsinftick_unfold tssnd_h_delayfun)
  using tssnd_h_msg_inftick by fastforce

lemma tssnd_h_tsabs: "tsAbs\<cdot>i = \<epsilon> \<Longrightarrow> tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)) = \<epsilon>"
  apply (induction i arbitrary: as ack, simp_all)
  apply (metis (no_types, lifting) bottomI srcdups_nbot strict_rev_sprojfst tsabs_delayfun 
        tsprojfst_tsabs tsremdups_tsabs tssnd_prefix_inp)
  by (simp add: tsabs_mlscons)

(* tssnd_nack2inftrans *)
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

lemma h4_2_h3_h: "tsAbs\<cdot>i \<noteq> \<epsilon> \<Longrightarrow>
           tsSnd_h\<cdot>(updis (shd (tsAbs\<cdot>i)) &&\<surd> tsRt\<cdot>(tsDropWhileTick\<cdot>i))\<cdot>(tsntimes x (Abs_tstream (\<up>\<surd>)))\<cdot>(Discr ack) =
           tsntimes x (updis (shd (tsAbs\<cdot>i), ack) &&\<surd> delay \<bottom>)"
  apply (induction x,simp_all)
  by (metis delayfun_insert mlscons_conc_delay_bottom tsDropwhileTick_tsrt_nbot tssnd_h_delayfun_nack)

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
  apply (simp add: tsdropwhile_mlscons_t tsabs_mlscons shd_updis)
  apply (meson dual_order.trans h4_2_h)
  by (simp add: tsdropwhile_mlscons_f)

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
  apply (simp add: tsdropwhile_mlscons_t)
  apply (smt dual_order.trans h4_2_h)
  apply (simp add: tsdropwhile_mlscons_f)
  by (simp add: h4_1_hh_h42)

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
  apply (simp add: tsdropwhile_mlscons_t)
  using h4_1_hh_h9_h4 apply blast 
  by(simp add: tsdropwhile_mlscons_f h4_1_hh_h9hh)

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
       apply (simp add: assms(3) h3 h4 tsdropfirstmsg_mlscons tsdropwhile_mlscons_t)
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
  apply (simp add: srcdups_step_tsabs)
  apply (fold tsdropwhile_tsabs)
  apply (case_tac "k = 0",simp_all)
  apply (simp add: lnsuc_fin [of k])
  using h4[of i as ack] empty_is_shortest h6_hh by blast

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


(* ----------------------------------------------------------------------- *)
section {* tssnd_ack2trans *}
(* ----------------------------------------------------------------------- *)
  
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
  
lemma tssnd_ack2trans_32:"(\<And>(i:: 'b tstream) as ack.
           lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
           Fin k = #(tsAbs\<cdot>i) \<Longrightarrow>
           #(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow>
           tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = stake k\<cdot>(tsAbs\<cdot>i)) \<Longrightarrow>
       lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
       Fin (Suc k) = #(tsAbs\<cdot>(i:: 'b tstream)) \<Longrightarrow>
       #(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow>
       tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = stake (Suc k)\<cdot>(tsAbs\<cdot>i)"  
proof(case_tac"#(tsAbs\<cdot>i) \<le> (lnsuc\<cdot>0)")
  assume a2:" Fin (Suc k) = #(tsAbs\<cdot>i)"
  assume a3:"#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
  assume a4:"#(tsAbs\<cdot>i) \<le> lnsuc\<cdot>0 "
  have h0:" k = 0"
    using a2 a4 lnle_Fin_0 lnsuc_lnle_emb by fastforce
  have h1:" Fin (Suc 0) = #(tsAbs\<cdot>i) \<Longrightarrow> #(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = stake (Suc 0)\<cdot>(tsAbs\<cdot>i)"
    by (smt Fin_02bot Zero_not_Suc a4 eq_slen_eq_and_less fin2stake lnle_Fin_0 lnzero_def min.strict_order_iff min_absorb2 min_lnsuc mono_slen not_le_zero_eq slen_empty_eq strict_slen tsdropfirst3_le tsprojfst_tsabs_slen tssnd_h_tsabs_nbot tssnd_prefix_inp)
  then show ?thesis
    using a2 a3 h0 by blast
next
  assume a0:"(\<And>(i::'b tstream) as ack.
           lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
           Fin k = #(tsAbs\<cdot>i) \<Longrightarrow>
           #(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) \<Longrightarrow>
           tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = stake k\<cdot>(tsAbs\<cdot>i))"
  assume a1:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack"
  assume a2:" Fin (Suc k) = #(tsAbs\<cdot>i)"
  assume a3:"#(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))"
  assume a4:"\<not>(#(tsAbs\<cdot>i) \<le> lnsuc\<cdot>0)"
  have h01: "(\<And>(i::'b tstream) ack.
           lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) = updis ack \<Longrightarrow>
           Fin k = #(tsAbs\<cdot>i) \<Longrightarrow>
           #(tsAbs\<cdot>i) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)))) \<Longrightarrow>
           tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)\<cdot>(Discr ack)))) = stake k\<cdot>(tsAbs\<cdot>i))"
          by (insert a0)
  have h0: "
           lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) = updis ack \<Longrightarrow>
           Fin k = #(tsAbs\<cdot>(tsDropFirst3\<cdot>i)) \<Longrightarrow>
           #(tsAbs\<cdot>(tsDropFirst3\<cdot>i)) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)))) \<Longrightarrow>
           tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>(tsDropFirst3\<cdot>i)\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as)\<cdot>(Discr ack)))) = stake k\<cdot>(tsAbs\<cdot>(tsDropFirst3\<cdot>i))"
           by (insert h01 [of "ack" "tsDropFirst3\<cdot>i"], blast)
  have f5: "Discr (shd (tsAbs\<cdot>(tsRemDups\<cdot>as))) = Discr ack"
    by (metis a1 lshd_updis stream.sel_rews(3) surj_scons up_defined updis_eq)
  have f7:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))) = Fin (Suc k) \<Longrightarrow> lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr ack)\<cdot>as)))) = Fin k"
    using a2 a3 by auto
  have h2:"\<not> #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<le> lnsuc\<cdot>0 \<Longrightarrow> lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr (ack))\<cdot>as))) = updis (\<not>ack)"
    apply (simp add: tsremdups_tsabs)
    apply (induction as, simp_all)  
    apply (rule adm_imp,simp_all)
    apply (rule admI)
    apply (simp add: contlub_cfun_arg lub_mono_const_leq)
    apply (simp add: tsdropwhile2_delayfun)
    apply (case_tac "t=ack")
    apply (simp add: tsdropwhile2_t)    
    apply (simp add: tsabs_mlscons lscons_conv)
    using tssnd_ack2trans_51_h3 apply blast
    by (metis lscons_conv lshd_updis srcdups_eq tsabs_mlscons tsremdups_h_tsabs tssnd_ack2trans_51_h3)
  have as1: "lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))) = updis (\<not>ack)"
    using a1 a3 a4 f5 h2 lnle2le trans_lnle by blast
  have as2: "Fin k = #(tsAbs\<cdot>(tsDropFirst3\<cdot>i))"
    by (metis Fin_02bot Fin_Suc a2 inject_Fin inject_lnsuc lnzero_def nat.distinct(1) only_empty_has_length_0 tsdropfirst3_le)
  have as3: "#(tsAbs\<cdot>(tsDropFirst3\<cdot>i)) < lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>(tsDropWhile2\<cdot>(Discr(shd (tsAbs\<cdot>(tsRemDups\<cdot>as))))\<cdot>as))))"
    by (metis Fin_Suc a1 a2 a3 as2 less_le lnsuc_lnle_emb lshd_updis stream.sel_rews(3) surj_scons tsdropwhile2_le2 up_defined)
  then show ?thesis
    using a0 a1 a2 a3 a4 as1 as2
    by (smt Fin_02bot Fin_Suc eq_slen_eq_and_less f5 fin2stake inject_Fin less2lnleD less_le lnat_po_eq_conv lnzero_def nat.distinct(1) not_le_zero_eq only_empty_has_length_0 tsDropFirst3.simps(1) tsabs_bot tsdropfirst3_le tsdropfirst3_rt tssnd_h_rt tssnd_h_tsabs_nbot tssnd_prefix_inp)
qed
  
lemma tssnd_ack2trans_31:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>  Fin k = #(tsAbs\<cdot>(i::'a tstream)) \<Longrightarrow>
    (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))) > #(tsAbs\<cdot>i) \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))) = stake k\<cdot>(tsAbs\<cdot>i)"
  apply(induction k arbitrary: i as ack,simp_all)
  apply (metis below_bottom_iff tssnd_prefix_inp)
  using tssnd_ack2trans_32 by blast
  
lemma tssnd_ack2trans_3:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>
    (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))) > #(tsAbs\<cdot>i) \<Longrightarrow> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack))))) = #(tsAbs\<cdot>i)"
proof-
  assume a0:"(lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))) > #(tsAbs\<cdot>i)"
  assume a1:"lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack"
  have h0:"\<exists>k. #(tsAbs\<cdot>i) = Fin k"
    by (metis a0 inf_ub lnat_well_h2 min_absorb2 min_def not_le)
  then show ?thesis
    by (metis a0 a1 fin2stake tssnd_ack2trans_31)
qed
  
lemma tssnd_ack2trans_2:"#\<surd>as = \<infinity> \<Longrightarrow>  lshd\<cdot>(tsAbs\<cdot>(tsRemDups\<cdot>as)) = updis ack \<Longrightarrow>#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>(Discr ack)))))
     = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
  apply(case_tac  "(lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))) > #(tsAbs\<cdot>i)",simp_all)
  apply (metis min.strict_order_iff tsprojfst_tsabs_slen tssnd_ack2trans_3)
  apply (simp add: min.strict_order_iff)
  by (metis lnat_po_eq_conv min.absorb_iff2 min_def tssnd_ack2trans_4)

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
