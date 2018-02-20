(*  Title:        NewSender.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Sender Component of the ABP on Timed Streams
*)

chapter {* Sender of the Alternating Bit Protocol *}
                                                            
theory NewSender
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
  (if (a = ack) then tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack)))
  (* wrong ack for the current msg \<Longrightarrow> send msg again *)
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if an input and ack is a tick \<Longrightarrow> send msg again plus a tick
     if transmission starts with tick \<Longrightarrow> #\<surd> acks = \<infinity> *)
"msg \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack 
  = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(delayFun\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if input and ack is a tick \<Longrightarrow> send one tick *)
"tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack
   = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack)" |

  (* if input is a tick \<Longrightarrow> send tick and remove wrong ack *)
"acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack
  = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack)"

definition tsSnd :: "'a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream" where
"tsSnd \<equiv> \<Lambda> msg acks. delay (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr True))"

(*
text {* input: msg from the user, acks from the receiver, ack buffer for the expected ack 
        output: msg and expected ack for the receiver *}
fixrec tsSnd_h :: "'a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> nat discr \<rightarrow> ('a \<times> bool) tstream" where
  (* bottom case *)
"tsSnd_h\<cdot>\<bottom>\<cdot>acks\<cdot>ack\<cdot>cou = \<bottom>" |
"tsSnd_h\<cdot>msg\<cdot>\<bottom>\<cdot>ack\<cdot>cou = \<bottom>" |

  (* if an input and ack from the receiver *)
"msg \<noteq> \<bottom> \<Longrightarrow> acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack\<cdot>cou = 
  (* ack for the current msg \<Longrightarrow> send next msg *)
  (if (a = ack) then tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack)))\<cdot>cou
  (* wrong ack for the current msg \<Longrightarrow> send msg again *)
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack\<cdot>cou))" | 

  (* if an input and ack is a tick \<Longrightarrow> send msg again plus a tick
     if transmission starts with tick \<Longrightarrow> #\<surd> acks = \<infinity> *)
"msg \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack\<cdot>cou  = 
  (if (cou = Discr 0) then delayFun\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack\<cdot>(Discr 1))
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(delayFun\<cdot>(tsSnd_h\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack\<cdot>(Discr ((undiscr cou) - 1)))))" |

  (* if input is a tick \<Longrightarrow> send tick and remove wrong ack *)
"acks \<noteq> \<bottom> \<Longrightarrow> tsSnd_h\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack\<cdot>cou
  = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack\<cdot>cou)"

definition tsSnd :: "'a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream" where
"tsSnd \<equiv> \<Lambda> msg acks. delay (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr True)\<cdot>(Discr 1))"

lemma tssnd_insert: "tsSnd\<cdot>msg\<cdot>acks = delay (tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr True)\<cdot>(Discr 1))"
  by (simp add: tsSnd_def)

lemma tssnd_h_strict [simp]:
"tsSnd_h\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>ack\<cdot>cou = \<bottom>"
"tsSnd_h\<cdot>\<bottom>\<cdot>acks\<cdot>ack\<cdot>cou = \<bottom>"
"tsSnd_h\<cdot>msg\<cdot>\<bottom>\<cdot>ack\<cdot>cou = \<bottom>"
  by (fixrec_simp)+
*)

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
     = tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>a))"
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
                      = delayFun\<cdot>(tsSnd_h\<cdot>msg\<cdot>acks\<cdot>ack)"
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
  apply (metis tsmlscons_bot2 tssnd_h_mlscons_ack)
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
    assume "(if #\<surd> msg \<le> #\<surd> acks then #\<surd> msg else #\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>(updis a &&\<surd> acks)
            \<cdot>(Discr ack)"
    then have "#\<surd> msg \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>(updis a &&\<surd> acks)\<cdot> (Discr ack)"
    using a1 by presburger
    then show "(lnsuc\<cdot>(#\<surd> msg) \<le> #\<surd> acks \<longrightarrow> #\<surd> msg \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>(updis a &&\<surd> acks)\<cdot> (Discr ack))
      \<and> (\<not> lnsuc\<cdot>(#\<surd> msg) \<le> #\<surd> acks \<longrightarrow> #\<surd> acks \<le> lnsuc\<cdot> (#\<surd> tsSnd_h\<cdot>msg\<cdot>(updis a &&\<surd> acks)\<cdot> (Discr ack)))"
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
    assume "\<And>msg ack. \<lbrakk>\<And>acks ack. min (#\<surd> msg) (#\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot> (Discr ack); msg \<noteq> \<bottom>\<rbrakk> 
            \<Longrightarrow> min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot> (updis ta &&\<surd> msg)\<cdot> as\<cdot> (Discr ack)"
    then have f4: "\<And>b. min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> msg)\<cdot>as\<cdot> (Discr b)"
      using a3 a2 by blast
    then have "\<exists>b. b \<and> min (#\<surd> msg)(#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> msg)\<cdot>(updis b &&\<surd> as)\<cdot>(Discr ack)"
      using a3 a2 a1 by (metis (no_types) tssnd_h_mlscons_ack tssnd_h_mlscons_nack tstickcount_mlscons)
    moreover
    { assume "\<not> t"
      then have "\<exists>b. min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> msg)\<cdot>(updis b &&\<surd> as)\<cdot>(Discr ack) 
                  \<and> \<not> t \<and> \<not> b"
        using f4 a3 a2 a1 by (metis (no_types) tssnd_h_mlscons_ack tssnd_h_mlscons_nack 
          tstickcount_mlscons)
      then have "min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> msg)\<cdot>(updis t &&\<surd> as)\<cdot>(Discr ack)"
        by force }
    ultimately show "min (#\<surd> msg) (#\<surd> as) \<le> #\<surd> tsSnd_h\<cdot>(updis ta &&\<surd> msg)\<cdot>(updis t &&\<surd> as)\<cdot>(Discr ack)"
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
  by (metis (no_types, lifting) less_lnsuc lnsuc_lnle_emb min.absorb1 min_le_iff_disj)
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

end