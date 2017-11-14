(*  Title:        Sender.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Sender Component of the ABP on Timed Streams
*)

chapter {* Sender of the Alternating Bit Protocol *}
                                                            
theory Sender
imports "../../TStream"

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

(* ToDo: tstickcount lemma for sender *)

lemma tssnd_h_tstickcount_h4: "acks \<noteq> \<bottom> \<Longrightarrow> min (lnsuc\<cdot>(#\<surd> msg)) (#\<surd> acks) = #\<surd> acks 
    \<Longrightarrow> #\<surd> acks \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>msg\<cdot>(updis t &&\<surd> acks)\<cdot>(Discr ack))"
  apply (induction acks arbitrary: t msg ack, simp_all)
  apply (rule adm_imp, simp_all)
  apply (rule adm_all)+
  apply (rule adm_imp)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun)
  apply (metis contlub_cfun_arg inf_less_eq inf_ub l42 min.absorb_iff2 ts_infinite_lub)
  apply (rule adm_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
  apply (simp add: tstickcount_delayfun tstickcount_mlscons)
  apply (rule_tac ts=msg in tscases, simp_all)
  apply (metis bottomI lnle_def lnsuc_lnle_emb lnzero_def min.cobounded1 ts_0ticks)
  apply (simp add: tssnd_h_delayfun_msg tstickcount_delayfun)
sorry

lemma tssnd_h_tstickcount_h2: "acks \<noteq> \<bottom> \<Longrightarrow> min (lnsuc\<cdot>(#\<surd> msg)) (#\<surd> acks) = #\<surd> acks 
    \<Longrightarrow> #\<surd> acks \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack))"
  apply (induction acks arbitrary: msg ack, simp_all)
  apply (rule adm_imp, simp_all)
  apply (rule adm_all)
  apply (rule adm_imp)
  apply (rule admI)
  using l42 apply force
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
  apply (simp add: tstickcount_delayfun tstickcount_mlscons)
  apply (rule_tac ts=msg in tscases, simp_all)
  apply (metis bottomI lnle_def lnsuc_lnle_emb lnzero_def min.cobounded1 ts_0ticks)
  apply (metis lnle_def lnsuc_lnle_emb lnzero_def min.absorb_iff2 minimal strict_tstickcount 
     tssnd_h_delayfun tstickcount_delayfun)
  apply (case_tac "as=\<bottom>")
  apply (metis lnsuc_lnle_emb min.cobounded1 strict_tstickcount tsmlscons_bot2 tssnd_h_strict(2))
  apply (simp add: tssnd_h_delayfun_nack)
  apply (metis (no_types, hide_lams) less_lnsuc min.absorb_iff2 min.bounded_iff strict_tstickcount 
    tsSnd_h.simps(2) tstickcount_delayfun tstickcount_mlscons)
  apply (simp add: tstickcount_mlscons)
  apply (rule_tac ts=msg in tscases, simp_all)
  apply (simp add: min.absorb_iff2)
  apply (case_tac "t\<noteq>ack")
  apply (simp add: tssnd_h_delayfun_nack tssnd_h_delayfun_msg tstickcount_delayfun tstickcount_mlscons)
  apply (rule_tac ts=as in tscases, simp_all)
  using min.absorb_iff2 apply blast 
  apply (simp add: tstickcount_delayfun tssnd_h_delayfun_msg tstickcount_mlscons)
sorry

lemma tssnd_h_tstickcount_h3: "acks \<noteq> \<bottom> \<Longrightarrow> min (lnsuc\<cdot>(#\<surd> msg)) (#\<surd> acks) = (lnsuc\<cdot>(#\<surd> msg)) 
    \<Longrightarrow> (lnsuc\<cdot>(#\<surd> msg)) \<le> lnsuc\<cdot>(#\<surd> tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack))"
sorry

text{* Minimum of ticks in delay msg and t \<bullet> acks is smaller then in sender output. *}
lemma tssnd_h_tstickcount_h1: "acks \<noteq> \<bottom> \<Longrightarrow> 
  min (#\<surd> delay msg) (#\<surd> updis t &&\<surd> acks) \<le> #\<surd> tsSnd_h\<cdot>(delay msg)\<cdot>(updis t &&\<surd> acks)\<cdot>(Discr ack)"
  apply (simp add: tstickcount_delayfun tstickcount_mlscons tssnd_h_delayfun_msg)
  apply (induction msg arbitrary: acks t ack, simp_all)
  apply (rule adm_all)+
  apply (rule adm_imp, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_min_mono2)
  apply (smt less_lnsuc lnsuc_lnle_emb min.coboundedI1 min.coboundedI2 min_def tssnd_h_delayfun_msg 
         tstickcount_delayfun)
  (*by (metis (no_types, lifting) min_def tsmlscons_nbot tssnd_h_tstickcount_h2 
    tssnd_h_tstickcount_h3 tstickcount_mlscons up_defined)*)
oops

text{* Count of ticks in sender output is greater than the minimum of ticks in msg and acks. *}
lemma tssnd_h_tstickcount:
  "min (#\<surd>msg) (#\<surd>acks) \<le> #\<surd>tsSnd_h\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
  apply (induction acks arbitrary: msg ack, simp_all)
  apply (rule adm_all)+
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_min_mono)
  apply (rule_tac ts=msg in tscases, simp_all)
  apply (metis (no_types, lifting) delayfun_insert lnsuc_lnle_emb min_def tssnd_h_delayfun 
         tstickcount_tscons)
  apply (smt le_less le_less_linear lenmin less_lnsuc lnsuc_lnle_emb min.coboundedI2 min.orderI 
         min_absorb2 min_def not_less strict_tstickcount tssnd_h_delayfun_nack tstickcount_delayfun
         tstickcount_mlscons)
  apply (rule_tac ts=msg in tscases, simp_all)
  (* using tssnd_h_tstickcount_h1 apply blast
  by (smt le_less lenmin min.cobounded1 min.orderI min_def strict_tstickcount tssnd_h_mlscons_ack 
      tssnd_h_mlscons_nack tstickcount_mlscons)*)
oops

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
lemma tssnd_ack2trans: "#\<surd>as = \<infinity> \<Longrightarrow>
   #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>ack))))
     = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
  oops

text {* #i > #fas \<Longrightarrow> #ds = \<infinity> where fas = \<alpha>.as
        if a data element is never acknowledged despite repetitive transmission by the sender 
        then the sender never stops transmitting this data element *}
lemma tssnd_nack2inftrans: "#\<surd>as = \<infinity> \<Longrightarrow> 
  #(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> #(tsAbs\<cdot>(tsSnd_h\<cdot>i\<cdot>as\<cdot>ack)) = \<infinity>"
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
  apply(simp add: tssnd_h_delayfun_msg)
  by (smt less_lnsuc trans_lnle tstickcount_delayfun)
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
    
lemma tssnd_as_inftick:"#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> lnsuc\<cdot>(#\<surd>as) \<le> #\<surd>(tsSnd\<cdot>i\<cdot>as)"
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
    
end
