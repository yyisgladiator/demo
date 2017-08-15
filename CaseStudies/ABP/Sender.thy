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
fixrec tsSnd :: "'a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> ('a \<times> bool) tstream" where
  (* bottom case *)
"tsSnd\<cdot>\<bottom>\<cdot>acks\<cdot>ack = \<bottom>" |
"tsSnd\<cdot>msg\<cdot>\<bottom>\<cdot>ack = \<bottom>" |

  (* if an input and ack from the receiver *)
"msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack = 
  (* ack for the current msg \<Longrightarrow> send next msg *)
  (if (a = ack) then tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack))))
  (* wrong ack for the current msg \<Longrightarrow> send msg again *)
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if an input and ack is a tick \<Longrightarrow> send msg again plus a tick
     if transmission starts with tick \<Longrightarrow> #\<surd> acks=\<infinity> *)
"msg\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack 
  = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(delayFun\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(up\<cdot>m)\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if input is a tick \<Longrightarrow> send tick *)
"tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack
                    = delayFun\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>ack)" |

"acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack
                    = delayFun\<cdot>(tsSnd\<cdot>msg\<cdot>(tsMLscons\<cdot>(up\<cdot>a)\<cdot>acks)\<cdot>ack)"

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

lemma tssnd_strict [simp]:
"tsSnd\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>ack = \<bottom>"
"tsSnd\<cdot>\<bottom>\<cdot>acks\<cdot>ack = \<bottom>"
"tsSnd\<cdot>msg\<cdot>\<bottom>\<cdot>ack = \<bottom>"
  by (fixrec_simp)+

lemma tssnd_delayfun_nack:
  "msg\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>acks)\<cdot>(Discr ack) 
  = tsMLscons\<cdot>(updis (m, ack))\<cdot>(delayFun\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>acks\<cdot>(Discr ack)))"
  by (simp add: delayfun_tslscons tsSnd.simps(4) tsmlscons_lscons)

lemma tssnd_delayfun_bot:
  "msg\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>\<bottom>)\<cdot>(Discr ack) 
     = tsMLscons\<cdot>(updis (m, ack))\<cdot>(delayFun\<cdot>\<bottom>)"
  by (simp add: tssnd_delayfun_nack)

lemma tssnd_mlscons_ack: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow>
   tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr a) 
     = tsMLscons\<cdot>(updis (m, a))\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>a)))"
  by (simp add: tsSnd.simps(3) tsmlscons_lscons)

lemma tssnd_mlscons_nack: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> a\<noteq>ack \<Longrightarrow>
   tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr ack) 
     = tsMLscons\<cdot>(updis (m, ack))\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>acks\<cdot>(Discr ack))"
  by (simp add: tsSnd.simps(3) tsmlscons_lscons)

lemma tssnd_delayfun:
  "tsSnd\<cdot>(delayFun\<cdot>msg)\<cdot>(delayFun\<cdot>acks)\<cdot>ack = delayFun\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>ack)"
  by (simp add: delayfun_tslscons tsSnd.simps(5))
    
lemma tssnd_delayfun_msg:
  "acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(delayFun\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>acks)\<cdot>ack 
                      = delayFun\<cdot>(tsSnd\<cdot>msg\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>acks)\<cdot>ack)"
  by (simp add: delayfun_tslscons tsmlscons_lscons)

(* ToDo: basic properties lemmata for sender *)

lemma tssnd_nbot2 [simp]: "msg\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>msg\<cdot>(delayFun\<cdot>acks)\<cdot>(Discr ack) \<noteq> \<bottom>"
  apply (induction msg arbitrary: acks ack)
  apply (simp_all)
  apply (simp add: delayfun_tslscons)
  by (simp add: tssnd_delayfun_nack)

lemma tssnd_nbot [simp]: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr ack) \<noteq> \<bottom>"
  apply (induction acks arbitrary: msg ack)
  apply (simp_all)
  apply (rule_tac ts=msg in tscases, simp_all)
  apply (simp add: delayfun_tslscons tsmlscons_lscons)
  by (smt tsmlscons_bot2 tsmlscons_nbot tssnd_mlscons_ack tssnd_mlscons_nack up_defined)

lemma tssnd_tstickcount_adm:
  "adm (\<lambda>a. \<forall>x. #(Rep_tstream x) \<le> #(Rep_tstream a) \<longrightarrow> (\<forall>xa. #\<surd> x \<le> #\<surd> tsSnd\<cdot>x\<cdot>a\<cdot>(Discr xa)))"
  apply (rule admI) (* trick adm_imp *)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
  oops

lemma tssnd_tstickcount:
  "#(Rep_tstream msg) \<le> #(Rep_tstream acks) \<Longrightarrow> #\<surd>msg \<le> #\<surd>(tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr ack))"
(*proof (induction msg arbitrary: acks ack, simp_all)
  case adm
  then show ?case oops
next
  case (delayfun msg)
  have "Rep_tstream (delay msg) \<noteq> \<epsilon>" oops
  then show ?case proof (rule tscases [of acks], simp_all)
    assume "Rep_tstream (delay msg) = \<epsilon>"
next
  case (mlscons msg t)
  then show ?case oops
qed*)
(*
proof (induction acks arbitrary: msg ack)
  case adm
  then show ?case
    apply (rule adm_upward)
    by (simp add: tssnd_tstickcount_adm) (*proof (rule admI)
    fix Y :: "nat \<Rightarrow> bool tstream"
    assume Y_chain: "chain Y"
    assume a: "\<forall>i x. #(Rep_tstream x) \<le> #(Rep_tstream (Y i)) \<longrightarrow> (\<forall>xa. (#\<surd>x) \<le> (#\<surd>tsSnd\<cdot>x\<cdot>(Y i)\<cdot>(Discr xa)))"
    assume b: "\<forall>x. #(Rep_tstream x) \<le> #(Rep_tstream (\<Squnion>i. Y i))"
    from this have "\<forall>x. #(Rep_tstream x) \<le> (\<Squnion>i. #(Rep_tstream (Y i)))" oops
  qed*)
next
  case bottom
  then show ?case
    by (simp add: tstickcount_insert)
next
  case (delayfun acks)
  then show ?case proof (rule_tac ts=msg in tscases, simp_all)
    fix as :: "'a tstream"
    assume as_leq_acks: "#(Rep_tstream msg) \<le> #(Rep_tstream acks)"
    assume ind: "(\<And>msg ack. #(Rep_tstream msg) \<le> #(Rep_tstream acks) \<Longrightarrow>
                 #\<surd>msg \<le> #\<surd> tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr ack))"
    hence "#\<surd>msg \<le> #\<surd> tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr ack)"
      using as_leq_acks by (simp add: delayfun.IH)
    have "#\<surd> delay as = lnsuc\<cdot>(#\<surd>as)" by (simp add: delayFun_def)
    have "tsSnd\<cdot>(delay as)\<cdot>(delay acks)\<cdot>(Discr ack) = delay (tsSnd\<cdot>as\<cdot>acks\<cdot>(Discr ack))"
      by (simp add: tsSnd.simps(5) delayfun_tslscons)
    oops
next
  case (mlscons acks t)
  then show ?case oops
*)
oops

lemma tssnd_tsabs_slen:
  "#(Rep_tstream msg) \<le> #(Rep_tstream acks) \<Longrightarrow> #(tsAbs\<cdot>msg) \<le> #(tsAbs\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>ack))"
oops

lemma tssnd_inftick: "acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>tsInfTick\<cdot>acks\<cdot>ack = tsInfTick"
proof (induction acks arbitrary: ack)
  case adm
  then show ?case by (rule adm_imp, simp_all)
next
  case bottom
  then show ?case using bottom.prems by blast
next
  case (delayfun acks)
  (*have delay_inftick: "delay (Abs_tstream \<up>(\<surd>::'a event)\<infinity>) = tsInfTick"
    by (metis (no_types)
        Rep_Abs delayFun.rep_eq sinftimes_unfold tick_msg tsInfTick.abs_eq tsInfTick.rep_eq
        tsconc_insert)*)
  have inftick_delay: "tsInfTick = delay tsInfTick" by simp
  have delay_both: "\<forall>msg acks' ack'. acks' = \<bottom> \<or>
        tsSnd\<cdot>(delay (msg::'a tstream))\<cdot>(delay (acks'::bool tstream))\<cdot>ack' = delay (tsSnd\<cdot>msg\<cdot>acks'\<cdot>ack')"
    using tssnd_delayfun by blast
  assume ind: "\<And>ack. acks \<noteq> \<bottom> \<Longrightarrow> tsSnd\<cdot>tsInfTick\<cdot>acks\<cdot>ack = tsInfTick"
  have delay_nbot: "delay acks \<noteq> \<bottom>" by simp
  show ?case
    apply (subst inftick_delay)
    (*apply (case_tac "acks = \<bottom>", simp_all)*)
    apply (subst tssnd_delayfun)
    sorry
next
  case (mlscons acks t)
  have inftick_delay: "tsInfTick = delay tsInfTick" by simp
  have delay_msg: "\<forall>msg acks' ack1' ack2'. acks' = \<bottom> \<or>
        tsSnd\<cdot>(delay (msg::'a tstream))\<cdot>(tsMLscons\<cdot>(updis (ack1'::bool))\<cdot>(acks'::bool tstream))\<cdot>ack2' =
        delay (tsSnd\<cdot>msg\<cdot>(tsMLscons\<cdot>(updis ack1')\<cdot>acks')\<cdot>ack2')"
    by (metis delayfun_tslscons tsSnd.simps(6) tsmlscons_lscons)
  show ?case
    by (smt delayFun.rep_eq delay_msg inftick_delay mlscons.hyps s2sinftimes tick_msg tsconc_insert
            tsconc_rep_eq)
oops

(* ----------------------------------------------------------------------- *)
section {* additional properties *}
(* ----------------------------------------------------------------------- *)

(* ToDo: additional properties lemmata for sender *)

lemma tssnd_inftick_inftick: "tsSnd\<cdot>tsInfTick\<cdot>tsInfTick\<cdot>ack = tsInfTick" 
  by (metis (no_types, lifting) Rep_Abs delayfun_insert s2sinftimes sinftimes_unfold tick_msg 
      tsInfTick.rep_eq tsInfTick_def tsconc_insert tsconc_rep_eq tssnd_delayfun)
  
lemma tssnd_delayfun_abs:
  "tsAbs\<cdot>(tsSnd\<cdot>(delayFun\<cdot>msg)\<cdot>(delayFun\<cdot>acks)\<cdot>ack) 
                      = tsAbs\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>ack)"
  by (simp add: tssnd_delayfun)

lemma tssnd_delayfun_nack_abs:
  "msg\<noteq>\<bottom> \<Longrightarrow> tsAbs\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>acks)\<cdot>(Discr ack)) 
  = updis (m, ack) && (tsAbs\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>acks\<cdot>(Discr ack)))"
  by (simp add: tssnd_delayfun_nack tsabs_mlscons)

lemma tssnd_delayfun_bot_abs:
  "msg\<noteq>\<bottom> \<Longrightarrow> tsAbs\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>\<bottom>)\<cdot>(Discr ack)) 
     = updis (m, ack) && \<bottom>"
  by (simp add: tssnd_delayfun_bot tsabs_mlscons)

lemma tssnd_mlscons_nack_abs: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> a\<noteq>ack \<Longrightarrow>
   tsAbs\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr ack)) 
     = updis (m, ack) && tsAbs\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>acks\<cdot>(Discr ack))"
  by (simp add: tssnd_mlscons_nack tsabs_mlscons)
    
lemma tssnd_delayfun_msg_abs:
  "acks\<noteq>\<bottom> \<Longrightarrow> tsAbs\<cdot>(tsSnd\<cdot>(delayFun\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>acks)\<cdot>ack) 
                      = tsAbs\<cdot>(tsSnd\<cdot>msg\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>acks)\<cdot>ack)"
  by(simp add: tssnd_delayfun_msg)
    
lemma tssnd_mlscons_ack_abs:"msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow>
   tsAbs\<cdot>((tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr a))) 
     = (updis (m, a)) && (tsAbs\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>a))))"
  by (simp add: tsabs_mlscons tssnd_mlscons_ack)


text {* fds \<sqsubseteq> i where fds = map(\<alpha>.ds, \<Pi>1) 
        fds is a prefix of i *} 

lemma tssnd_prefix_inp_h4:"(\<And>tb ack as. sprojfst\<cdot>(srcdups\<cdot>(\<up>(tb, ack) \<bullet> 
          tsAbs\<cdot>(tsSnd\<cdot>asc\<cdot>as\<cdot>(Discr (\<not> ack))))) \<sqsubseteq>\<up>tb \<bullet> tsAbs\<cdot>asc) \<Longrightarrow>\<up>ta \<bullet> 
          sprojfst\<cdot>(srcdups\<cdot>(\<up>(tb, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>asc\<cdot>as\<cdot>(Discr ack)))) \<sqsubseteq> \<up>ta \<bullet> \<up>tb \<bullet> tsAbs\<cdot>asc"
  proof(induction as arbitrary: ta tb ack asc)
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
      apply(rule_tac ts = asc in tscases, simp_all)
      apply(simp add: tssnd_delayfun_abs)
      apply (metis tssnd_delayfun_abs)
      apply (case_tac "as = \<bottom>", simp_all)
      apply(simp add: tssnd_delayfun_nack_abs lscons_conv tsabs_mlscons)
    proof -
      fix a :: 'a and asb :: "'a tstream"
      assume a1: "\<And>tb ack as. sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, ack) \<bullet> 
               tsAbs\<cdot> (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot>asb)\<cdot> as\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>asb"
      assume a2: "asb \<noteq> \<bottom>"
      have "ack = ack"
        by auto
      then have f0:"\<And> ack. sprojfst\<cdot> (srcdups\<cdot> (\<up>(a,  ack) \<bullet> 
     tsAbs\<cdot> (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> asb)\<cdot> (delayFun\<cdot>as)\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>asb"
        using a1 by auto
      then have f3: "sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, \<not> ack) \<bullet> 
         tsAbs\<cdot> (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> asb)\<cdot> (delayFun\<cdot>as)\<cdot> (Discr ack)))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>asb"
        by (insert f0 [of "\<not>ack"], auto)
      have "tsAbs\<cdot> (tsSnd\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>asb)\<cdot> (delayFun\<cdot>as)\<cdot> (Discr ack)) = updis (a, ack) && 
          tsAbs\<cdot> (tsSnd\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>asb)\<cdot>as\<cdot> (Discr ack))"
        using a2 by (meson tssnd_delayfun_nack_abs)
      then have "srcdups\<cdot> (\<up>(a, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> asb)\<cdot> (delayFun\<cdot>as)\<cdot> 
                                   (Discr ack))) = \<up>(a, \<not> ack) \<bullet> srcdups\<cdot> (\<up>(a, ack) \<bullet> 
                                  tsAbs\<cdot> (tsSnd\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>asb)\<cdot> as\<cdot> (Discr ack)))"
        by (simp add: lscons_conv)
      then have "\<up>a \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, ack) \<bullet> tsAbs\<cdot> 
                          (tsSnd\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>asb)\<cdot>as\<cdot> (Discr ack)))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>asb"
        using f3 by simp
      then show "\<up>ta \<bullet> \<up>tb \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, ack) \<bullet> 
              tsAbs\<cdot> (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot>asb)\<cdot> as\<cdot> (Discr ack)))) \<sqsubseteq> \<up>ta \<bullet> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>asb"
        by (meson less_all_sconsD monofun_cfun_arg)
    qed
  next
    case (mlscons asa t)
    then show ?case
    apply(rule_tac ts = asc in tscases, simp_all)
    apply(simp add: tssnd_delayfun_msg_abs)defer
    apply(case_tac "as=\<bottom>", simp_all)
    apply(case_tac "t= ack", simp_all)
    apply(simp add: tssnd_mlscons_ack_abs lscons_conv tsabs_mlscons)defer
    apply(simp add: tssnd_mlscons_nack_abs lscons_conv tsabs_mlscons)
    proof -
      fix a :: 'a and as :: "'a tstream" and asa :: "bool tstream"
      assume a1: "\<And>tb ack asa. sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, ack) \<bullet> 
                tsAbs\<cdot> (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot>as)\<cdot> asa\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>as"
      assume a2: "asa \<noteq> \<bottom>"
      assume a3: "as \<noteq> \<bottom>"
      have "ack = ack"
        by auto
      then have f0: "\<And>ack asa. sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb,  ack) \<bullet> 
                tsAbs\<cdot> (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> as)\<cdot> asa\<cdot> (Discr (\<not>ack))))) \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>as"
        using a1 by blast
      then have "sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> as)\<cdot> 
                                     (tsMLscons\<cdot>(updis ack)\<cdot>asa)\<cdot>(Discr ack)))) \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>as"
        by (insert f0 [of "\<not>ack"], auto)
      then have "\<up>tb \<bullet> sprojfst\<cdot> (srcdups\<cdot> ( \<up>(a,  ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>as\<cdot>asa\<cdot>(Discr (\<not> ack))))) 
                 \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>as"
        by (simp add: a2 a3 lscons_conv tssnd_mlscons_ack_abs)
      then show "\<up>ta \<bullet> \<up>tb \<bullet> sprojfst\<cdot>(srcdups\<cdot>(\<up>(a, ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>as\<cdot>asa\<cdot>(Discr (\<not> ack))))) 
                    \<sqsubseteq> \<up>ta \<bullet> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>as"
        using monofun_cfun_arg by blast
    next
      fix a :: 'a and asb :: "'a tstream"
      assume a1: "\<And>tb ack as. sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, ack) \<bullet> tsAbs\<cdot> 
                      (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot>asb)\<cdot> as\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>asb"
      assume a2: "asb \<noteq> \<bottom>"
      have "ack = ack"
        by auto
      then have f0:"\<And>ack. sprojfst\<cdot> (srcdups\<cdot> (\<up>(a,  ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> asb)\<cdot> 
                        (delayFun\<cdot>asa)\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>asb"
        using a1 by blast
      then have "sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot> asb)\<cdot> 
                 (delayFun\<cdot>asa)\<cdot> (Discr ack)))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>asb"
        by (insert f0 [of "\<not>ack"], auto) 
      then have "\<up>a \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>asb)\<cdot>asa\<cdot> 
                   (Discr ack)))) \<sqsubseteq> \<up>a \<bullet> \<up>a \<bullet> tsAbs\<cdot>asb"
        using a2 by (simp add: lscons_conv tssnd_delayfun_nack_abs)
      then show "\<up>ta \<bullet> \<up>tb \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(a, ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot> (tsMLscons\<cdot>(updis a)\<cdot>asb)\<cdot> 
                asa\<cdot> (Discr ack)))) \<sqsubseteq> \<up>ta \<bullet> \<up>tb \<bullet> \<up>a \<bullet> tsAbs\<cdot>asb"
        by (meson less_all_sconsD monofun_cfun_arg)
    next
      fix asb :: "'a tstream"
      assume a1: "\<And>tb ack as. sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>(delayFun\<cdot>asb)\<cdot>as\<cdot> 
                    (Discr (\<not> ack))))) \<sqsubseteq> \<up>tb \<bullet> tsAbs\<cdot>asb"
      have "ack = ack"
        by auto
      then have f0: "\<And>ack . sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>(delayFun\<cdot>asb)\<cdot>(delayFun\<cdot> 
                    (tsMLscons\<cdot>(updis t)\<cdot> asa))\<cdot> (Discr (\<not> ack))))) \<sqsubseteq> \<up>tb \<bullet> tsAbs\<cdot>asb"
        using a1 by auto
      then have "sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>(delayFun\<cdot>asb)\<cdot> 
                        (delayFun\<cdot> (tsMLscons\<cdot>(updis t)\<cdot> asa))\<cdot> (Discr ack)))) \<sqsubseteq> \<up>tb \<bullet> tsAbs\<cdot>asb"
        by (insert f0 [of "\<not>ack"], auto)
      then show "\<up>ta \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(tb, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asb\<cdot> (tsMLscons\<cdot>(updis t)\<cdot>asa)\<cdot> 
                   (Discr ack)))) \<sqsubseteq> \<up>ta \<bullet> \<up>tb \<bullet> tsAbs\<cdot>asb"
        by (simp add: monofun_cfun_arg tsabs_delayfun tssnd_delayfun)
    qed
  qed

lemma tssnd_prefix_inp_h3:"(\<And>ta ack as. sprojfst\<cdot>(srcdups\<cdot>(\<up>(ta, ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>asa\<cdot>as\<cdot>
           (Discr (\<not> ack))))) \<sqsubseteq> \<up>ta \<bullet> tsAbs\<cdot>asa) \<Longrightarrow> asa \<noteq> \<bottom> \<Longrightarrow> \<up>ta \<bullet> sprojfst\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack)
            \<bullet> tsAbs\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>asa)\<cdot>as\<cdot>(Discr (\<not> ack))))) \<sqsubseteq> \<up>ta \<bullet> \<up>t \<bullet> tsAbs\<cdot>asa"
  apply(induction as arbitrary: ta t ack asa,simp_all)
  apply(simp add: monofun_cfun_arg)
  apply(simp add: tssnd_delayfun_nack_abs lscons_conv)
  apply(case_tac "t=ack")
  apply(simp add: tssnd_mlscons_nack_abs lscons_conv)
  by(simp add: tssnd_mlscons_ack_abs lscons_conv tssnd_prefix_inp_h4)  
    
lemma tssnd_prefix_inp_h2:"sprojfst\<cdot>(srcdups\<cdot>(updis (ta, ack) && tsAbs\<cdot>(tsSnd\<cdot>asc\<cdot>as\<cdot>(Discr (\<not> ack)))))
                         \<sqsubseteq> updis ta && tsAbs\<cdot>asc"
  proof(induction asc arbitrary: ta ack as)
  fix asc:: "'a tstream" and as:: "bool tstream" and ack:: "bool discr" and ta:: "'a"
    case adm
    then show ?case 
    by simp
  next
    case bottom
    then show ?case
    by(simp add: lscons_conv)
  next
    case (delayfun asa)
    then show ?case
    apply(rule_tac ts = as in tscases, simp_all)
    apply(simp add: lscons_conv)    
    apply(simp add: tssnd_delayfun_abs)
    apply(case_tac "as=\<bottom>")    
    apply(simp add: lscons_conv)    
    by(simp add: tssnd_delayfun_msg_abs)
  next
    case (mlscons asa t)
    then show ?case
    apply(rule_tac ts=as in tscases, simp_all)
    apply(simp add: lscons_conv)  
    apply(simp add: tssnd_delayfun_nack_abs lscons_conv tsabs_mlscons tssnd_prefix_inp_h3)
    apply(case_tac "as=\<bottom>",simp)
    apply(simp add:lscons_conv)
    apply(case_tac "a=ack")
    apply(simp add: tssnd_mlscons_nack_abs tsabs_mlscons lscons_conv tssnd_prefix_inp_h3) 
    apply(simp add: tssnd_mlscons_ack_abs lscons_conv tsabs_mlscons)
    proof -
      fix a :: bool and asd :: "bool tstream"
      assume a1: "\<And>ta ack as. sprojfst\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>as\<cdot> 
                    (Discr (\<not> ack))))) \<sqsubseteq> \<up>ta \<bullet> tsAbs\<cdot>asa"
      have "ack = ack"
        by auto
      then have f0: "\<And>ack . sprojfst\<cdot> (srcdups\<cdot> (\<up>(t, ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>asd\<cdot> (Discr (\<not> ack))))) 
                   \<sqsubseteq> \<up>t \<bullet> tsAbs\<cdot>asa"
        using a1 by auto    
      then have "sprojfst\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>asd\<cdot> (Discr ack)))) 
                \<sqsubseteq> \<up>t \<bullet> tsAbs\<cdot>asa"
        by (insert f0 [of "\<not>ack"], auto)
      then show "\<up>ta \<bullet> sprojfst\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>asd\<cdot>(Discr ack)))) 
              \<sqsubseteq> \<up>ta \<bullet> \<up>t \<bullet> tsAbs\<cdot>asa"
        using monofun_cfun_arg by blast
      qed
  qed
    
lemma tssnd_prefix_inp_h1: "asc \<noteq> \<bottom> \<Longrightarrow>
    sprojfst\<cdot>
    (srcdups\<cdot>( \<up>(t, ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>asc)\<cdot>as\<cdot>(Discr ack)))) \<sqsubseteq>
    \<up>t \<bullet> tsAbs\<cdot>asc"
  apply(induction as arbitrary: t ack asc, simp_all)
  apply(simp add: tssnd_delayfun_nack_abs lscons_conv)
  apply(case_tac "t\<noteq>ack")
  apply(simp add: tssnd_mlscons_nack_abs lscons_conv)
  apply(simp add: tssnd_mlscons_ack tsabs_mlscons lscons_conv)
  by (metis lscons_conv tssnd_prefix_inp_h2)

lemma tssnd_prefix_inp: "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>(Discr ack)))) \<sqsubseteq> tsAbs\<cdot>i"
  apply(simp add: tsremdups_tsabs tsprojfst_tsabs)
  proof(induction as arbitrary: i ack,simp_all)
    fix i:: "'a tstream" and as:: "bool tstream" and ack:: "bool discr"
    case (delayfun as)
    then show ?case
    apply(rule_tac ts = i in tscases, simp_all)
    apply(simp add: tssnd_delayfun_abs)
    apply(case_tac "as=\<bottom>")    
    apply(simp add: lscons_conv)    
    by(simp add: tssnd_delayfun_nack_abs lscons_conv tsabs_mlscons tssnd_prefix_inp_h1)
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
      by(simp add: tssnd_delayfun_msg_abs)
    next
      case (mlscons i ta)
      then show ?case
      apply(case_tac "t\<noteq>ack")
      apply(simp add: tssnd_mlscons_nack_abs tsabs_mlscons lscons_conv tssnd_prefix_inp_h1)
      by(simp add: tssnd_mlscons_ack tsabs_mlscons tssnd_prefix_inp_h2)
    qed
  qed
    
    
text {* \<alpha>.fb = fb  where fb = map(\<alpha>.ds, \<Pi>2)
        each new data element from i is assigned a bit different from the bit assigned to 
        the previous one*}
lemma tssnd_alt_bit_h5:"(\<And>ack t as. srcdups\<cdot>(\<up>ack \<bullet> sprojsnd\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack) \<bullet> 
      tsAbs\<cdot>(tsSnd\<cdot>asa\<cdot>as\<cdot>(Discr ack))))) = \<up>ack \<bullet> sprojsnd\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>asa\<cdot>as\<cdot>
 (Discr ack))))) \<Longrightarrow> asa\<noteq>\<bottom> \<Longrightarrow> \<up>ack \<bullet> srcdups\<cdot>(\<up>(\<not> ack) \<bullet> sprojsnd\<cdot>(srcdups\<cdot>(\<up>(ta, ack) \<bullet> 
  tsAbs\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis ta)\<cdot>asa)\<cdot>as\<cdot>(Discr ack))))) = \<up>ack \<bullet> \<up>(\<not> ack) \<bullet> 
    sprojsnd\<cdot>(srcdups\<cdot>(\<up>(ta, ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis ta)\<cdot>asa)\<cdot>as\<cdot>(Discr ack))))"
  apply(induction as arbitrary: ta ack asa,simp_all)
  apply(subst srcdups_def [THEN fix_eq2],simp)
  apply(simp add: tssnd_delayfun_nack_abs lscons_conv)
  apply(case_tac "t\<noteq>ack")
  apply(simp add: tssnd_mlscons_nack_abs lscons_conv)
  apply(simp add: tssnd_mlscons_ack_abs lscons_conv)
  proof -
    fix asb :: "bool tstream" and t :: bool and taa :: 'a and acka :: bool and asaa :: "'a tstream"
    assume a1: "\<And>ack t as. srcdups\<cdot> (\<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asaa\<cdot>as\<cdot>
      (Discr ack))))) = \<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asaa\<cdot>as\<cdot>(Discr ack))))"
    then have f0:"\<And>ack. srcdups\<cdot> (\<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(taa, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asaa\<cdot>asb\<cdot>
   (Discr ack))))) = \<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(taa, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asaa\<cdot>asb\<cdot>(Discr ack))))"
      by auto
    then have"srcdups\<cdot> (\<up>(\<not> acka) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(taa, acka) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asaa\<cdot>asb\<cdot> 
       (Discr (\<not> acka)))))) = \<up>(\<not> acka) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(taa, acka) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asaa\<cdot>asb\<cdot> 
            (Discr (\<not> acka)))))"
      by (insert f0 [of "\<not>acka"], auto)
    then show "\<up>acka \<bullet> srcdups\<cdot> (\<up>(\<not> acka) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(taa, acka) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>asaa\<cdot>asb\<cdot>
   (Discr (\<not> acka)))))) = \<up>acka \<bullet> \<up>(\<not> acka) \<bullet> sprojsnd\<cdot>(srcdups\<cdot> (\<up>(taa, acka) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>asaa\<cdot>asb\<cdot> 
             (Discr (\<not> acka)))))"
      by simp
  qed

lemma tssnd_alt_bit_h4:
          "srcdups\<cdot>(\<up>ack \<bullet> sprojsnd\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>(Discr ack))))) 
                          = \<up>ack \<bullet> sprojsnd\<cdot>(srcdups\<cdot>(\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>(Discr ack))))"
  proof(induction i arbitrary: ack t as)
  fix i:: "'a tstream" and as:: "bool tstream" and ack:: "bool discr" and t::"'a"
    case adm
    then show ?case
    by simp
  next
    case bottom
    then show ?case 
    by(subst srcdups_def [THEN fix_eq2],simp)
  next
    case (delayfun asa)
    then show ?case
      apply(rule_tac ts= as in tscases, simp_all)
      apply(subst srcdups_def [THEN fix_eq2],simp)
      apply(simp add: tssnd_delayfun_abs)
      apply(case_tac "as=\<bottom>", simp_all)
      apply(subst srcdups_def [THEN fix_eq2],simp)
      by(simp add: tssnd_delayfun_msg_abs)
  next
    case (mlscons asa ta)
    then show ?case
    apply(rule_tac ts= as in tscases, simp_all)
    apply(subst srcdups_def [THEN fix_eq2],simp)
    apply(simp add: tssnd_delayfun_nack_abs lscons_conv tssnd_alt_bit_h5)
    apply(case_tac "as=\<bottom>", simp)
    apply(subst srcdups_def [THEN fix_eq2],simp_all)
    apply(case_tac "a\<noteq>ack", simp_all)
    apply(simp add: tssnd_mlscons_nack_abs lscons_conv tssnd_alt_bit_h5)    
    apply(simp add: tssnd_mlscons_ack_abs lscons_conv)
    proof -
      fix a :: bool and asc :: "bool tstream"
      assume a1: "\<And>ack t as. srcdups\<cdot> (\<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>as\<cdot>
       (Discr ack))))) = \<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(t, \<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>as\<cdot>(Discr ack))))"
      then have f0:"\<And>ack. srcdups\<cdot> (\<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta,\<not> ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>asc\<cdot> 
   (Discr  ack))))) = \<up>ack \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, \<not>ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>asc\<cdot> (Discr  ack))))"
        by auto
      then have"srcdups\<cdot> (\<up>(\<not> ack) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>asc\<cdot> 
                               (Discr (\<not> ack)))))) =  \<up>(\<not> ack) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> 
                                tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>asc\<cdot> (Discr (\<not> ack)))))"
        by (insert f0 [of "\<not>ack"], auto)
      then show "\<up>ack \<bullet> srcdups\<cdot> (\<up>(\<not> ack) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>asc\<cdot> 
           (Discr (\<not> ack)))))) = \<up>ack \<bullet> \<up>(\<not> ack) \<bullet> sprojsnd\<cdot> (srcdups\<cdot> (\<up>(ta, ack) \<bullet> 
                           tsAbs\<cdot> (tsSnd\<cdot>asa\<cdot>asc\<cdot> (Discr (\<not> ack)))))"
      by simp
    qed
  qed 
    
lemma tssnd_alt_bit_h3:"i \<noteq> \<bottom> \<Longrightarrow> srcdups\<cdot>
    (\<up>ack \<bullet> sprojsnd\<cdot>
            (srcdups\<cdot>
             (\<up>(ta, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis ta)\<cdot>i)\<cdot>as\<cdot>(Discr (\<not> ack)))))) =
    \<up>ack \<bullet> sprojsnd\<cdot>
           (srcdups\<cdot>(\<up>(ta, \<not> ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis ta)\<cdot>i)\<cdot>as\<cdot>(Discr (\<not> ack)))))"
  apply(induction as arbitrary: ack ta i,simp_all)
  apply(subst srcdups_def [THEN fix_eq2], simp)
  apply(simp add: tssnd_delayfun_nack_abs lscons_conv)
  apply(case_tac "t=ack")
  apply(simp add: tssnd_mlscons_nack_abs lscons_conv)
  by(simp add: tssnd_mlscons_ack_abs lscons_conv tssnd_alt_bit_h4)

lemma tssnd_alt_bit_h2:"
       srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(\<up> (t, ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>(Discr (\<not>ack)))))) =
       sprojsnd\<cdot>(srcdups\<cdot>(\<up> (t, ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>(Discr (\<not>ack)))))"
  proof(induction i arbitrary: as ack t )
  fix i:: "'a tstream" and as:: "bool tstream" and ack:: "bool discr" and t::"'a"
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
    apply(simp add: tssnd_delayfun_abs)
    apply(case_tac "as=\<bottom>", simp_all)
    by(simp add: tssnd_delayfun_msg_abs)
  next
    case (mlscons asa ta)
    then show ?case
    apply(rule_tac ts=as in tscases, simp_all) 
    apply(simp add: tssnd_delayfun_nack_abs lscons_conv)
    using tssnd_alt_bit_h3 apply blast
    apply(case_tac "as=\<bottom>",simp_all)
    apply(case_tac "a=(\<not> ack)")
    apply(simp add: tssnd_mlscons_ack_abs lscons_conv)
    using tssnd_alt_bit_h4 apply blast
    apply(simp add: tssnd_mlscons_ack_abs lscons_conv)
    by (simp add: lscons_conv tssnd_alt_bit_h3 tssnd_mlscons_nack_abs)  
  qed

lemma tssnd_alt_bit_h1:"i\<noteq>\<bottom> \<Longrightarrow> srcdups\<cdot>(sprojsnd\<cdot>(srcdups\<cdot>(\<up> (t, ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>
      (tsMLscons\<cdot>(updis t)\<cdot>i)\<cdot>as\<cdot>(Discr ack))))) = sprojsnd\<cdot>(srcdups\<cdot>(\<up> (t, ack) \<bullet> tsAbs\<cdot>(tsSnd\<cdot>
      (tsMLscons\<cdot>(updis t)\<cdot>i)\<cdot>as\<cdot>(Discr ack))))"
  apply(induction as arbitrary: i ack t, simp_all)
  apply(simp add: tssnd_delayfun_nack_abs lscons_conv)
  apply(rename_tac  ta i ack t )  
  apply(case_tac "ta\<noteq>ack")
  apply(simp add: tssnd_mlscons_nack_abs lscons_conv)
  by(simp add: tssnd_mlscons_ack_abs lscons_conv tssnd_alt_bit_h2)

lemma tssnd_alt_bit:
  "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>(Discr ack)))))
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>(Discr ack))))"
  apply(simp add: tsremdups_tsabs tsprojsnd_tsabs)
  proof(induction i arbitrary: as ack, simp_all)
  fix i:: "'a tstream" and as:: "bool tstream" and ack:: "bool discr"
  case (delayfun i)
  then show ?case
    apply(rule_tac ts=as in tscases,simp_all)
    apply(simp add: tssnd_delayfun_abs)
    apply(case_tac "as=\<bottom>",simp_all)
    by(simp add: tssnd_delayfun_msg_abs)  
  next
    case (mlscons i t)
    then show ?case
    apply(rule_tac ts=as in tscases,simp_all)
    apply(simp add:tssnd_delayfun_nack_abs lscons_conv tssnd_alt_bit_h1)
    apply(case_tac "as=\<bottom>",simp_all)
    apply(case_tac "a=ack")
    apply(simp add: tssnd_mlscons_ack_abs lscons_conv tssnd_alt_bit_h2)
    by(simp add: tssnd_mlscons_nack_abs lscons_conv tssnd_alt_bit_h1)
  qed

text {* #fds = min{#i, #fas+1} where fds = map(\<alpha>.ds, \<Pi>1), fas = \<alpha>.as 
        when an acknowledgment is received then the next data next data element will eventually
        be transmitted given that there are more data elements to transmit *}
lemma tssnd_ack2trans:
  "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack))))
     = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as))))"
oops


text {* #i > #fas \<Longrightarrow> #ds = \<infinity> where fas = \<alpha>.as
        if a data element is never acknowledged despite repetitive transmission by the sender 
        then the sender never stops transmitting this data element *}
lemma tssnd_nack2inftrans:
  "#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> #(tsAbs\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack)) = \<infinity>"
oops
    
end
