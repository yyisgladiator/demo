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
  "acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(delayFun\<cdot>msg)\<cdot>(delayFun\<cdot>acks)\<cdot>ack = delayFun\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>ack)"
  by (simp add: delayfun_tslscons tsSnd.simps(5))

(* ToDo: basic properties lemmata for sender *)

lemma tssnd_nbot2 [simp]: "msg\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>msg\<cdot>(delayFun\<cdot>acks)\<cdot>(Discr ack) \<noteq> \<bottom>"
  apply (induction msg arbitrary: acks ack)
  apply (simp_all)
  apply (simp add: delayfun_tslscons tsSnd.simps(5))
  by (simp add: tssnd_delayfun_nack)

lemma tssnd_nbot [simp]: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr ack) \<noteq> \<bottom>"
  apply (induction acks arbitrary: msg ack)
  apply (simp_all)
  apply (rule_tac ts=msg in tscases, simp_all)
  apply (simp add: delayfun_tslscons tsSnd.simps(6) tsmlscons_lscons)
  by (smt tsmlscons_bot2 tsmlscons_nbot tssnd_mlscons_ack tssnd_mlscons_nack up_defined)

lemma tssnd_tstickcount_adm:
  "adm (\<lambda>a. \<forall>x. #(Rep_tstream x) \<le> #(Rep_tstream a) \<longrightarrow> (\<forall>xa. #\<surd> x \<le> #\<surd> tsSnd\<cdot>x\<cdot>a\<cdot>(Discr xa)))"
  apply (rule admI) (* trick adm_imp *)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
  sorry

(*lemma tssnd_tstickcount:
  "#(Rep_tstream msg) \<le> #(Rep_tstream acks) \<Longrightarrow> #\<surd>msg \<le> #\<surd>(tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr ack))"
(*proof (induction msg arbitrary: acks ack, simp_all)
  case adm
  then show ?case sorry
next
  case (delayfun msg)
  have "Rep_tstream (delay msg) \<noteq> \<epsilon>" sorry
  then show ?case proof (rule tscases [of acks], simp_all)
    assume "Rep_tstream (delay msg) = \<epsilon>"
next
  case (mlscons msg t)
  then show ?case sorry
qed*)
proof (induction acks arbitrary: msg ack)
  case adm
  then show ?case by (simp add: tssnd_tstickcount_adm) (*proof (rule admI)
    fix Y :: "nat \<Rightarrow> bool tstream"
    assume Y_chain: "chain Y"
    assume a: "\<forall>i x. #(Rep_tstream x) \<le> #(Rep_tstream (Y i)) \<longrightarrow> (\<forall>xa. (#\<surd>x) \<le> (#\<surd>tsSnd\<cdot>x\<cdot>(Y i)\<cdot>(Discr xa)))"
    assume b: "\<forall>x. #(Rep_tstream x) \<le> #(Rep_tstream (\<Squnion>i. Y i))"
    from this have "\<forall>x. #(Rep_tstream x) \<le> (\<Squnion>i. #(Rep_tstream (Y i)))" sorry
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
    sorry
next
  case (mlscons acks t)
  then show ?case sorry
qed*)

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
    apply (simp add: tsSnd.simps(5))
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
qed

(* ----------------------------------------------------------------------- *)
section {* additional properties *}
(* ----------------------------------------------------------------------- *)

(* ToDo: additional properties lemmata for sender *)

text {* lemmata for sender, see BS01, page 103 

   fds = stream of transmitted messages
   fb = corresponding stream of bits
   fas = stream of received acknowledgments
   i = input stream
   as = acks stream
   ds = output stream 
*}

text {* fds \<sqsubseteq> i where fds = map(\<alpha>.ds, \<Pi>1) 
        fds is a prefix of i *}
lemma tssnd_prefix_inp: "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack))) \<sqsubseteq> tsAbs\<cdot>i"
oops

text {* \<alpha>.fb = fb  where fb = map(\<alpha>.ds, \<Pi>2)
        each new data element from i is assigned a bit different from the bit assigned to 
        the previous one *}
lemma tssnd_alt_bit:
  "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack))))
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack)))"
oops

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
