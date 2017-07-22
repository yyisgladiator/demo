(*  Title:        Sender.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Sender Component of the ABP on Timed Streams
*)

chapter {* Components of the Alternating Bit Protocol *}
                                                            
theory Sender
imports "../../TStream"

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* Definition *}
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
  (if (a = ack) then tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack)))
  (* wrong ack for the current msg \<Longrightarrow> send msg again *)
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if an input and ack is a tick \<Longrightarrow> send msg again plus a tick
     if transmission starts with tick \<Longrightarrow> #\<surd> acks=\<infinity> *)
"msg\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack 
  = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(delayFun\<cdot>(tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if input is a tick \<Longrightarrow> send tick *)
"acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>acks\<cdot>ack
                    = delayFun\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>ack)"

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

declare tsSnd.simps [simp del]

lemma tssnd_strict [simp]:
"tsSnd\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>ack = \<bottom>"
"tsSnd\<cdot>\<bottom>\<cdot>acks\<cdot>ack = \<bottom>"
"tsSnd\<cdot>msg\<cdot>\<bottom>\<cdot>ack = \<bottom>"
  by (fixrec_simp)+

lemma tssnd_tslscons_msgtick [simp]: 
  "msg\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack 
     = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>
         (delayFun\<cdot>(tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>acks\<cdot>ack))"
  by (fixrec_simp)

lemma tssnd_tslscons_msgack [simp]: 
  "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack = 
    (if (a = ack) then tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack)))
     else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>acks\<cdot>ack))"
  by (fixrec_simp)

lemma tssnd_tslscons_tick [simp]: 
  "acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>acks\<cdot>ack 
                      = delayFun\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>ack)"
  by (fixrec_simp)

lemma tssnd_delayfun_nack:
  "msg\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>acks)\<cdot>(Discr ack) 
  = tsMLscons\<cdot>(updis (m, ack))\<cdot>(delayFun\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>acks\<cdot>(Discr ack)))"
  by (simp add: delayfun_tslscons tsmlscons_lscons)

lemma tssnd_delayfun_bot:
  "msg\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>\<bottom>)\<cdot>(Discr ack) 
     = tsMLscons\<cdot>(updis (m, ack))\<cdot>(delayFun\<cdot>\<bottom>)"
  by (simp add: delayfun_tslscons tsmlscons_lscons)

lemma tssnd_mlscons_ack: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow>
   tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr a) 
     = tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>a))"
  by (simp add: tsmlscons_lscons)

lemma tssnd_mlscons_nack: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> a\<noteq>ack \<Longrightarrow>
   tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr ack) 
     = tsMLscons\<cdot>(updis (m, ack))\<cdot>(tsSnd\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>acks\<cdot>(Discr ack))"
  by (simp add: tsmlscons_lscons)

lemma tssnd_delayfun:
  "acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>(delayFun\<cdot>msg)\<cdot>acks\<cdot>ack 
                      = delayFun\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>ack)"
  by (simp add: delayfun_tslscons)

(* ToDo: basic properties lemmata for sender *)

lemma tssnd_nbot2 [simp]: "msg\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>msg\<cdot>(delayFun\<cdot>acks)\<cdot>(Discr ack) \<noteq> \<bottom>"
  apply (induction msg arbitrary: acks ack)
  apply (simp_all)
  apply (simp add: tssnd_delayfun)
  by (simp add: tssnd_delayfun_nack)

lemma tssnd_nbot [simp]: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr ack) \<noteq> \<bottom>"
  apply (induction acks arbitrary: msg ack)
  apply (simp_all)
  apply (rule_tac ts=msg in tscases, simp_all)
  apply (simp add: tssnd_delayfun)
  apply (case_tac "t=ack", simp_all)
  apply (metis tsmlscons_nbot_rev tssnd_mlscons_ack)
  by (metis tsmlscons_bot2 tsmlscons_nbot tssnd_mlscons_nack up_defined)

lemma tssnd_tstickcount: 
  "#(Rep_tstream msg) \<le> #(Rep_tstream acks) \<Longrightarrow> #\<surd>msg \<le> #\<surd>(tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr ack))"
oops

lemma tssnd_tsabs_slen: 
  "#(Rep_tstream msg) \<le> #(Rep_tstream acks) \<Longrightarrow> #(tsAbs\<cdot>msg) \<le> #(tsAbs\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>ack))"
oops

lemma tssnd_inftick: "acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>tsInfTick\<cdot>acks\<cdot>ack = tsInfTick"
proof -
  assume a1: "acks \<noteq> \<bottom>"
  have f2: "delay (Abs_tstream \<up>(\<surd>::'a event)\<infinity>) = tsInfTick"
    by (metis (no_types)
        Rep_Abs delayFun.rep_eq sinftimes_unfold tick_msg tsInfTick.abs_eq tsInfTick.rep_eq
        tsconc_insert)
  have "\<forall>t ta d. t = \<bottom> \<or> tsSnd\<cdot>(delay (ta::'a tstream))\<cdot>t\<cdot>d = delay (tsSnd\<cdot>ta\<cdot>t\<cdot>d)"
    using tssnd_delayfun by blast
  then have "tsSnd\<cdot>(tsInfTick::'a tstream)\<cdot>acks\<cdot>ack = delay (tsSnd\<cdot>(Abs_tstream \<up>\<surd>\<infinity>)\<cdot>acks\<cdot>ack)"
    using f2 a1 by (metis (no_types))
  then show ?thesis
    by (metis (no_types)
        Rep_Abs delayFun.rep_eq s2sinftimes tick_msg tsInfTick.abs_eq tsconc_insert tsconc_rep_eq)
qed

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