(*  Title:        TimedABP_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Workspace for the  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory TimedABP_DS
imports TimedABP

begin
default_sort countable

(* input: msg from the user, acks from the receiver, ack buffer for the expected ack 
   output: msg and expected ack for the receiver *)
fixrec tsSender :: "'a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> ('a \<times> bool) tstream" where
  (* bottom case *)
"tsSender\<cdot>\<bottom>\<cdot>acks\<cdot>ack = \<bottom>" |
"tsSender\<cdot>msg\<cdot>\<bottom>\<cdot>ack = \<bottom>" |

  (* if an input and ack from the receiver *)
"msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack = 
  (* ack for the current msg \<Longrightarrow> send next msg *)
  (if (a = ack) then tsSender\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack)))
  (* wrong ack for the current msg \<Longrightarrow> send msg again *)
   else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if an input and ack is a tick \<Longrightarrow> send msg again plus a tick
     if transmission starts with tick \<Longrightarrow> #\<surd> acks=\<infinity> *)
"msg\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack 
  = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(delayFun\<cdot>(tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>acks\<cdot>ack))" |

  (* if input is a tick \<Longrightarrow> send tick *)
"acks\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>acks\<cdot>ack
        = delayFun\<cdot>(tsSender\<cdot>msg\<cdot>acks\<cdot>ack)"

declare tsSender.simps [simp del]

lemma tssender_strict [simp]:
"tsSender\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>ack = \<bottom>"
"tsSender\<cdot>\<bottom>\<cdot>acks\<cdot>ack = \<bottom>"
"tsSender\<cdot>msg\<cdot>\<bottom>\<cdot>ack = \<bottom>"
by (fixrec_simp)+

lemma tssender_tslscons_msgtick [simp]: 
  "msg\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>acks)\<cdot>ack 
     = tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>
         (delayFun\<cdot>(tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>acks\<cdot>ack))"
by (fixrec_simp)

lemma tssender_tslscons_msgack [simp]: 
  "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>a))\<cdot>acks)\<cdot>ack = 
    (if (a = ack) then tsSender\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>(undiscr ack)))
     else tsMLscons\<cdot>(upApply2 Pair\<cdot>(up\<cdot>m)\<cdot>(up\<cdot>ack))\<cdot>(tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>m))\<cdot>msg)\<cdot>acks\<cdot>ack))"
by (fixrec_simp)

lemma tssender_tslscons_tick [simp]: 
  "acks\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>msg)\<cdot>acks\<cdot>ack 
          = delayFun\<cdot>(tsSender\<cdot>msg\<cdot>acks\<cdot>ack)"
by (fixrec_simp)

lemma tssender_delayfun_nack:
  "msg\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>acks)\<cdot>(Discr ack) 
  = tsMLscons\<cdot>(updis (m, ack))\<cdot>(delayFun\<cdot>(tsSender\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>acks\<cdot>(Discr ack)))"
by (simp add: delayfun_tslscons tsmlscons_lscons)

lemma tssender_delayfun_bot:
  "msg\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(delayFun\<cdot>\<bottom>)\<cdot>(Discr ack) 
     = tsMLscons\<cdot>(updis (m, ack))\<cdot>(delayFun\<cdot>\<bottom>)"
by (simp add: delayfun_tslscons tsmlscons_lscons)

lemma tssender_mlscons_ack: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow>
   tsSender\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr a) 
     = tsSender\<cdot>msg\<cdot>acks\<cdot>(Discr (\<not>a))"
by (simp add: tsmlscons_lscons)

lemma tssender_mlscons_nack: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> a\<noteq>ack \<Longrightarrow>
   tsSender\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(tsMLscons\<cdot>(updis a)\<cdot>acks)\<cdot>(Discr ack) 
     = tsMLscons\<cdot>(updis (m, ack))\<cdot>(tsSender\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>acks\<cdot>(Discr ack))"
by (simp add: tsmlscons_lscons)

lemma tssender_delayfun:
  "acks\<noteq>\<bottom> \<Longrightarrow> tsSender\<cdot>(delayFun\<cdot>msg)\<cdot>acks\<cdot>ack 
          = delayFun\<cdot>(tsSender\<cdot>msg\<cdot>acks\<cdot>ack)"
by (simp add: delayfun_tslscons)

lift_definition tsExampInp_1 :: "nat tstream" is
  "<[Msg 1, Msg 2, \<surd>, Msg 1, \<surd>]>"
by (subst ts_well_def, auto)

lemma tsexampinp_12mlscons: 
  "tsExampInp_1 = tsMLscons\<cdot>(updis 1)\<cdot>(tsMLscons\<cdot>(updis 2)\<cdot>
                     (delayFun\<cdot>(tsMLscons\<cdot>(updis 1)\<cdot>(delayFun\<cdot>\<bottom>))))"
apply (simp add: tsExampInp_1_def)
by (metis (no_types, lifting) One_nat_def absts2delayfun2 absts2delayfun_tick absts2mlscons2 
    list2s.simps(1) list2s.simps(2) lscons_conv sconc_scons sup'_def tick_msg tsExampInp_1.rep_eq
    ts_well_Rep ts_well_conc1 ts_well_sing_conc)

lift_definition tsExampInp_2 :: "bool tstream" is
  "<[\<surd>, Msg True, Msg True, \<surd>, Msg False, \<surd>, Msg True, \<surd>]>"
by (subst ts_well_def, auto)

lemma tsexampinp_22mlscons:
  "tsExampInp_2 = delayFun\<cdot>(tsMLscons\<cdot>(updis True)\<cdot>(tsMLscons\<cdot>(updis True)\<cdot>
                    (delayFun\<cdot>(tsMLscons\<cdot>(updis False)\<cdot>(delayFun\<cdot>
                       (tsMLscons\<cdot>(updis True)\<cdot>(delayFun\<cdot>\<bottom>)))))))"
apply (simp add: tsExampInp_2_def)
by (metis (no_types, lifting) Rep_Abs absts2mlscons2 delayfun_abststream delayfun_nbot
    lscons_conv sConc_fin_well absts2delayfun_tick ts_well_sing_conc tsmlscons_nbot up_defined)

lift_definition tsExampOut :: "(nat \<times> bool) tstream" is
  "<[Msg (1, True), \<surd>,  Msg (2, False), Msg (2, False), \<surd>, \<surd>, Msg (1, True), \<surd>, \<surd>]>"
by (subst ts_well_def, auto)

lemma "tsSender\<cdot>tsExampInp_1\<cdot>tsExampInp_2\<cdot>(Discr True) = tsExampOut"
apply (simp add: tsExampOut_def tsexampinp_12mlscons tsexampinp_22mlscons)
apply (simp add: tssender_delayfun_nack tssender_mlscons_ack tssender_mlscons_nack 
                 tssender_delayfun)
by (smt Rep_Abs absts2delayfun2 absts2delayfun_tick absts2mlscons2 delayfun_nbot sConc_fin_well
    tick_msg tsmlscons_nbot up_defined)

(* lemmata for sender, see BS01, page 103 *)

(* fds = stream of transmitted messages
   fb = corresponding stream of bits
   fas = stream of received acknowledgments
   i = input stream
   as = acks stream
   ds = output stream *)

(* fds \<sqsubseteq> i where fds = map(\<alpha>.ds, \<Pi>1) *)
(* fds is a prefix of i *)
lemma "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSender\<cdot>i\<cdot>as\<cdot>ack))) \<sqsubseteq> tsAbs\<cdot>i"
oops

(* \<alpha>.fb = fb  where fb = map(\<alpha>.ds, \<Pi>2) *)
(* each new data element from i is assigned a bit different from the bit assigned to 
   the previous one *)    
lemma 
  "tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSender\<cdot>i\<cdot>as\<cdot>ack))))
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSender\<cdot>i\<cdot>acks\<cdot>ack)))"
oops

(* #fds = min{#i, #fas+1} where fds = map(\<alpha>.ds, \<Pi>1), fas = \<alpha>.as *)
(* when an acknowledgment is received then the next data next data element will eventually
   be transmitted given that there are more data elements to transmit *)
(*
lemma
  "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSender\<cdot>i\<cdot>as\<cdot>ack)))) = min (#(tsAbs\<cdot>i)) ((#(tsAbs\<cdot>(tsRemDups\<cdot>as)))+1)"
oops
*)

(* #i > #fas \<Longrightarrow> #ds = \<infinity> where fas = \<alpha>.as *)
(* if a data element is never acknowledged despite repetitive transmission by the sender then the
   sender never stops transmitting this data element *)
lemma "#(tsAbs\<cdot>i)>#(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<Longrightarrow> #(tsAbs\<cdot>(tsSender\<cdot>i\<cdot>as\<cdot>ack)) = \<infinity>"
oops

end