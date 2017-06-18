(*  Title:        TimedABP.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory TimedABP
imports "../TStream"

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* components definition *}
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
subsection {* sender *}
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
subsection {* medium *}
(* ----------------------------------------------------------------------- *)

definition tsMed :: "'a tstream \<rightarrow> bool stream \<rightarrow> 'a tstream" where
"tsMed \<equiv> \<Lambda> msg ora. tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"

(* ----------------------------------------------------------------------- *)
subsection {* receiver *}
(* ----------------------------------------------------------------------- *)

definition tsRecSnd :: "('a \<times> 'b) tstream \<rightarrow> 'a tstream" where
"tsRecSnd \<equiv> \<Lambda> dat. tsProjFst\<cdot>(tsRemDups\<cdot>dat)"

definition tsRec :: "('a \<times> 'b) tstream \<rightarrow> ('b tstream \<times> 'a tstream)" where
"tsRec \<equiv> \<Lambda> dat. (tsProjSnd\<cdot>dat, tsRecSnd\<cdot>dat)"

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
subsection {* sender *}
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

lemma tssnd_nbot [simp]: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr ack) \<noteq> \<bottom>"
oops

lemma tssnd_tstickcount: "#\<surd>msg \<le> #\<surd>(tsSnd\<cdot>msg\<cdot>acks\<cdot>ack)"
oops

lemma tssnd_tsabs_slen: "#(tsAbs\<cdot>msg) \<le> #(tsAbs\<cdot>(tsSnd\<cdot>msg\<cdot>acks\<cdot>ack))"
oops

lemma tssnd_inftick: "acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>tsInfTick\<cdot>acks\<cdot>ack = tsInfTick"
oops

(* ----------------------------------------------------------------------- *)
subsection {* medium *}
(* ----------------------------------------------------------------------- *)

text {* Assumption for medium lemmata: #({True} \<ominus> ora)=\<infinity> *}

lemma tsmed_insert: "tsMed\<cdot>msg\<cdot>ora = tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
  by (simp add: tsMed_def)

(* ToDo: basic properties lemmata for medium *)

lemma tsmed_strict [simp]: 
  "tsMed\<cdot>\<bottom>\<cdot>\<epsilon> = \<bottom>"
  "tsMed\<cdot>msg\<cdot>\<epsilon> = \<bottom>"
  "tsMed\<cdot>\<bottom>\<cdot>ora = \<bottom>"
  by (simp add: tsMed_def)+

lemma tsmed_mlscons_true: "msg\<noteq>\<bottom> \<Longrightarrow> #ora=\<infinity> \<Longrightarrow> 
  tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>((updis True) && ora) = tsMLscons\<cdot>(updis m)\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
  apply (simp add: tsmed_insert)
  by (metis Inf'_neq_0 mem_Collect_eq prod.sel(2) slen_empty_eq tsfilter_mlscons_in
      tsfilter_nbot tsprojfst_mlscons tszip_mlscons tszip_nbot)

lemma tsmed_mlscons_false: "msg\<noteq>\<bottom> \<Longrightarrow> #ora=\<infinity> \<Longrightarrow> 
  tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>((updis False) && ora) = tsMed\<cdot>msg\<cdot>ora"
  apply (simp add: tsmed_insert)
  by (metis Inf'_neq_0 mem_Collect_eq prod.sel(2) slen_empty_eq tsfilter_mlscons_nin
      tszip_mlscons tszip_nbot)

lemma tsmed_delayfun: "ora\<noteq>\<epsilon> \<Longrightarrow> tsMed\<cdot>(delayFun\<cdot>msg)\<cdot>ora = delayFun\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
  by (simp add: tsMed_def tszip_delayfun tsfilter_delayfun tsprojfst_delayfun)

text {* If just infinite ticks will be sent just infinite ticks will be transmitted. *}
lemma tsmed_inftick [simp]: "#ora=\<infinity> \<Longrightarrow> tsMed\<cdot>tsInfTick\<cdot>ora = tsInfTick"
  apply (simp add: tsmed_insert tsInfTick_def tsfilter_unfold)
  by (metis (no_types, lifting)
      Inf'_neq_0 Rep_tstream_inject delayfun_insert insertI1 s2sinftimes sfilter_in
      sinftimes_unfold slen_empty_eq tick_msg tsInfTick.abs_eq tsInfTick.rep_eq
      tsconc_rep_eq tsprojfst_delayfun tszip_delayfun)

text {* Medium without oracle will transmit all messages and ticks. *}
lemma tsmed_inftrue [simp]: "tsMed\<cdot>msg\<cdot>((\<up>True) \<infinity>) = msg"
  oops

text {* If infinite ticks will be sent infinite ticks will be transmitted. *}
lemma tsmed_tstickcount [simp]: "#ora=\<infinity> \<Longrightarrow> #\<surd>(tsMed\<cdot>msg\<cdot>ora) = #\<surd>msg"
  by (simp add: tsmed_insert)

text {* Not every message will be transmitted. *}    
lemma tsmed_tsabs_slen: "#ora=\<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) \<le> #(tsAbs\<cdot>msg)"
  apply (simp add: tsmed_insert)
  by (metis tsfilter_tsabs_slen tszip_tsabs_slen)

text {* If infinite messages will be sent infinite messages will be transmitted. *}
lemma tsmed_tsabs_slen_inf [simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(tsAbs\<cdot>msg)=\<infinity>" 
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
  oops

lemma tsmed_map: "tsMed\<cdot>(tsMap f\<cdot>msg)\<cdot>ora = tsMap f\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
oops

lemma tsmed_tsdom: "#ora=\<infinity> \<Longrightarrow> tsDom\<cdot>(tsMed\<cdot>msg\<cdot>ora) \<subseteq> tsDom\<cdot>msg"
oops

(* ----------------------------------------------------------------------- *)
subsection {* receiver *}
(* ----------------------------------------------------------------------- *)

lemma tsrecsnd_insert: "tsRecSnd\<cdot>dat = tsProjFst\<cdot>(tsRemDups\<cdot>dat)"
by (simp add: tsRecSnd_def)

(* ToDo: basic properties lemmata for receiver *)

lemma tsrecsnd_strict [simp]: "tsRecSnd\<cdot>\<bottom> = \<bottom>"
oops

lemma tsrecsnd_delayfun: "tsRecSnd\<cdot>(delayFun\<cdot>dat) = delayFun\<cdot>(tsRecSnd\<cdot>dat)"
oops

lemma tsrecsnd_inftick [simp]: "tsRecSnd\<cdot>tsInfTick = tsInfTick"
oops

lemma tsrecsnd_tstickcount [simp]: "#\<surd>(tsRecSnd\<cdot>dat) = #\<surd>dat"
oops

lemma tsrec_insert: "tsRec\<cdot>dat = (tsProjSnd\<cdot>dat, tsRecSnd\<cdot>dat)"
by (simp add: tsRec_def)

lemma tsrec_strict [simp]: "tsRec\<cdot>\<bottom> = \<bottom>"
oops

lemma tsrec_delayfun: "tsRec\<cdot>(delayFun\<cdot>dat) = (delayFun\<cdot>(tsProjSnd\<cdot>dat), delayFun\<cdot>(tsRecSnd\<cdot>dat))"
oops

lemma tsrec_inftick [simp]: "tsRec\<cdot>tsInfTick = (tsInfTick, tsInfTick)"
oops

(* ----------------------------------------------------------------------- *)
section {* additional properties *}
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
subsection {* sender *}
(* ----------------------------------------------------------------------- *)

(* ToDo: additional properties lemmata for sender, first show testings below *)

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
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>acks\<cdot>ack)))"
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

(* ----------------------------------------------------------------------- *)
subsection {* medium *}
(* ----------------------------------------------------------------------- *)

(* ToDo: additional properties lemmata for medium, first show testings below *)

text {* Two medium can be reduced to one medium. *}
lemma tsmed2med: obtains ora3 where "tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>ora3"
oops

text {* Two medium with fairness requirement can be reduced to one medium with 
        fairness requirement. *}
lemma tsmed2infmed: assumes "#({True} \<ominus> ora1)=\<infinity>" and "#({True} \<ominus> ora2)=\<infinity>" 
  obtains ora3 where "tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>ora3" and "#({True} \<ominus> ora3)=\<infinity>"
oops    

(* ----------------------------------------------------------------------- *)
section {* testing *}
(* ----------------------------------------------------------------------- *)

text {* equivalence classes: empty tstream, finite tstream, infinite tstream *}

(* ----------------------------------------------------------------------- *)
subsection {* sender *}
(* ----------------------------------------------------------------------- *)

lift_definition tsSndExampInp_1 :: "nat tstream" is
  "<[Msg 1, Msg 2, \<surd>, Msg 1, \<surd>]>"
by (subst ts_well_def, auto)

lift_definition tsSndExampInp_2 :: "bool tstream" is
  "<[\<surd>, Msg True, Msg True, \<surd>, Msg False, \<surd>, Msg True, \<surd>]>"
by (subst ts_well_def, auto)

lift_definition tsSndExampOut :: "(nat \<times> bool) tstream" is
  "<[Msg (1, True), \<surd>,  Msg (2, False), Msg (2, False), \<surd>, \<surd>, Msg (1, True), \<surd>, \<surd>]>"
by (subst ts_well_def, auto)

(* ToDo: testing lemmata for sender *)

lemma tsmed_test_bot: "tsSnd\<cdot>\<bottom>\<cdot>tsInfTick = \<bottom>"
oops

lemma tssnd_test_fin: 
  "tsSnd\<cdot>tsSndExampInp_1\<cdot>(tsSndExampInp_2 \<bullet> tsInfTick)\<cdot>(Discr True) = tsSndExampOut"
oops

lemma tssnd_test_inf:
  "tsSnd\<cdot>(tsSndExampInp_1 \<bullet> tsInfTick)\<cdot>(tsSndExampInp_2 \<bullet> tsInfTick)\<cdot>(Discr True) 
       = tsSndExampOut \<bullet> tsInfTick"
oops

(* ----------------------------------------------------------------------- *)
subsection {* medium *}
(* ----------------------------------------------------------------------- *)

lift_definition tsMedExampInp :: "nat tstream" is
  "<[Msg 1, \<surd>, Msg 2, \<surd>, Msg 3, \<surd>]>"
by (subst ts_well_def, auto)

lift_definition tsMedExampOut :: "nat tstream" is
  "<[Msg 1, \<surd>, \<surd>, Msg 3, \<surd>]>"
by (subst ts_well_def, auto)

lemma tsmed_test_bot: "tsMed\<cdot>\<bottom>\<cdot>((\<up>True) \<infinity>) = \<bottom>"
by (simp add: tsmed_insert)

(* ToDo: testing lemmata for medium *)

lemma tsmed_test_fin: "tsMed\<cdot>tsMedExampInp\<cdot>((\<up>True) \<infinity>) = tsMedExampInp"
oops

lemma tsmed_test_fin2: "tsMed\<cdot>tsMedExampInp\<cdot>(<[True, False]> \<infinity>) = tsMedExampOut"
oops

lemma tsmed_test_inf:
  "tsMed\<cdot>(tsMedExampInp \<bullet> tsInfTick)\<cdot>((\<up>True) \<infinity>) = (tsMedExampInp \<bullet> tsInfTick)"
oops

(* ----------------------------------------------------------------------- *)
subsection {* receiver *}
(* ----------------------------------------------------------------------- *)

lift_definition tsRecExampInp :: "(nat \<times> bool) tstream" is
  "<[Msg (1, True), Msg (1, True), \<surd>, Msg (1, True), \<surd>, Msg (1, False), \<surd>]>"
by (subst ts_well_def, auto)

lift_definition tsRecExampOut_1 :: "bool tstream" is
  "<[Msg True, Msg True, \<surd>, Msg True, \<surd>, Msg False, \<surd>]>"
by (subst ts_well_def, auto)

lift_definition tsRecExampOut_2 :: "nat tstream" is
  "<[Msg 1, \<surd>, \<surd>, Msg 1, \<surd>]>"
by (subst ts_well_def, auto)

(* ToDo: testing lemmata for receiver *)

lemma tsrec_test_bot: "tsRec\<cdot>\<bottom> = \<bottom>"
oops

lemma tsrec_test_fin: "tsRec\<cdot>tsRecExampInp = (tsRecExampOut_1, tsRecExampOut_2)"
oops

lemma tsrec_test_inf:
  "tsRec\<cdot>(tsRecExampInp \<bullet> tsInfTick) = (tsRecExampOut_1 \<bullet> tsInfTick, tsRecExampOut_2 \<bullet> tsInfTick)"
oops
    
end