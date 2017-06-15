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

(* ----------------------------------------------------------------------- *)
subsection {* medium *}
(* ----------------------------------------------------------------------- *)

(* Assumption for medium  lemmata: #({True} \<ominus> ora)=\<infinity> *)

lemma tsmed_insert: "tsMed\<cdot>msg\<cdot>ora = tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
by (simp add: tsMed_def)

(* ToDo: basic properties lemmata for medium *)

lemma tsmed_strict [simp]: 
  "tsMed\<cdot>\<bottom>\<cdot>\<epsilon> = \<bottom>"
  "tsMed\<cdot>msg\<cdot>\<epsilon> = \<bottom>"
  "tsMed\<cdot>\<bottom>\<cdot>ora = \<bottom>"
oops

lemma tsmed_mlscons_true: "msg\<noteq>\<bottom> \<Longrightarrow> #ora=\<infinity> \<Longrightarrow> 
  tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>((updis True) && ora) = tsMLscons\<cdot>(updis m)\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
oops
    
lemma tsmed_mlscons_false: "msg\<noteq>\<bottom> \<Longrightarrow> #ora=\<infinity> \<Longrightarrow> 
  tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>((updis False) && ora) = tsMed\<cdot>msg\<cdot>ora"
oops

lemma tsmed_delayfun: "ora\<noteq>\<epsilon> \<Longrightarrow> tsMed\<cdot>(delayFun\<cdot>msg)\<cdot>ora = delayFun\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
oops
 
text {* If just infinite ticks will be sent just infinite ticks will be transmitted. *}
lemma tsmed_inftick [simp]: "#ora=\<infinity> \<Longrightarrow> tsMed\<cdot>tsInfTick\<cdot>ora = tsInfTick"
oops

text {* Medium without oracle will transmit all messages and ticks. *}
lemma tsmed_inftrue [simp]: "tsMed\<cdot>msg\<cdot>((\<up>True) \<infinity>) = msg"
oops

text {* If infinite ticks will be sent infinite ticks will be transmitted. *}
lemma tsmed_tstickcount [simp]: "#ora=\<infinity> \<Longrightarrow> #\<surd>(tsMed\<cdot>msg\<cdot>ora) = #\<surd>msg"
oops

text {* Not every message will be transmitted. *}    
lemma tsmed_tsabs_slen: "#ora=\<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) \<le> #(tsAbs\<cdot>msg)"
oops

text {* If infinite messages will be sent infinite messages will be transmitted. *}
lemma tsmed_tsabs_slen_inf [simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(tsAbs\<cdot>msg)=\<infinity>" 
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
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

lemma tsmed_map: "tsMed\<cdot>(tsMap f\<cdot>msg)\<cdot>ora = tsMap f\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
oops

(* ----------------------------------------------------------------------- *)
section {* testing *}
(* ----------------------------------------------------------------------- *)

text {* equivalence classes: empty tstream, finite tstream, infinite tstream *}

(* ----------------------------------------------------------------------- *)
subsection {* sender *}
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
subsection {* medium *}
(* ----------------------------------------------------------------------- *)

lift_definition tsMedExampInp :: "nat tstream" is
  "<[Msg 1, \<surd>, Msg 2, \<surd>, Msg 3, \<surd>]>"
by (subst ts_well_def, auto)

lift_definition tsMedExampOut :: "nat tstream" is
  "<[Msg 1, \<surd>, \<surd>, Msg 3, \<surd>]>"
by (subst ts_well_def, auto)

lemma "tsMed\<cdot>\<bottom>\<cdot>((\<up>True) \<infinity>) = \<bottom>"
by (simp add: tsmed_insert)

(* ToDo: testing lemmata for medium *)

lemma "tsMed\<cdot>tsMedExampInp\<cdot>((\<up>True) \<infinity>) = tsMedExampInp"
oops

lemma "tsMed\<cdot>tsMedExampInp\<cdot>(<[True, False]> \<infinity>) = tsMedExampOut"
oops

lemma "tsMed\<cdot>(tsMedExampInp \<bullet> tsInfTick)\<cdot>((\<up>True) \<infinity>) = (tsMedExampInp \<bullet> tsInfTick)"
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

lift_definition tsRecExampInp_2 :: "nat tstream" is
  "<[Msg 1, \<surd>, \<surd>, Msg 1, \<surd>]>"
by (subst ts_well_def, auto)

(* ToDo: testing lemmata for receiver *)

lemma "tsRec\<cdot>\<bottom> = \<bottom>"
oops

lemma "tsRec\<cdot>tsRecExampInp = (tsRecExampOut_1, tsRecExampInp_2)"
oops

lemma 
  "tsRec\<cdot>(tsRecExampInp \<bullet> tsInfTick) = (tsRecExampOut_1 \<bullet> tsInfTick, tsRecExampInp_2 \<bullet> tsInfTick)"
oops
    
end