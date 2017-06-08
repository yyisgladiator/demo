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

definition tsMed :: "'a tstream \<rightarrow> bool stream \<rightarrow> 'a tstream" where
"tsMed \<equiv> \<Lambda> msg ora. tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"

definition tsRecSnd :: "('a \<times> 'b) tstream \<rightarrow> 'a tstream" where
"tsRecSnd \<equiv> \<Lambda> dat. tsProjFst\<cdot>(tsRemDups\<cdot>dat)"

definition tsRec :: "('a \<times> 'b) tstream \<rightarrow> ('b tstream \<times> 'a tstream)" where
"tsRec \<equiv> \<Lambda> dat. (tsProjSnd\<cdot>dat, tsRecSnd\<cdot>dat)"

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

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

(* Assumptions are missing. Add msg\<noteq>\<bottom> and ora\<noteq>\<bottom> as needed. *)
lemma tsmed_mlscons_true: "tsMed\<cdot>(tsMLscons\<cdot>m\<cdot>msg)\<cdot>((updis True) && ora) = tsMLscons\<cdot>m\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
oops
    
lemma tsmed_mlscons_false: "tsMed\<cdot>(tsMLscons\<cdot>m\<cdot>msg)\<cdot>((updis False) && ora) = tsMed\<cdot>msg\<cdot>ora"
oops

lemma tsmed_delayfun: "ora\<noteq>\<bottom> \<Longrightarrow> tsMed\<cdot>(delayFun\<cdot>msg)\<cdot>ora = delayFun\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
oops
 
text {* If infinite ticks will be sent infinite ticks will be transmitted. *}
lemma tsmed_tstickcount [simp]: "#\<surd>(tsMed\<cdot>msg\<cdot>ora) = #\<surd>msg"
oops

text {* Not every message will be transmitted. *}    
lemma tsmed_slen_leq: "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) \<le> #(tsAbs\<cdot>msg)"
oops

text {* If infinite messages will be sent infinite messages will be transmitted. *}
lemma tsmed_slen [simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(tsAbs\<cdot>msg)=\<infinity>" 
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
oops

text {* If just infinite ticks will be sent just infinite ticks will be transmitted. *}
lemma tsmed_inftick [simp]: "#ora=\<infinity> \<Longrightarrow> tsMed\<cdot>tsInfTick\<cdot>ora = tsInfTick"
oops

text {* Medium without oracle will transmit all messages and ticks. *}
lemma tsmed_inftrue [simp]: "tsMed\<cdot>msg\<cdot>((\<up>True) \<infinity>) = msg"
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

lemma tsrecsnd_tstickcount [simp]: "#\<surd>(tsRecSnd\<cdot>dat) = #\<surd>dat"
oops

lemma tsrec_insert: "tsRec\<cdot>dat = (tsProjSnd\<cdot>dat, tsRecSnd\<cdot>dat)"
by (simp add: tsRec_def)

lemma tsrec_strict [simp]: "tsRec\<cdot>\<bottom> = \<bottom>"
oops

lemma tsrec_delayfun: "tsRec\<cdot>(delayFun\<cdot>dat) = (delayFun\<cdot>(tsProjSnd\<cdot>dat), delayFun\<cdot>(tsRecSnd\<cdot>dat))"
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
subsection {* medium *}
(* ----------------------------------------------------------------------- *)

lift_definition OneTwoThree :: "nat tstream" is
  "<[Msg 1, \<surd>, Msg 2, \<surd>, Msg 3, \<surd>]>"
by (subst ts_well_def, auto)

lemma "tsMed\<cdot>\<bottom>\<cdot>((\<up>True) \<infinity>) = \<bottom>"
by (simp add: tsmed_insert)

(* ToDo: testing lemmata for medium *)

lemma "tsMed\<cdot>OneTwoThree\<cdot>((\<up>True) \<infinity>) = OneTwoThree"
oops

lemma "tsMed\<cdot>OneTwoThree\<cdot>(<[True, False]> \<infinity>) = Abs_tstream (<[Msg 1, \<surd>, \<surd>, Msg 3, \<surd>]>)"
oops

lemma "tsMed\<cdot>(OneTwoThree \<bullet> tsInfTick)\<cdot>((\<up>True) \<infinity>) = (OneTwoThree \<bullet> tsInfTick)"
oops

(* ----------------------------------------------------------------------- *)
subsection {* receiver *}
(* ----------------------------------------------------------------------- *)

lift_definition OneTrue3OneFalse :: "(nat \<times> bool) tstream" is
  "<[Msg (1, True), Msg (1, True), \<surd>, Msg (1, True), \<surd>, Msg (1, False), \<surd>]>"
by (subst ts_well_def, auto)

lift_definition True3False :: "bool tstream" is
  "<[Msg True, Msg True, \<surd>, Msg True, \<surd>, Msg False, \<surd>]>"
by (subst ts_well_def, auto)

lift_definition OneOne :: "nat tstream" is
  "<[Msg 1, \<surd>, \<surd>, Msg 1, \<surd>]>"
by (subst ts_well_def, auto)

(* ToDo: testing lemmata for receiver *)

lemma "tsRec\<cdot>\<bottom> = \<bottom>"
oops

lemma "tsRec\<cdot>OneTrue3OneFalse = (True3False, OneOne)"
oops

lemma "tsRec\<cdot>(OneTrue3OneFalse \<bullet> tsInfTick) = (True3False \<bullet> tsInfTick, OneOne \<bullet> tsInfTick)"
oops
    
end