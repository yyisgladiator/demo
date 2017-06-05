(*  Title:        TimedABP.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory TimedABP
imports "../TStream_DS"

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* Medium *}
(* ----------------------------------------------------------------------- *)

definition tsMed :: "'a tstream \<rightarrow> bool stream \<rightarrow> 'a tstream" where
"tsMed \<equiv> \<Lambda> msg ora. tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"

(* Assumption for medium  lemmata: #({True} \<ominus> ora)=\<infinity> *)

lemma tsmed_insert: "tsMed\<cdot>msg\<cdot>ora = tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
by (simp add: tsMed_def)

(* ToDo: Properties lemmata for medium *)

(* Assumtions are missing. Add msg\<noteq>\<bottom> and ora\<noteq>\<bottom> as needed. *)
lemma tsmed_mlscons_true: "tsMed\<cdot>(tsMLscons\<cdot>m\<cdot>msg)\<cdot>((updis True) && ora) = tsMLscons\<cdot>m\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
oops
    
lemma tsmed_mlscons_false: "tsMed\<cdot>(tsMLscons\<cdot>m\<cdot>msg)\<cdot>((updis False) && ora) = tsMed\<cdot>msg\<cdot>ora"
oops

lemma tsmed_delayfun: "ora \<noteq>\<bottom> \<Longrightarrow> tsMed\<cdot>(delayFun\<cdot>msg)\<cdot>ora = delayFun\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
oops

text {* Not every message will be transmitted. *}    
lemma tsmed_slen_leq:
  shows "#(Rep_tstream (tsMed\<cdot>msg\<cdot>ora)) \<le> #(Rep_tstream msg)"
oops

text {* If infinity messages will be sent infinity messages will be transmitted. *}
lemma tsmed_slen [simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(tsAbs\<cdot>msg)=\<infinity>" 
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
oops

text {* If infinity ticks will be sent infinity ticks will be transmitted. *}
lemma tsmed_inftick [simp]: "#ora=\<infinity> \<Longrightarrow> tsMed\<cdot>tsInfTick\<cdot>ora = tsInfTick"
oops

text {* Medium without oracle will transmit all messages and ticks. *}
lemma tsmed_inftrue [simp]: "tsMed\<cdot>msg\<cdot>((\<up>True) \<infinity>) = msg"
oops

(* ToDo: More properties lemmata for medium, first show testings below *)

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
section {* Receiver *}
(* ----------------------------------------------------------------------- *)

definition tsRec :: "('a \<times> 'b) tstream \<rightarrow> ('b tstream \<times> 'a tstream)" where
"tsRec \<equiv> \<Lambda> dat. (tsProjSnd\<cdot>dat, tsProjFst\<cdot>(tsRemDups\<cdot>dat))"

(* ----------------------------------------------------------------------- *)
section {* Testing *}
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
subsection {* Medium *}
(* ----------------------------------------------------------------------- *)

text {* equivalence classes: empty tstream, finite tstream, infinite tstream *}

lift_definition OneTwoThree :: "nat tstream" is
  "<[Msg 1, \<surd>, Msg 2, \<surd>, Msg 3, \<surd>]>"
by (metis (no_types, lifting) assoc_sconc list2s.simps(1) list2s.simps(2) lscons_conv sup'_def
    ts_well_conc1 ts_well_sing_conc)

lemma "tsMed\<cdot>\<bottom>\<cdot>((\<up>True) \<infinity>) = \<bottom>"
by (simp add: tsmed_insert)

(* ToDo: Testing lemmata *)

lemma "tsMed\<cdot>OneTwoThree\<cdot>((\<up>True) \<infinity>) = OneTwoThree"
oops

lemma "tsMed\<cdot>OneTwoThree\<cdot>(<[True, False]> \<infinity>) = Abs_tstream (<[Msg 1, \<surd>, \<surd>, Msg 3, \<surd>]>)"
oops

lemma "tsMed\<cdot>(OneTwoThree \<bullet> tsInfTick)\<cdot>((\<up>True) \<infinity>) = (OneTwoThree \<bullet> tsInfTick)"
oops
    
end