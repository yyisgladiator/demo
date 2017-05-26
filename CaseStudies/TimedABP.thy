(*  Title:        TimedABP.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory TimedABP
imports "../TStream"

begin

lemma tszip_strict[simp]: "tsZip\<cdot>\<bottom>\<cdot>\<epsilon> = \<bottom>"
sorry

lemma tszip_strict_fst[simp]: "tsZip\<cdot>\<bottom>\<cdot>s = \<bottom>"
sorry

lemma tszip_strict_snd[simp]: "tsZip\<cdot>ts\<cdot>\<epsilon> = \<bottom>"
sorry

(* ToDo: Vor der Verwendung durch sorry auf Korrektheit überprüfen *)
lemma tszip_scons_tick: "tsZip\<cdot>(Abs_tstream (\<up>\<surd>)\<bullet>ts)\<cdot>xs = Abs_tstream(\<up>\<surd>) \<bullet> tsZip\<cdot>ts\<cdot>xs"
oops

lemma tszip_scons: "t\<noteq>\<surd> \<Longrightarrow> ts_well (\<up>(\<M> (\<M>\<inverse> t,x)) \<bullet> Rep_tstream (tsZip\<cdot>ts\<cdot>xs)) 
  \<Longrightarrow> tsZip\<cdot>(Abs_tstream (\<up>t)\<bullet>ts)\<cdot>(\<up>x\<bullet>xs) = Abs_tstream(\<up>(\<M> (\<M>\<inverse> t,x)) \<bullet> Rep_tstream (tsZip\<cdot>ts\<cdot>xs))"
oops

(* ----------------------------------------------------------------------- *)
section {* Medium *}
(* ----------------------------------------------------------------------- *)

definition tsMed :: "'a tstream \<rightarrow> bool stream \<rightarrow> 'a tstream" where
"tsMed \<equiv> \<Lambda> msg ora. tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"

(* Assumption for lemmata: #({True} \<ominus> ora)=\<infinity> *)

(* ToDo: Description for lemmata *)

lemma tsmed_unfold: "tsMed\<cdot>msg\<cdot>ora = tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
by (simp add: tsMed_def)

lemma tsmed_slen_leq:
  shows "#(Rep_tstream (tsMed\<cdot>msg\<cdot>ora)) \<le> #(Rep_tstream msg)"
oops

text {* If infinity messages will be sent infinity messages will be transmitted. *}
lemma tsmed_slen[simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(tsAbs\<cdot>msg)=\<infinity>" 
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
oops

lemma "#s=\<infinity> \<Longrightarrow> tsMed\<cdot>tsInfTick\<cdot>s = tsInfTick"
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
by(simp add: ts_well_def)

lemma "tsMed\<cdot>OneTwoThree\<cdot>\<bottom> = \<bottom>"
oops
    
lemma "tsMed\<cdot>OneTwoThree\<cdot>((\<up>True) \<infinity>) = OneTwoThree"
oops

lemma "tsMed\<cdot>OneTwoThree\<cdot>(<[True, False, True]>) = Abs_tstream (<[Msg 1, \<surd>, \<surd>, Msg 3, \<surd>]>)" 
oops

lemma "tsMed\<cdot>(OneTwoThree \<bullet> tsInfTick)\<cdot>((\<up>True) \<infinity>) = (OneTwoThree \<bullet> tsInfTick)"
oops
    
end