(*  Title:        TimedABP.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory TimedABP
imports "../TStream_DS"

begin

(* ----------------------------------------------------------------------- *)
section {* Medium *}
(* ----------------------------------------------------------------------- *)

definition tsMed :: "('a::countable) tstream \<rightarrow> bool stream \<rightarrow> 'a tstream" where
"tsMed \<equiv> \<Lambda> msg ora. tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"

(* Assumption for lemmata: #({True} \<ominus> ora)=\<infinity> *)

(* ToDo: Description for lemmata *)

lemma tsmed_insert: "tsMed\<cdot>msg\<cdot>ora = tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
by (simp add: tsMed_def)

lemma tsmed_delayfun: "ora \<noteq> \<bottom>\<Longrightarrow> tsMed\<cdot>(delayFun\<cdot>ts)\<cdot>ora = delayFun\<cdot>(tsMed\<cdot>ts\<cdot>ora)"
  oops
    
    (* assumtions are missing. add them as needed. ts\<noteq>\<bottom> and ora\<noteq>\<bottom>*)
lemma tsmed_mlscons_true: "tsMed\<cdot>(tsMLscons\<cdot>t\<cdot>ts)\<cdot>((updis True) && ora) = tsMLscons\<cdot>t\<cdot>(tsMed\<cdot>ts\<cdot>ora)"
  oops
    
lemma tsmed_mlscons_false: "tsMed\<cdot>(tsMLscons\<cdot>t\<cdot>ts)\<cdot>((updis False) && ora) = tsMed\<cdot>ts\<cdot>ora"
  oops
    
lemma tsmed_slen_leq:
  shows "#(Rep_tstream (tsMed\<cdot>msg\<cdot>ora)) \<le> #(Rep_tstream msg)"
oops

text {* If infinity messages will be sent infinity messages will be transmitted. *}
lemma tsmed_slen[simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(tsAbs\<cdot>msg)=\<infinity>" 
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
oops

lemma tsmed_inftick [simp]: "#s=\<infinity> \<Longrightarrow> tsMed\<cdot>tsInfTick\<cdot>s = tsInfTick"
oops

lemma tsmed_trues [simp]: "tsMed\<cdot>ts\<cdot>((\<up>True) \<infinity>) = ts"
oops


(* Some more complicated stuff, first show the testings below *)

  (* You can reduce 2 mediums to one medium *)
lemma tsmeds2med: obtains o3 where "tsMed\<cdot>(tsMed\<cdot>ts\<cdot>o1)\<cdot>o2= tsMed\<cdot>ts\<cdot>o3"
  oops

lemma tsmed2infmed: assumes "#({True} \<ominus> o1)=\<infinity>" and "#({True} \<ominus> o2)=\<infinity>" 
    obtains o3 where "tsMed\<cdot>(tsMed\<cdot>ts\<cdot>o1)\<cdot>o2= tsMed\<cdot>ts\<cdot>o3" and "#({True} \<ominus> o3)=\<infinity>"
  oops    

lemma tsmed_map: "tsMed\<cdot>(tsMap f\<cdot>ts)\<cdot>oracle = tsMap f\<cdot>(tsMed\<cdot>ts\<cdot>oracle)"
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

(* ToDo: Lemmata for Testing the medium. Proof sketch for first lemma.
         Other lemmata analogously. Alternatively use tsMLscons representation *)

  (* SWS: these lemmata might be helpful to test the medium. Might...
lemma h1_f1: "tsZip\<cdot>(Abs_tstream (<[Msg 1, \<surd>, Msg 2, \<surd>, Msg 3, \<surd>]>))\<cdot>(\<up>True \<infinity>) 
           = Abs_tstream (<[Msg (1, True), \<surd>, Msg (2, True), \<surd>, Msg (3, True), \<surd>]>)"
oops

lemma h2_f1: 
  "tsFilter {x. snd x}\<cdot>(Abs_tstream (<[\<M> (1, True), \<surd>, \<M> (2, True), \<surd>, \<M> (3, True), \<surd>]>))
                    = (Abs_tstream (<[\<M> (1, True), \<surd>, \<M> (2, True), \<surd>, \<M> (3, True), \<surd>]>))"
oops

lemma h3_f1: "tsProjFst\<cdot>(Abs_tstream (<[\<M> (1, True), \<surd>, \<M> (2, True), \<surd>, \<M> (3, True), \<surd>]>)) 
                   = Abs_tstream (<[\<M> 1, \<surd>, \<M> 2, \<surd>, \<M> 3, \<surd>]>)"
oops
*)
lemma "tsMed\<cdot>OneTwoThree\<cdot>((\<up>True) \<infinity>) = OneTwoThree"
oops

lemma "tsMed\<cdot>OneTwoThree\<cdot>(<[True, False]> \<infinity>) = Abs_tstream (<[Msg 1, \<surd>, \<surd>, Msg 3, \<surd>]>)"
oops

lemma "tsMed\<cdot>(OneTwoThree \<bullet> tsInfTick)\<cdot>((\<up>True) \<infinity>) = (OneTwoThree \<bullet> tsInfTick)"
oops
    
end