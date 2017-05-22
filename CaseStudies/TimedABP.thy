(*  Title:        TimedABP.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory TimedABP
imports "../TStream"

begin

(* ----------------------------------------------------------------------- *)
section {* Medium *}
(* ----------------------------------------------------------------------- *)

definition tsMed :: "'a tstream \<rightarrow> bool stream \<rightarrow> 'a tstream" where
"tsMed \<equiv> \<Lambda> msg ora. tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"

(* Assumption for lemmata: #({True} \<ominus> ora)=\<infinity> *)

lemma tsmed_unfold: "tsMed\<cdot>msg\<cdot>ora = tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
by (simp add: tsMed_def)

lemma tsmed_slen_leq: assumes "#({True} \<ominus> ora)=\<infinity>"
  shows "#(Rep_tstream (tsMed\<cdot>msg\<cdot>ora)) \<le> #(Rep_tstream msg)"
oops
  
lemma tsmed_slen[simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(Rep_tstream msg)=\<infinity>" 
  shows "#(Rep_tstream (tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
oops

(* ----------------------------------------------------------------------- *)
section {* Receiver *}
(* ----------------------------------------------------------------------- *)

definition tsRec :: "('a \<times> 'b) tstream \<rightarrow> ('b tstream \<times> 'a tstream)" where
"tsRec \<equiv> \<Lambda> dat. (tsProjSnd\<cdot>dat, tsProjFst\<cdot>(tsRemDups\<cdot>dat))"

end