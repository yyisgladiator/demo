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

lemma "#s=\<infinity> \<Longrightarrow> tsMed\<cdot>tsInfTick\<cdot>s = tsInfTick"
  oops
    
    
    
(* ----------------------------------------------------------------------- *)
section {* Receiver *}
(* ----------------------------------------------------------------------- *)

definition tsRec :: "('a \<times> 'b) tstream \<rightarrow> ('b tstream \<times> 'a tstream)" where
"tsRec \<equiv> \<Lambda> dat. (tsProjSnd\<cdot>dat, tsProjFst\<cdot>(tsRemDups\<cdot>dat))"











(* Test of the definitions *)

(* Med *)

lift_definition EinsZweiDrei :: "nat tstream " is
  "<[Msg 1, \<surd>, Msg 2, \<surd>, Msg 3, \<surd> ]>"
  by(simp add: ts_well_def)  
    
lemma "tsMed\<cdot>EinsZweiDrei\<cdot>\<bottom> = \<bottom>"
  oops
    
lemma "tsMed\<cdot>EinsZweiDrei\<cdot>((\<up>True) \<infinity>) = EinsZweiDrei"
  oops

lemma "tsMed\<cdot>EinsZweiDrei\<cdot>(<[True, False, True]>) = EinsZweiDrei" (* Es kommt nicht EinsZweiDrei raus.... anpassen*)
  oops

lemma "tsMed\<cdot>(EinsZweiDrei \<bullet> tsInfTick)\<cdot>((\<up>True) \<infinity>) = (EinsZweiDrei \<bullet> tsInfTick)"
  oops
    
  
end