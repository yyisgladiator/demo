(*  Title:        TimedABP.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory TimedABP_Comp
imports "../TimedABP"

begin
default_sort countable

type_synonym 'a sender = "('a tstream \<rightarrow> bool tstream  \<rightarrow> ('a \<times> bool) tstream)"

definition tsSnd2Rec :: "'a sender \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsSnd2Rec \<equiv> \<Lambda> tssnd msg. snd (fix\<cdot>(\<Lambda> (acks, out). tsRec\<cdot>(delayFun\<cdot>(tssnd\<cdot>msg\<cdot>acks))))"

definition tsSender :: "('a sender) set" where
"tsSender = {tsSnd :: 'a tstream \<rightarrow> bool tstream \<rightarrow> ('a \<times> bool) tstream. 
  \<forall>i as. 
  tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i \<and> 
  tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as)))) 
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as))) \<and>
  #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as)))) 
    = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))) \<and>
  (#(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(tsSnd\<cdot>i\<cdot>as)) = \<infinity>)
}"

lemma tssnd2rec_inp2out: assumes "tssnd \<in> tsSender"
  shows "tsAbs\<cdot>(tsSnd2Rec\<cdot>tssnd\<cdot>msg) = tsAbs\<cdot>msg"
  apply (simp add: tsSnd2Rec_def)
  oops

    (* TADA *)
lemma 
  fixes send:: "'a sender"
  assumes "send\<in>tsSender"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(send\<cdot>i\<cdot>as))) \<sqsubseteq> tsAbs\<cdot>i"
  using assms tsSender_def by auto

  (* goal lemma *)    
lemma assumes 
      "tssnd \<in> tsSender"
  and "ds = tssnd\<cdot>msg\<cdot>as"
  and "as = tsProjSnd\<cdot>ds"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>msg"
  oops

    
    
    
(* stuff with medium *)



  (* goal lemma *)    
lemma assumes 
      "tssnd \<in> tsSender"
  and "#({True} \<ominus> ora1)=\<infinity>"
  and "#({True} \<ominus> ora2)=\<infinity>"
  
  and "ds = tssnd\<cdot>msg\<cdot>as\<cdot>ack"
  and "dr = tsMed\<cdot>ds\<cdot>ora1"
  and "ar = tsProjSnd\<cdot>dr"
  and "as = tsMed\<cdot>ar\<cdot>ora2"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>dr) = tsAbs\<cdot>msg"
  oops
    
end