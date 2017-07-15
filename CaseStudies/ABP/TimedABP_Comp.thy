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

type_synonym 'a sender = "('a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> ('a \<times> bool) tstream)"

definition tsSnd2Rec :: "'a sender \<rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsSnd2Rec \<equiv> \<Lambda> tssnd msg. snd (fix\<cdot>(\<Lambda> (acks, out). tsRec\<cdot>(delayFun\<cdot>(tssnd\<cdot>msg\<cdot>acks\<cdot>(Discr True)))))"

definition "tsSender = {tsSnd :: 'a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> ('a \<times> bool) tstream. 
  \<forall>i as ack. 
  tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack))) \<sqsubseteq> tsAbs\<cdot>i \<and> 
  tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack)))) 
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack))) \<and>
  #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack)))) 
    = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))) \<and>
  #(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack)) = \<infinity>
}"

lemma tssnd2rec_inp2out: assumes "tssnd \<in> tsSender"
  shows "tsAbs\<cdot>(tsSnd2Rec\<cdot>tssnd\<cdot>msg) = tsAbs\<cdot>msg"
  apply (simp add: tsSnd2Rec_def)
  oops
    
  (* goal lemma *)    
lemma assumes 
      "tssnd \<in> tsSender"
  and "ds = tssnd\<cdot>msg\<cdot>as\<cdot>ack"
  and "as = tsProjSnd\<cdot>ds"
  shows "tsAbs\<cdot>(tsRecSnd\<cdot>ds) = tsAbs\<cdot>msg"
  oops
    
    
end