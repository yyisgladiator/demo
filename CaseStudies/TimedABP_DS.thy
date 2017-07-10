(*  Title:        TimedABP_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Workspace for the Definition of Alternating Bit Protocol on Timed Streams
*)

chapter {* Alternating Bit Protocol *}       
                                                            
theory TimedABP_DS
imports TimedABP

begin
default_sort countable

definition "tsSender = {tsSnd :: 'a tstream \<rightarrow> bool tstream \<rightarrow> bool discr \<rightarrow> ('a \<times> bool) tstream. 
  \<forall>i as ack. 
  tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack))) \<sqsubseteq> tsAbs\<cdot>i \<and> 
  tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack)))) 
    = tsAbs\<cdot>(tsProjSnd\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack))) \<and>
  #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack)))) 
    = min (#(tsAbs\<cdot>i)) (lnsuc\<cdot>(#(tsAbs\<cdot>(tsRemDups\<cdot>as)))) \<and>
  #(tsAbs\<cdot>i) > #(tsAbs\<cdot>(tsRemDups\<cdot>as)) \<longrightarrow> #(tsAbs\<cdot>(tsSnd\<cdot>i\<cdot>as\<cdot>ack)) = \<infinity>
}"

lemma tssender_exists: "\<exists>tsSnd. tsSnd \<in> tsSender"
sorry

definition "tsReceiver = {tsRec :: ('a \<times> 'b) tstream \<rightarrow> ('b tstream \<times> 'a tstream).
  tsRec\<cdot>\<bottom> = \<bottom>
}"

lemma tsreceiver_exists: "\<exists>tsRec. tsRec \<in> tsReceiver"
sorry

lemma inp2out: assumes "tssnd \<in> tsSender" and "tsrec \<in> tsReceiver"
  shows "(\<Lambda> msg. snd (fix\<cdot>(\<Lambda> (acks, m). tsrec\<cdot>(tssnd\<cdot>msg\<cdot>acks\<cdot>(Discr True)))))\<cdot>msg = msg"
oops

(* here I just try a few things *)

(* simple test for sender *)

lift_definition tsExampInp_1 :: "nat tstream" is
  "<[Msg 1, Msg 2, \<surd>, Msg 1, \<surd>]>"
by (subst ts_well_def, auto)

lemma tsexampinp_12mlscons:
  "tsExampInp_1 = tsMLscons\<cdot>(updis 1)\<cdot>(tsMLscons\<cdot>(updis 2)\<cdot>
                     (delayFun\<cdot>(tsMLscons\<cdot>(updis 1)\<cdot>(delayFun\<cdot>\<bottom>))))"
apply (simp add: tsExampInp_1_def)
by (metis (no_types, lifting) One_nat_def absts2delayfun2 absts2delayfun_tick absts2mlscons2 
    list2s.simps(1) list2s.simps(2) lscons_conv sconc_scons sup'_def tick_msg tsExampInp_1.rep_eq
    ts_well_Rep ts_well_conc1 ts_well_sing_conc)

lift_definition tsExampInp_2 :: "bool tstream" is
  "<[\<surd>, Msg True, Msg True, \<surd>, Msg False, \<surd>, Msg True, \<surd>]>"
by (subst ts_well_def, auto)

lemma tsexampinp_22mlscons:
  "tsExampInp_2 = delayFun\<cdot>(tsMLscons\<cdot>(updis True)\<cdot>(tsMLscons\<cdot>(updis True)\<cdot>
                    (delayFun\<cdot>(tsMLscons\<cdot>(updis False)\<cdot>(delayFun\<cdot>
                       (tsMLscons\<cdot>(updis True)\<cdot>(delayFun\<cdot>\<bottom>)))))))"
apply (simp add: tsExampInp_2_def)
by (metis (no_types, lifting) Rep_Abs absts2mlscons2 delayfun_abststream delayfun_nbot
    lscons_conv sConc_fin_well absts2delayfun_tick ts_well_sing_conc tsmlscons_nbot up_defined)

lift_definition tsExampOut :: "(nat \<times> bool) tstream" is
  "<[Msg (1, True), \<surd>,  Msg (2, False), Msg (2, False), \<surd>, \<surd>, Msg (1, True), \<surd>, \<surd>]>"
by (subst ts_well_def, auto)

lemma "tsSnd\<cdot>tsExampInp_1\<cdot>tsExampInp_2\<cdot>(Discr True) = tsExampOut"
apply (simp add: tsExampOut_def tsexampinp_12mlscons tsexampinp_22mlscons)
apply (simp add: tssnd_delayfun_nack tssnd_mlscons_ack tssnd_mlscons_nack 
                 tssnd_delayfun)
by (smt Rep_Abs absts2delayfun2 absts2delayfun_tick absts2mlscons2 delayfun_nbot sConc_fin_well
    tick_msg tsmlscons_nbot up_defined)

end