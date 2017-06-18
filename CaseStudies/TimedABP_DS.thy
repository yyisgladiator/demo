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

(* here I just try a few things *)

lemma tssnd_nbot [simp]: "msg\<noteq>\<bottom> \<Longrightarrow> acks\<noteq>\<bottom> \<Longrightarrow> tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr ack) \<noteq> \<bottom>"
  apply (induction msg arbitrary: acks ack)
  apply (simp_all)
  apply (simp add: tssnd_delayfun)
  apply (rule_tac ts=acks in tscases, auto)
  apply (simp add: tssnd_delayfun_nack)
  apply (case_tac "a\<noteq>ack", auto)
  oops

lemma h1: "adm (\<lambda>a. \<forall>x. x \<noteq> \<bottom> \<longrightarrow> (\<forall>xa. #\<surd> a \<le> #\<surd> tsSnd\<cdot>a\<cdot>x\<cdot>(Discr xa)))"
oops

(*
lemma tssnd_tstickcount: "acks\<noteq>\<bottom> \<Longrightarrow> #\<surd>msg \<le> #\<surd>(tsSnd\<cdot>msg\<cdot>acks\<cdot>(Discr ack))"
  apply (induction msg arbitrary: acks ack)
  apply (simp_all add: h1 tssnd_delayfun)
  apply (simp add: delayfun_insert)
  apply (rule_tac ts=acks in tscases, auto)
  apply (simp add: tssnd_delayfun_nack tstickcount_mlscons)
oops
*)

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