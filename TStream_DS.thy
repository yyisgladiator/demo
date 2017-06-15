(*  Title:        TStream_DS.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Workspace for Development of Functions on Timed Streams
*)

theory TStream_DS
 
imports TStream

begin  
default_sort countable

(* here I just try a few things. *)

lemma tsabs_slen_adm [simp]: "adm (\<lambda>a. #(tsAbs\<cdot>(f\<cdot>a)) \<le> #(tsAbs\<cdot>a))"
oops

lemma tsremdups_h_tsabs_slen:
  "#(tsAbs\<cdot>(tsRemDups_h\<cdot>ts\<cdot>(Some (Discr t)))) \<le> #(tsAbs\<cdot>(tsRemDups_h\<cdot>ts\<cdot>None))"
apply (induction ts arbitrary: t)
apply (simp_all)
oops

lemma tsremdups_tsabs_slen [simp]: "#(tsAbs\<cdot>(tsRemDups\<cdot>ts)) \<le> #(tsAbs\<cdot>ts)"
apply (induction ts)
apply (simp_all)
apply (simp add: tsremdups_insert)
oops

lemma tszip_tsabs_slen_leq [simp]: "#(tsAbs\<cdot>(tsZip\<cdot>ts\<cdot>xs)) \<le> #(tsAbs\<cdot>ts)"
apply (induction ts)
apply (simp_all)
oops



lift_definition tsExampInp :: "nat tstream" is "<[Msg 1, Msg 2, \<surd>, Msg 2, \<surd>]>"
by (subst ts_well_def, auto)

lift_definition tsExampOut :: "nat tstream" is "<[Msg 1, Msg 2, \<surd>,  \<surd>]>"  
by (subst ts_well_def, auto)

lemma "tsRemDups\<cdot>tsExampInp = tsExampOut"
apply (simp add: tsExampInp_def tsExampOut_def tsremdups_insert)
using absts2mlscons2 absts2delayfun2 tsremdups_h_mlscons_dup tsremdups_h_mlscons_ndup
      tsremdups_h_strict tsremdups_h_mlscons tsremdups_h_delayfun
by (smt DiscrTick_def delayfun_nbot delayfun_tslscons_bot lscons_conv lscons_well msg_nwell
    n_not_Suc_n numeral_2_eq_2 strictI sup'_def tick_msg ts_well_sing_conc tslscons_bot2)

lift_definition tsExampInp2_1 :: "nat tstream" is "<[Msg 1, \<surd>, Msg 2, \<surd>]>"
by (subst ts_well_def, auto)

definition tsExampInp2_2 :: "bool stream" where 
"tsExampInp2_2 = <[True, False]>"

lift_definition tsExampOut2 :: "(nat \<times> bool) tstream" is "<[Msg (1, True), \<surd>, Msg (2, False), \<surd>]>"  
by (subst ts_well_def, auto)

lemma 
  "tsZip\<cdot>tsExampInp2_1\<cdot>tsExampInp2_2 = tsExampOut2"
apply (simp add: tsExampInp2_1_def tsExampInp2_2_def tsExampOut2_def)
using absts2mlscons2 absts2delayfun2 tszip_mlscons tszip_delayfun tszip_mlscons_2msg 
      tszip_mlscons_msgdelayfun tszip_mlscons_2msg_bot tszip_strict
proof -
  have f1: "Abs_tstream (\<up>(\<M> Suc 0) \<bullet> \<up>\<surd> \<bullet> \<up>(\<M> 2) \<bullet> \<up>\<surd>) 
              = tsMLscons\<cdot>(updis (Suc 0))\<cdot> (Abs_tstream (\<up>\<surd> \<bullet> \<up>(\<M> 2) \<bullet> \<up>\<surd>))"
    by (metis (no_types) absts2mlscons2 sconc_scons ts_well_conc1 ts_well_sing_conc)
  have f2: "\<up>True \<bullet> \<up>False = updis True && updis False && \<epsilon>"
    by (metis lscons_conv sup'_def)
  have f3: "tsZip\<cdot> (tsMLscons\<cdot>(updis (2::nat))\<cdot>(Abs_tstream (\<up>\<surd>)))\<cdot> (updis False && \<epsilon>) 
              = Abs_tstream (\<up>(\<M> (2, False)) \<bullet> \<up>\<surd>)"
    by (metis (no_types) Abs_tstream_strict absts2delayfun2 absts2mlscons2 lscons_conv sup'_def
        tick_msg ts_well_sing_conc tszip_mlscons_msgdelayfun tszip_strict(1))
  have "ts_well (\<up>(\<M> (Suc 0, True)) \<bullet> \<up>\<surd> \<bullet> \<up>(\<M> (2, False)) \<bullet> \<up>\<surd>)"
    by (metis (no_types) sconc_scons ts_well_conc1 ts_well_sing_conc)
  then show "tsZip\<cdot> (Abs_tstream (\<up>(\<M> Suc 0) \<bullet> \<up>\<surd> \<bullet> \<up>(\<M> 2) \<bullet> \<up>\<surd>))\<cdot> (\<up>True \<bullet> \<up>False) 
               = Abs_tstream (\<up>(\<M> (Suc 0, True)) \<bullet> \<up>\<surd> \<bullet> \<up>(\<M> (2, False)) \<bullet> \<up>\<surd>)"
    using f3 f2 f1 by (metis (no_types) absts2delayfun2 absts2mlscons2 tick_msg ts_well_conc1
                       ts_well_sing_conc tszip_mlscons_msgdelayfun)
qed

end  