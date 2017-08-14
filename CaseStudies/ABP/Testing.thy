(*  Title:        Testing.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Testing of the ABP components
*)

chapter {* Testing of the Alternating Bit Protocol components *}
                                                            
theory Testing
imports Medium Receiver Sender

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* testing *}
(* ----------------------------------------------------------------------- *)

text {* equivalence classes: empty tstream, finite tstream, infinite tstream *}

(* ----------------------------------------------------------------------- *)
subsection {* sender *}
(* ----------------------------------------------------------------------- *)

definition tsSndExampInp_1 :: "nat tstream" where
  "tsSndExampInp_1 = <[Msg 1, Msg 2, \<surd>, Msg 1, \<surd>]>\<surd>"

definition tsSndExampInp_2 :: "bool tstream" where
  "tsSndExampInp_2 = <[\<surd>, Msg True, Msg True, \<surd>, Msg False, \<surd>, Msg True, \<surd>]>\<surd>"

definition tsSndExampOut :: "(nat \<times> bool) tstream" where
  "tsSndExampOut = <[Msg (1, True), \<surd>,  Msg (2, False), Msg (2, False), \<surd>, \<surd>, Msg (1, True), \<surd>, \<surd>]>\<surd>"

(* ToDo: testing lemmata for sender *)

lemma tssnd_test_bot: "tsSnd\<cdot>\<bottom>\<cdot>tsInfTick = \<bottom>" 
  by (fixrec_simp)

lemma tssnd_test_fin: 
  "tsSnd\<cdot>tsSndExampInp_1\<cdot>(tsSndExampInp_2 \<bullet> tsInfTick)\<cdot>(Discr True) = tsSndExampOut"
  apply (simp add: tsSndExampInp_1_def tsSndExampInp_2_def tsSndExampOut_def)
  oops

lemma tssnd_test_inf:
  "tsSnd\<cdot>(tsSndExampInp_1 \<bullet> tsInfTick)\<cdot>(tsSndExampInp_2 \<bullet> tsInfTick)\<cdot>(Discr True) 
       = tsSndExampOut \<bullet> tsInfTick"
  apply (simp add: tsSndExampInp_1_def tsSndExampInp_2_def tsSndExampOut_def )
oops

(* ----------------------------------------------------------------------- *)
subsection {* medium *}
(* ----------------------------------------------------------------------- *)

definition tsMedExampInp :: "nat tstream" where
  "tsMedExampInp = <[Msg 1, \<surd>, Msg 2, \<surd>, Msg 3, \<surd>]>\<surd>"

definition tsMedExampOut :: "nat tstream" where
  "tsMedExampOut = <[Msg 1, \<surd>, \<surd>, Msg 3, \<surd>]>\<surd>"

lemma tsmed_test_bot: "tsMed\<cdot>\<bottom>\<cdot>((\<up>True) \<infinity>) = \<bottom>"
  by simp

lemma tsmed_test_fin: "tsMed\<cdot>tsMedExampInp\<cdot>((\<up>True) \<infinity>) = tsMedExampInp"
  by simp

lemma tsmed_test_fin2: "tsMed\<cdot>tsMedExampInp\<cdot>(<[True, False]> \<infinity>) = tsMedExampOut"
proof -
  have h1: "#(updis False && updis True && updis False && ((updis True && \<up>False)\<infinity>)) = \<infinity>"
    by (simp add: lscons_conv slen_sinftimes)
  have h2: "#(updis True && updis False && ((updis True && \<up>False)\<infinity>)) = \<infinity>"
    by (simp add: lscons_conv slen_sinftimes)
  have h3: "#(updis False && ((updis True && \<up>False)\<infinity>)) = \<infinity>"
    by (simp add: lscons_conv slen_sinftimes)  
  show "tsMed\<cdot>tsMedExampInp\<cdot>(<[True, False]> \<infinity>) = tsMedExampOut"    
    apply (simp add: tsMedExampInp_def tsMedExampOut_def)
    apply (subst sinftimes_unfold, subst sinftimes_unfold, auto)
    apply (fold lscons_conv)
    apply (simp add: h1 tsmed_mlscons_true tsmed_delayfun) 
    apply (simp add: h2 tsmed_mlscons_false tsmed_delayfun)
    by (simp add: h3 tsmed_mlscons_true tsmed_delayfun)
qed
  
lemma tsmed_test_inf:
  "tsMed\<cdot>(tsMedExampInp \<bullet> tsInfTick)\<cdot>((\<up>True) \<infinity>) = (tsMedExampInp \<bullet> tsInfTick)"
  by simp

(* ----------------------------------------------------------------------- *)
subsection {* receiver *}
(* ----------------------------------------------------------------------- *)

definition tsRecExampInp :: "(nat \<times> bool) tstream" where
  "tsRecExampInp = <[Msg (1, True), Msg (1, True), \<surd>, Msg (1, True), \<surd>, Msg (1, False), \<surd>]>\<surd>"

definition tsRecExampOut_1 :: "bool tstream" where
  "tsRecExampOut_1 = <[Msg True, Msg True, \<surd>, Msg True, \<surd>, Msg False, \<surd>]>\<surd>"

definition tsRecExampOut_2 :: "nat tstream" where
  "tsRecExampOut_2 = <[Msg 1, \<surd>, \<surd>, Msg 1, \<surd>]>\<surd>"

(* ToDo: testing lemmata for receiver *)

lemma tsrec_test_bot: "tsRec\<cdot>\<bottom> = \<bottom>"
  by simp

lemma tsrec_test_fin: "tsRec\<cdot>tsRecExampInp = (tsRecExampOut_1, tsRecExampOut_2)"
  by (simp add: tsrec_insert tsrecsnd_insert tsRecExampInp_def tsRecExampOut_1_def 
      tsRecExampOut_2_def tsprojsnd_delayfun tsprojsnd_mlscons tsprojfst_delayfun 
      tsprojfst_mlscons tsremdups_h_delayfun tsremdups_h_mlscons tsremdups_h_mlscons_dup 
      tsremdups_h_mlscons_ndup tsremdups_insert)  

lemma tsremdups_tsinftick: "tsRemDups\<cdot>tsInfTick = tsInfTick"
  by (metis delayfun2tsinftick tsremdups_h_delayfun tsremdups_insert)

lemma tsremdups_h_tsinftick: "tsRemDups_h\<cdot>tsInfTick\<cdot>t= tsInfTick"
  by (metis (no_types, lifting) delayfun2tsinftick delayfun_insert s2sinftimes tick_msg 
      tsconc_insert tsconc_rep_eq tsremdups_h_delayfun)

lemma tsprojsnd_tsconc: "tsProjSnd\<cdot>(ts1 \<bullet> ts2) = tsProjSnd\<cdot>ts1 \<bullet> tsProjSnd\<cdot>ts2"
  by (simp add: tsprojsnd_insert tsmap_insert smap_split tsconc_insert tsmap_h_well)  
    
lemma tsprojfst_tsconc: "tsProjFst\<cdot>(ts1 \<bullet> ts2) = tsProjFst\<cdot>ts1 \<bullet> tsProjFst\<cdot>ts2"
  by (simp add: tsprojfst_insert tsmap_insert smap_split tsconc_insert tsmap_h_well)

lemma mlscons2absts: "ts_well (\<up>(Msg t) \<bullet> Rep_tstream ts) \<Longrightarrow> 
  tsMLscons\<cdot>(updis t)\<cdot>ts = Abs_tstream (\<up>(Msg t) \<bullet> (Rep_tstream ts))"
  by (metis Abs_Rep absts2mlscons lscons_conv)

lemma delayfun2absts: "ts_well s \<Longrightarrow> delayFun\<cdot>(Abs_tstream s) = Abs_tstream (\<up>\<surd> \<bullet> s)"
  by (simp add: absts2delayfun2)

lemma tsrec_test_inf_h1: 
  "(Abs_tstream (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream (Abs_tstream
     (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream (delay (Abs_tstream (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream 
       (delay (Abs_tstream (\<up>(\<M> (Suc 0, False)) \<bullet> Rep_tstream (delay \<bottom>)))))))))) \<bullet> tsInfTick) = 
   (Abs_tstream (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream (Abs_tstream
     (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream (delay (Abs_tstream (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream 
        (delay (Abs_tstream (\<up>(\<M> (Suc 0, False)) \<bullet> Rep_tstream (delay (\<bottom> \<bullet> tsInfTick))))))))))))"
  by (smt Rep_Abs Rep_tstream_inject assoc_sconc delayfun_insert delayfun_nbot mlscons2absts 
      sConc_fin_well tick_msg tsconc_assoc tsconc_rep_eq tsmlscons_nbot up_defined)

lemma tsrec_test_inf_h2: "tsRemDups_h\<cdot>(\<bottom> \<bullet> tsInfTick)\<cdot>(Some (Discr (Suc 0, False))) = \<bottom> \<bullet> tsInfTick"
  by (simp add: tsremdups_h_tsinftick)
  
lemma tsrec_test_inf:
  "tsRec\<cdot>(tsRecExampInp \<bullet> tsInfTick) = (tsRecExampOut_1 \<bullet> tsInfTick, tsRecExampOut_2 \<bullet> tsInfTick)"
  apply (simp add: tsrec_insert tsRecExampInp_def tsRecExampOut_1_def tsRecExampOut_2_def)
  apply (simp add: tsprojsnd_tsconc tsprojsnd_mlscons tsprojsnd_delayfun)
  apply (simp add: tsrecsnd_insert tsremdups_insert)
  using delayfun_nbot sConc_fin_well tsmlscons_nbot up_defined
  apply (subst mlscons2absts, blast)+
  apply (simp only: tsrec_test_inf_h1)
  apply (subst absts2mlscons2)
  apply (smt mlscons2absts)
  apply (subst absts2mlscons2, blast)+
  apply (simp add: tsremdups_h_delayfun tsremdups_h_mlscons tsremdups_h_mlscons_dup
         tsremdups_h_mlscons_ndup tsremdups_h_tsinftick)
  apply (simp add: tsprojfst_tsconc tsprojfst_mlscons tsprojfst_delayfun)
  apply (subst mlscons2absts, smt delayfun_nbot)+
  by (smt Rep_tstream_inverse absts2delayfun_tick delayFun.rep_eq delayfun2tsinftick delayfun_nbot 
      lscons_conv sconc_scons' tick_msg ts_well_Rep tsconc_rep_eq1 tsmlscons_lscons2)

end