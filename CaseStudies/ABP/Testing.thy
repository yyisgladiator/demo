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



(* just a few ideas *)
definition tsInfDelay :: "'a tstream" where "tsInfDelay = tsinftimes (delay \<bottom>)"

lemma tsinfdelay_unfold: "tsInfDelay = delay tsInfDelay"
  by (metis absts2delayfun_tick delayFun_def eta_cfun tsInfDelay_def tsinftimes_unfold)

lemma tsinftick_eq_tsinfdelay: "tsInfTick = tsInfDelay"
  apply (simp add: tsInfDelay_def tsInfTick_def)
  by (metis Rep_Abs absts2delayfun_tick s2sinftimes tick_msg tsconc_insert tsconc_rep_eq 
      tsinftimes_unfold)

lemma tsremdups_tsinftick: "tsRemDups\<cdot>tsInfTick = tsInfTick"
  by (metis delayfun2tsinftick tsremdups_h_delayfun tsremdups_insert)

lemma tsprojsnd_tsconc: "tsProjSnd\<cdot>(ts1 \<bullet> ts2) = tsProjSnd\<cdot>ts1 \<bullet> tsProjSnd\<cdot>ts2"
  by (simp add: tsprojsnd_insert tsmap_insert smap_split tsconc_insert tsmap_h_well)  
    
lemma tsprojfst_tsconc: "tsProjFst\<cdot>(ts1 \<bullet> ts2) = tsProjFst\<cdot>ts1 \<bullet> tsProjFst\<cdot>ts2"
  by (simp add: tsprojfst_insert tsmap_insert smap_split tsconc_insert tsmap_h_well)

lemma absts2mlscons3: "ts_well (\<up>(Msg m) \<bullet> (Rep_tstream ts)) \<Longrightarrow> 
  tsMLscons\<cdot>(updis m)\<cdot>ts = Abs_tstream (\<up>(Msg m) \<bullet> (Rep_tstream ts))"
  by (metis Abs_Rep absts2mlscons lscons_conv)

lemma h1:" ts_well (\<up>(\<M> (Suc 0,True)) \<bullet> Rep_tstream (updis (Suc 0, True) &&\<surd>
           delay (updis (Suc 0, True) &&\<surd> delay (updis (Suc 0, False) &&\<surd> delay \<bottom>))))"
  using delayfun_nbot sConc_fin_well tsmlscons_nbot up_defined by blast
    
lemma h2:"ts_well
     (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream (delay (updis (Suc 0, True) &&\<surd> delay (updis (Suc 0, False) &&\<surd> delay \<bottom>))))" 
  using delayfun_nbot sConc_fin_well tsmlscons_nbot up_defined by blast
    
lemma h3: "ts_well (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream (delay (updis (Suc 0, False) &&\<surd> delay \<bottom>)))"
  using delayfun_nbot sConc_fin_well tsmlscons_nbot up_defined by blast
    
lemma h4:"ts_well (\<up>(\<M> (Suc 0, False)) \<bullet> Rep_tstream (delay \<bottom>))"
  using delayfun_nbot sConc_fin_well tsmlscons_nbot up_defined by blast

lemma delayh: "ts_well s \<Longrightarrow> delayFun\<cdot>(Abs_tstream s) = Abs_tstream (\<up>\<surd> \<bullet> s)"
  by (simp add: absts2delayfun2)      
    
lemma h6: "tsProjFst\<cdot>(tsRemDups_h\<cdot>(Abs_tstream (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream (Abs_tstream
           (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream (delay (Abs_tstream (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream 
           (delay (Abs_tstream (\<up>(\<M> (Suc 0, False)) \<bullet> Rep_tstream (delay \<bottom>)))))))))) \<bullet> tsInfTick)\<cdot>None) = 
           tsProjFst\<cdot>(tsRemDups_h\<cdot>(Abs_tstream (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream (Abs_tstream
           (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream (delay (Abs_tstream (\<up>(\<M> (Suc 0, True)) \<bullet> Rep_tstream 
           (delay (Abs_tstream (\<up>(\<M> (Suc 0, False)) \<bullet> Rep_tstream (delay (\<bottom> \<bullet> tsInfTick))))))))))))\<cdot>None)"
  by (smt Rep_Abs absts2delayfun_tick absts2mlscons3 assoc_sconc delayfun_nbot delayh h1 sConc_fin_well sinftimes_unfold tick_msg tsInfTick.rep_eq ts_well_conc1 tsconc_fst_empty tsconc_insert tsinfdelay_unfold tsinftick_eq_tsinfdelay)

lemma h5: "tsRemDups_h\<cdot>tsInfTick\<cdot>(Some (Discr (Suc 0, False)))= tsInfTick"
  by (metis (no_types, lifting) Rep_tstream_inject delayFun.rep_eq s2sinftimes tick_msg tsInfTick.rep_eq tsconc_rep_eq tsinfdelay_unfold tsremdups_h_delayfun)

lemma h7: "tsRemDups_h\<cdot>(\<bottom> \<bullet> tsInfTick)\<cdot>(Some (Discr (Suc 0, False))) = \<bottom> \<bullet> tsInfTick"
  by (simp add: h5)    
    
declare sconc_fst_empty [simp del]  
declare tsconc_fst_empty [simp del]  
    
lemma tsrec_test_inf:
  "tsRec\<cdot>(tsRecExampInp \<bullet> tsInfTick) = (tsRecExampOut_1 \<bullet> tsInfTick, tsRecExampOut_2 \<bullet> tsInfTick)"
  apply (simp add: tsrec_insert tsRecExampInp_def tsRecExampOut_1_def tsRecExampOut_2_def)
  apply (simp add: tsprojsnd_tsconc tsprojsnd_mlscons tsprojsnd_delayfun)
  apply (simp add: tsrecsnd_insert  tsremdups_insert)   
     
  apply (subst absts2mlscons3) 
  apply (simp add: h1)
  apply (subst absts2mlscons3)
  apply (simp add: h2)
  apply (subst absts2mlscons3)
  apply (simp add: h3)
  apply (subst absts2mlscons3)
  apply (simp add: h4)
  apply (simp only: h6)
  apply (subst absts2mlscons2)
  apply (smt Rep_Abs Rep_tstream_strict delayFun.rep_eq delayfun_nbot inject_scons sConc_fin_well sconc_scons sconc_snd_empty tick_msg tsconc_rep_eq1)  
   apply (subst absts2mlscons2)
  using delayfun_nbot sConc_fin_well apply blast
    apply (subst absts2mlscons2)
  using delayfun_nbot sConc_fin_well apply blast
    apply (subst absts2mlscons2)
  using delayfun_nbot sConc_fin_well apply blast  
  apply (simp del: sconc_fst_empty  tsconc_fst_empty add: tsremdups_h_delayfun tsremdups_h_mlscons tsremdups_h_mlscons_dup
         tsremdups_h_mlscons_ndup Rep_tstream_inverse h7)
  apply (simp add: tsprojfst_tsconc tsprojfst_mlscons tsprojfst_delayfun)
   apply (subst  absts2mlscons3)
  using delayfun_nbot sConc_fin_well apply blast 
     apply (subst  absts2mlscons3)
  using delayfun_nbot sConc_fin_well apply blast 
     apply (subst  absts2mlscons3)
  using delayfun_nbot sConc_fin_well apply blast 
     apply (subst  absts2mlscons3)
  using delayfun_nbot sConc_fin_well apply blast
  by (smt Rep_Abs Rep_tstream_inject Rep_tstream_strict delayFun.rep_eq delayfun_nbot sConc_fin_well sconc_scons sconc_snd_empty tick_msg tsconc_fst_empty tsconc_rep_eq) 
    
end