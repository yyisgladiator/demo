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
  "tsSndExampOut = <[Msg (1, True), \<surd>, Msg (1, True), Msg (2, False), Msg (2, False), \<surd>, 
                     Msg (2, False), \<surd>, Msg (1, True), \<surd>]>\<surd>"

lemma tssnd_test_bot: "tsSnd_h\<cdot>\<bottom>\<cdot>tsInfTick = \<bottom>" 
  by (fixrec_simp)

lemma tssnd_test_fin:
  "tsSnd_h\<cdot>tsSndExampInp_1\<cdot>(tsSndExampInp_2 \<bullet>\<surd> tsInfTick)\<cdot>(Discr True) = tsSndExampOut"
  apply (simp add: tsSndExampInp_1_def tsSndExampInp_2_def tsSndExampOut_def tsconc_mlscons 
         tsconc_delayfun tssnd_h_mlscons_ack tssnd_h_mlscons_nack tssnd_h_delayfun_nack 
         tssnd_h_delayfun)
  apply (subst tsinftick_unfold)
  by (simp only: tssnd_h_delayfun, simp)    
    
lemma tssnd_test_inf:
  "tsSnd_h\<cdot>(tsSndExampInp_1 \<bullet>\<surd> tsInfTick)\<cdot>(tsSndExampInp_2 \<bullet>\<surd> tsInfTick)\<cdot>(Discr True) 
     = tsSndExampOut \<bullet>\<surd> tsInfTick"
  by (simp add: tsSndExampInp_1_def tsSndExampInp_2_def tsSndExampOut_def tsconc_mlscons 
      tsconc_delayfun tssnd_h_mlscons_ack tssnd_h_mlscons_nack tssnd_h_delayfun_nack 
      tssnd_h_delayfun tssnd_h_inftick_inftick)

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
  "tsMed\<cdot>(tsMedExampInp \<bullet>\<surd> tsInfTick)\<cdot>((\<up>True) \<infinity>) = (tsMedExampInp \<bullet>\<surd> tsInfTick)"
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

lemma tsrec_test_bot: "tsRec\<cdot>\<bottom> = \<bottom>"
  by simp

lemma tsrec_test_fin: "tsRec\<cdot>tsRecExampInp = (tsRecExampOut_1, tsRecExampOut_2)"
  by (simp add: tsRecExampInp_def tsRecExampOut_1_def tsRecExampOut_2_def tsrec_insert
      tsrecsnd_insert tsremdups_insert tsprojsnd_mlscons tsprojsnd_delayfun tsprojfst_mlscons 
      tsprojfst_delayfun tsremdups_h_mlscons tsremdups_h_mlscons_dup tsremdups_h_mlscons_ndup 
      tsremdups_h_delayfun)
  
lemma tsrec_test_inf2:
  "tsRec\<cdot>(tsRecExampInp \<bullet>\<surd> tsInfTick) = (tsRecExampOut_1 \<bullet>\<surd> tsInfTick, tsRecExampOut_2 \<bullet>\<surd> tsInfTick)"
  by (simp add: tsRecExampInp_def tsRecExampOut_1_def tsRecExampOut_2_def tsrec_insert 
      tsrecsnd_insert tsremdups_insert tsconc_mlscons tsconc_delayfun tsprojsnd_mlscons
      tsprojsnd_delayfun tsprojfst_mlscons tsprojfst_delayfun tsremdups_h_mlscons 
      tsremdups_h_mlscons_dup tsremdups_h_mlscons_ndup tsremdups_h_delayfun tsremdups_h_tsinftick)

(* ----------------------------------------------------------------------- *)
subsection {* composition *}
(* ----------------------------------------------------------------------- *)

(* ToDo: add definitions for oracles p1, p2 and input stream i to cover all possibilities *)

definition tsAltbitproExampInp :: "nat tstream" where
"tsAltbitproExampInp = <[Msg 1, Msg 2, \<surd>, Msg 1, \<surd>]>\<surd>"

definition tsAltbitproExampOra1 :: "bool stream" where
"tsAltbitproExampOra1 = <[True, True, False, True, True, True]>"

definition tsAltbitproExampOra2 :: "bool stream" where
"tsAltbitproExampOra2 = <[True, True, False, True, True]>"

(*case bot*)
lemma tsaltbitpro_test_bot:
  assumes ds_def: "ds = tsSnd\<cdot>\<bottom>\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>(<[True]> \<infinity>)"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    and as_def: "as = tsMed\<cdot>ar\<cdot>(<[True]> \<infinity>)"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>\<bottom>"
  by (simp add: dr_def ds_def as_def tssnd_insert tsremdups_insert tsremdups_h_delayfun 
      tsprojfst_delayfun)

(*case finite*)
lemma tsaltbitpro_test_fin:
  assumes ds_def: "ds = tsSnd\<cdot>tsAltbitproExampInp\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>(tsAltbitproExampOra1 \<bullet> tsAltbitproExampOra1 \<bullet> (tsAltbitproExampOra1\<infinity>))"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    and as_def: "as = tsMed\<cdot>ar\<cdot>(tsAltbitproExampOra2  \<bullet> tsAltbitproExampOra2 \<bullet>(tsAltbitproExampOra2\<infinity>))"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>tsAltbitproExampInp"
  apply(simp add: ds_def dr_def as_def tsAltbitproExampOra1_def tsAltbitproExampOra2_def tsAltbitproExampInp_def) 
  apply (subst ar_def)  
  apply(simp add: ds_def dr_def as_def tsAltbitproExampOra1_def tsAltbitproExampOra2_def tsAltbitproExampInp_def) 
  apply (subst ar_def)  
  apply(simp add: ds_def dr_def as_def tsAltbitproExampOra1_def tsAltbitproExampOra2_def tsAltbitproExampInp_def) 
  apply (subst ar_def)  
  apply(simp add: ds_def dr_def as_def tsAltbitproExampOra1_def tsAltbitproExampOra2_def tsAltbitproExampInp_def) 
  apply (subst ar_def)  
  apply(simp add: ds_def dr_def as_def tsAltbitproExampOra1_def tsAltbitproExampOra2_def tsAltbitproExampInp_def) 
  apply (subst ar_def)  
  apply(simp add: ds_def dr_def as_def tsAltbitproExampOra1_def tsAltbitproExampOra2_def tsAltbitproExampInp_def) 
  apply (subst ar_def)  
  apply(simp add: ds_def dr_def as_def tsAltbitproExampOra1_def tsAltbitproExampOra2_def tsAltbitproExampInp_def) 
  by(simp add: 
        tssnd_insert tssnd_h_delayfun_nack tssnd_h_delayfun_bot tssnd_h_mlscons_ack 
        tssnd_h_mlscons_nack tssnd_h_delayfun tssnd_h_delayfun_msg
        tsmed_mlscons_true tsmed_mlscons_false tsmed_delayfun
        tsremdups_insert tsremdups_h_mlscons tsremdups_h_mlscons_dup tsremdups_h_mlscons_ndup 
        tsremdups_h_delayfun
        tsprojsnd_mlscons tsprojsnd_delayfun tsprojfst_mlscons tsprojfst_delayfun tsabs_mlscons
        tsconc_mlscons tsconc_delayfun)


(*case infinite*)
lemma tsaltbitpro_test_inf:
  assumes ds_def: "ds = tsSnd\<cdot>(tsAltbitproExampInp \<bullet>\<surd> tsInfTick)\<cdot>as"
    and dr_def: "dr = tsMed\<cdot>ds\<cdot>(tsAltbitproExampOra1 \<infinity>)"
    and ar_def: "ar = tsProjSnd\<cdot>dr"
    and as_def: "as = tsMed\<cdot>ar\<cdot>(tsAltbitproExampOra2 \<infinity>)"
  shows "tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>dr)) = tsAbs\<cdot>(tsAltbitproExampInp \<bullet>\<surd> tsInfTick)"
  oops
    
end