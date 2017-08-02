(*  Title:        Medium.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Medium Component of the ABP on Timed Streams
*)

chapter {* Medium of the Alternating Bit Protocol *}
                                                            
theory Medium
imports "../../TStream"

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition *}
(* ----------------------------------------------------------------------- *)

definition tsMed :: "'a tstream \<rightarrow> bool stream \<rightarrow> 'a tstream" where
"tsMed \<equiv> \<Lambda> msg ora. tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"

definition tsMeds :: "('a tstream \<rightarrow> 'a tstream) set" where
"tsMeds \<equiv> { (\<Lambda> ts. tsMed\<cdot>ts\<cdot>ora) | ora. #({True} \<ominus> ora)=\<infinity> }"

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

  
fixrec newOracle :: "bool stream \<rightarrow> bool stream \<rightarrow> bool stream" where
"newOracle\<cdot>\<bottom>\<cdot>bs = \<bottom> " |
"newOracle\<cdot>as\<cdot>\<bottom> = \<bottom> " |
"newOracle\<cdot>((up\<cdot>a)&&as)\<cdot>((up\<cdot>b)&&bs) = 
  (* First oracle is not transmitting the message *)
  (if(a = Discr False) then (updis False)&&newOracle\<cdot>as\<cdot>((up\<cdot>b)&&bs)
  
  (* First oracle is transmitting *)
   else  up\<cdot>b && newOracle\<cdot>as\<cdot>bs)"

(* Testing that it works *)
lemma "newOracle\<cdot>(<[True, True, False, True]>)\<cdot>(<[True, False, True]>) = <[True, False, False, True]>"
apply (simp only: list2s_0 list2s_Suc)
  by fixrec_simp

text {* Assumption for medium lemmata: #({True} \<ominus> ora)=\<infinity> *}

lemma tsmed_insert: "tsMed\<cdot>msg\<cdot>ora = tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
  by (simp add: tsMed_def)

lemma tsmed_strict [simp]: 
  "tsMed\<cdot>\<bottom>\<cdot>\<epsilon> = \<bottom>"
  "tsMed\<cdot>msg\<cdot>\<epsilon> = \<bottom>"
  "tsMed\<cdot>\<bottom>\<cdot>ora = \<bottom>"
  by (simp add: tsMed_def)+

lemma tsmed_mlscons_true: "msg\<noteq>\<bottom> \<Longrightarrow> #ora=\<infinity> \<Longrightarrow> 
  tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>((updis True) && ora) = tsMLscons\<cdot>(updis m)\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
  apply (simp add: tsmed_insert)
  by (metis Inf'_neq_0 mem_Collect_eq prod.sel(2) slen_empty_eq tsfilter_mlscons_in
      tsfilter_nbot tsprojfst_mlscons tszip_mlscons tszip_nbot)

lemma tsmed_mlscons_false: "msg\<noteq>\<bottom> \<Longrightarrow> #ora=\<infinity> \<Longrightarrow> 
  tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>((updis False) && ora) = tsMed\<cdot>msg\<cdot>ora"
  apply (simp add: tsmed_insert)
  by (metis Inf'_neq_0 mem_Collect_eq prod.sel(2) slen_empty_eq tsfilter_mlscons_nin
      tszip_mlscons tszip_nbot)

lemma tsmed_delayfun: "ora\<noteq>\<epsilon> \<Longrightarrow> tsMed\<cdot>(delayFun\<cdot>msg)\<cdot>ora = delayFun\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
  by (simp add: tsMed_def tszip_delayfun tsfilter_delayfun tsprojfst_delayfun)

(* ToDo: basic properties lemmata for medium *)

lemma tsmed_nbot [simp]: "msg\<noteq>\<bottom> \<Longrightarrow> #ora=\<infinity> \<Longrightarrow> tsMed\<cdot>msg\<cdot>ora \<noteq> \<bottom>"
 by (simp add: tsmed_insert)

text {* If infinite ticks will be sent infinite ticks will be transmitted. *}
lemma tsmed_tstickcount [simp]: "#ora=\<infinity> \<Longrightarrow> #\<surd>(tsMed\<cdot>msg\<cdot>ora) = #\<surd>msg"
  by (simp add: tsmed_insert)

text {* If just infinite ticks will be sent just infinite ticks will be transmitted. *}
lemma tsmed_inftick [simp]: "#ora=\<infinity> \<Longrightarrow> tsMed\<cdot>tsInfTick\<cdot>ora = tsInfTick"
  apply (simp add: tsmed_insert tsInfTick_def tsfilter_insert)
  by (metis (no_types, lifting)
      Inf'_neq_0 Rep_tstream_inject delayfun_insert insertI1 s2sinftimes sfilter_in
      sinftimes_unfold slen_empty_eq tick_msg tsInfTick.abs_eq tsInfTick.rep_eq
      tsconc_rep_eq tsprojfst_delayfun tszip_delayfun)

(* ToDo Steffen: basic properties lemmata for medium *)

text {* Medium without oracle will transmit all messages and ticks. *}
lemma tsmed_inftrue [simp]: "tsMed\<cdot>msg\<cdot>((\<up>True) \<infinity>) = msg"
  apply(simp add: tsmed_insert)
  apply (induction msg)
  apply (simp_all)
  apply (metis lscons_conv sinftimes_unfold stream.con_rews(2)
         tsmed_delayfun tsmed_insert up_defined)
  by (metis lscons_conv sinftimes_unfold slen_sinftimes strict_icycle
      tsmed_insert tsmed_mlscons_true tsmed_strict(2))


text {* Not every message will be transmitted. *}    
lemma tsmed_tsabs_slen: "#ora=\<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) \<le> #(tsAbs\<cdot>msg)"
  apply (simp add: tsmed_insert)
  by (metis tsfilter_tsabs_slen tszip_tsabs_slen)

(* ToDo Steffen: basic properties lemmata for medium *)


 lemma tsmed_map: "#ora=\<infinity> \<Longrightarrow> tsMed\<cdot>(tsMap f\<cdot>msg)\<cdot>ora = tsMap f\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
  apply(induct msg arbitrary: ora, auto)
  apply (metis tsmap_delayfun tsmed_delayfun tsmed_strict(2))
  apply(rule_tac x=ora in scases, simp_all)
  apply(rename_tac y x )
  apply (case_tac "y=True", simp_all)
  apply (metis (no_types, lifting) lscons_conv tsmap_mlscons tsmap_nbot 
          tsmed_mlscons_true tsmed_nbot)
  by (metis lscons_conv tsmap_mlscons tsmap_nbot tsmed_mlscons_false)

    

   



lemma h3:" #ora=\<infinity> \<Longrightarrow>  #(tsAbs\<cdot>msg) = \<infinity> \<Longrightarrow>  #(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = #({True} \<ominus> ora) \<Longrightarrow>
           #(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(\<up>True \<bullet> ora))) = #({True} \<ominus> \<up>True \<bullet> ora)"
  by (metis (no_types, lifting) Inf'_neq_0 lscons_conv sfilter_in singletonI slen_empty_eq
      slen_updis_eq tsabs_bot tsabs_mlscons tsmed_mlscons_true tsmed_nbot)

lemma h4:" #ora=\<infinity> \<Longrightarrow>  #(tsAbs\<cdot>msg) = \<infinity> \<Longrightarrow>  #(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = #({True} \<ominus> ora) \<Longrightarrow>
           #(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(\<up>False \<bullet> ora))) = #({True} \<ominus> \<up>False  \<bullet> ora)"
  by (metis Inf'_neq_0 lscons_conv sfilter_nin singletonD
       slen_empty_eq tsabs_bot tsmed_mlscons_false)
       
lemma h5: "#ora=\<infinity> \<Longrightarrow>  #(tsAbs\<cdot>msg) = \<infinity> \<Longrightarrow>   #(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = #({True} \<ominus> ora) \<Longrightarrow>
           #(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(\<up>a \<bullet> ora))) = #({True} \<ominus> \<up>a \<bullet> ora)"
  by (metis h3 h4)
  

    


lemma tsmed_tsabs_slen_inf_h: 
   "#ora=\<infinity> \<Longrightarrow> #(tsAbs\<cdot>msg)=\<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = #({True} \<ominus> ora)"
proof(induction msg arbitrary: ora)
  
  case adm
  then  show ?case   
    apply(rule adm_all)
    apply(rule adm_imp)
    apply simp

     
   sorry    
  next
    case bottom
    then show ?case 
      by simp
  next
    case (delayfun msg)
    then show ?case 
     by (metis Inf'_neq_0 slen_empty_eq tsabs_delayfun tsmed_delayfun)
  next
    case (mlscons msg t)
    then show ?case 
    proof (rule_tac x=ora in scases, simp_all)
      fix a:: "bool"
      fix s:: "bool stream"
      show "\<And>a s. #s = \<infinity> \<Longrightarrow>
           ora = \<up>a \<bullet> s \<Longrightarrow>
           (\<And>ora. #ora = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>msg) = \<infinity> \<Longrightarrow> #(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = #({True} \<ominus> ora)) \<Longrightarrow>
           msg \<noteq> \<bottom> \<Longrightarrow> 
           #(tsAbs\<cdot>(updis t &&\<surd> msg)) = \<infinity> \<Longrightarrow> 
           #(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(\<up>a \<bullet> s))) = #({True} \<ominus> \<up>a \<bullet> s)" 
     by (simp add: h5 lscons_conv tsabs_mlscons)
       
    qed
  qed

    
text {* If infinite messages will be sent infinite messages will be transmitted. *}
lemma tsmed_tsabs_slen_inf [simp]: assumes "#({True} \<ominus> ora)=\<infinity>" and "#(tsAbs\<cdot>msg)=\<infinity>" 
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
proof -
   have transform:"#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) =  #(Collect snd \<ominus> tsAbs\<cdot>(tsZip\<cdot>msg\<cdot>ora)) " 
     by (simp add: tsfilter_tsabs tsmed_insert)
   hence "#({True} \<ominus> ora)=\<infinity> \<Longrightarrow> #(tsAbs\<cdot>msg)=\<infinity> \<Longrightarrow> #(Collect snd \<ominus> tsAbs\<cdot>(tsZip\<cdot>msg\<cdot>ora)) = \<infinity> "
     using sfilterl4 tsmed_tsabs_slen_inf_h by fastforce
   then show ?thesis
     by (simp add: assms(1) assms(2) transform)
qed
    
    
 
(*
lemma szip_collect_inf_h: assumes "#s=\<infinity>" shows  "#(Collect snd \<ominus> s) = \<infinity>" 
  sorry
    
lemma szip_collect_inf: assumes "#ora=\<infinity>" and "#msg=\<infinity>"
  shows "#(Collect snd \<ominus> szip\<cdot>msg\<cdot>ora) = \<infinity>"
  by (simp add: assms(1) assms(2) szip_collect_inf_h)
*)
    


lemma tsmed_tsdom: "#ora=\<infinity> \<Longrightarrow> tsDom\<cdot>(tsMed\<cdot>msg\<cdot>ora) \<subseteq> tsDom\<cdot>msg"
proof(induction msg arbitrary: ora)
 case adm
   then show ?case 
     apply (rule admI)
     by (simp add: contlub_cfun_arg contlub_cfun_fun lub_eq_Union SUP_subset_mono)
 next
   case bottom
   then show ?case 
     by simp
 next
   case (delayfun msg)
   then show ?case 
     by (metis Inf'_neq_0 strict_slen tsdom_delayfun tsmed_delayfun)
 next
  case (mlscons msg t)
  then show ?case 
  proof -
    
  have lscons_conv_for_True: "\<up>True \<bullet> ora= (updis True) && ora"
    by(simp add:lscons_conv)  
  hence tsmed_mlscons_true_less_assms: "#ora=\<infinity>  \<Longrightarrow> tsMed\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>msg)\<cdot>(\<up>True \<bullet> ora) 
                                                     = tsMLscons\<cdot>(updis t)\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
    using tsmed_mlscons_true by force
      
  (* can I user scases somehow here?*)
  have ora_split: "ora = \<up>(shd ora) \<bullet> srt\<cdot>ora \<and> #(srt\<cdot>ora) = \<infinity>"
    by (metis Inf'_neq_0 fold_inf inject_lnsuc mlscons.prems 
        slen_empty_eq srt_decrements_length surj_scons)    
  have tsdom_ora_srt: "tsDom\<cdot>(tsMed\<cdot>msg\<cdot>(srt\<cdot>ora)) \<subseteq> {t} \<union> tsDom\<cdot>msg"
    by (metis Inf'_neq_0 fold_inf inject_lnsuc mlscons.IH 
        mlscons.prems slen_empty_eq srt_decrements_length sup.coboundedI2)
      
  { 
    assume "({t} \<union> tsDom\<cdot>(tsMed\<cdot>msg\<cdot>(srt\<cdot>ora)) \<subseteq> {t} \<union> tsDom\<cdot>msg) \<noteq>
            (tsDom\<cdot>(tsMed\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>msg)\<cdot>ora) \<subseteq> tsDom\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>msg))"
      
    then have "{t} \<union> tsDom\<cdot>(tsMed\<cdot>msg\<cdot>(srt\<cdot>ora)) \<noteq> tsDom\<cdot>(tsMed\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>msg)\<cdot>ora)"
      using mlscons.hyps tsdom_mlscons by fastforce    
    then have "\<up>True \<bullet> srt\<cdot>ora \<noteq> ora"
      by (metis ora_split lscons_conv mlscons.hyps tsdom_mlscons tsmed_mlscons_true tsmed_nbot)        
    then have ?thesis 
      by (metis (full_types) ora_split tsdom_ora_srt lscons_conv 
          mlscons.hyps tsdom_mlscons tsmed_mlscons_false) }
    
  then show ?thesis
    using tsdom_ora_srt by auto
  qed
qed


(* ----------------------------------------------------------------------- *)
section {* additional properties *}
(* ----------------------------------------------------------------------- *)

(* ToDo: additional properties lemmata for medium *)

text {* Two medium can be reduced to one medium. *}
lemma tsmed2med: "tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>(newOracle\<cdot>ora1\<cdot>ora2 )"
oops

text {* Two medium with fairness requirement can be reduced to one medium with 
        fairness requirement. *}
lemma tsmed2infmed: assumes "#({True} \<ominus> ora1)=\<infinity>" and "#({True} \<ominus> ora2)=\<infinity>" 
  obtains ora3 where "tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>ora3" and "#({True} \<ominus> ora3)=\<infinity>"
oops    
    
end