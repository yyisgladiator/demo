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

definition sMed :: "'a stream \<rightarrow> bool stream \<rightarrow> 'a stream" where
"sMed \<equiv> \<Lambda> msg ora. sprojfst\<cdot>(sfilter {x. snd x}\<cdot>(szip\<cdot>msg\<cdot>ora))"

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
  
 
 (* SWS: Das ist mein vorschlag *)

lemma tsmed_tsabs [simp]: "#ora = \<infinity> \<Longrightarrow> tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora) = sMed\<cdot>(tsAbs\<cdot>msg)\<cdot>ora"
  apply(simp add: tsMed_def sMed_def)
  by(simp add: tsprojfst_tsabs tsfilter_tsabs tszip_tsabs)
    
lemma smed_t [simp]: "sMed\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>True \<bullet> ora) = \<up>a \<bullet> (sMed\<cdot>as\<cdot>ora)"
  by(simp add: sMed_def)
lemma smed_f [simp]: "sMed\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>False \<bullet> ora) = (sMed\<cdot>as\<cdot>ora)"
  by(simp add: sMed_def)    
lemma smed_bot1 [simp]: "sMed\<cdot>\<bottom>\<cdot>ora = \<bottom>"
  by(simp add: sMed_def)
lemma smed_bot2 [simp]: "sMed\<cdot>msg\<cdot>\<bottom> = \<bottom>"
  by(simp add: sMed_def)    
    
lemma smed_slen_inf [simp]: 
  shows "#msg=\<infinity> \<Longrightarrow> #(sMed\<cdot>msg\<cdot>ora) = #({True} \<ominus> ora)"
proof(induction ora arbitrary: msg rule:ind)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 a s)
  have h1: "a = True \<Longrightarrow> ?case"
    using "3.IH" "3.prems" inf_scase by force 
  have h2: "a = False \<Longrightarrow> ?case"
    using "3.IH" "3.prems" inf_scase by force      
  then show ?case using h1 h2 by blast
qed

lemma tsmed_tsabs_slen_inf [simp]: 
  assumes " #({True} \<ominus> ora) = \<infinity>"
      and "#(tsAbs\<cdot>msg)=\<infinity>"
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = #({True} \<ominus> ora)"
  using assms(1) assms(2) sfilterl4 by fastforce

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

lemma oracases:
  assumes bottom: "ts=\<bottom> \<Longrightarrow> P ts"
    and true: "\<And>as. ts= (\<up>True \<bullet> as) \<Longrightarrow> P ts"
    and false: "\<And>as. ts=(\<up>False \<bullet> as) \<Longrightarrow> P ts"
  shows "P ts"
  by (metis (full_types) bottom false scases true)  

lemma conc2cons: "\<up>a \<bullet>as = updis a && as"
  by (simp add: lscons_conv)    
    
lemma newora_f [simp]: "(newOracle\<cdot>(\<up>False \<bullet> ora1)\<cdot>(\<up>ora \<bullet> ora2)) = \<up>False \<bullet> newOracle\<cdot>ora1\<cdot>(\<up>ora \<bullet> ora2)"
by (simp add: conc2cons)

lemma newora_t [simp]: "(newOracle\<cdot>(\<up>True \<bullet> ora1)\<cdot>(\<up>ora \<bullet> ora2)) = \<up>ora \<bullet> newOracle\<cdot>ora1\<cdot>ora2"
by (simp add: conc2cons)
  
lemma newora_fair: assumes "#({True} \<ominus> ora1)=\<infinity>" and "#({True} \<ominus> ora2)=\<infinity>"
  shows "#({True} \<ominus> (newOracle\<cdot>ora1\<cdot>ora2))=\<infinity>"
  sorry
    
lemma smed2med: 
(*    assumes "#ora1 = \<infinity>" and "#ora2 = \<infinity>" *)
    shows "sMed\<cdot>(sMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = sMed\<cdot>msg\<cdot>(newOracle\<cdot>ora1\<cdot>ora2 )"
proof(induction msg arbitrary: ora1 ora2 rule: ind)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 a s)
  then show ?case 
  proof (cases rule: oracases [of ora1])
    case 1
    then show ?thesis by simp
  next
    case (2 as)
    then show ?thesis 
      by(cases rule: oracases [of ora2], auto simp add: "3.IH")
  next
    case (3 as)
    then show ?thesis       
      by(cases rule: oracases [of ora2], auto simp add: "3.IH")
  qed
qed

lemma tsmed_mlscons_false2 [simp]: "msg\<noteq>\<bottom> \<Longrightarrow> ora\<noteq>\<bottom>\<Longrightarrow> 
  tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(\<up>False \<bullet> ora) = tsMed\<cdot>msg\<cdot>ora"
  apply(simp add: tsmed_insert conc2cons)
  by (metis (full_types) mem_Collect_eq snd_conv tsfilter_mlscons_nin tsmlscons_bot2 tszip_mlscons)

lemma tsmed_mlscons_true2 [simp]: "msg\<noteq>\<bottom> \<Longrightarrow> ora\<noteq>\<bottom>\<Longrightarrow> 
  tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(\<up>True \<bullet> ora) = updis m &&\<surd> tsMed\<cdot>msg\<cdot>ora"
  apply(simp add: tsmed_insert conc2cons)
  by (metis (no_types, lifting) mem_Collect_eq snd_conv tsfilter_mlscons_in tsfilter_strict tsmlscons_bot2 tsprojfst_mlscons tsprojfst_strict tszip_mlscons)
  

    
text {* Two medium can be reduced to one medium. *}
lemma tsmed2med: "#ora1=\<infinity> \<Longrightarrow> #ora2=\<infinity> \<Longrightarrow> tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>(newOracle\<cdot>ora1\<cdot>ora2 )"
proof(induction msg arbitrary: ora1 ora2)
  case adm
  then show ?case by simp
next
  case bottom
  then show ?case by simp
next
  case (delayfun msg)
  then show ?case
    by (smt inf_scase lscons_conv newora_f newora_t stream.con_rews(2) tsmed_delayfun up_defined) 
next
  case (mlscons msg t)
  then show ?case 
  proof (cases rule: oracases [of ora1])
    case 1
    then show ?thesis by simp
  next
    case (2 as)
    then show ?thesis 
      apply(cases rule: oracases [of ora2], auto simp add: conc2cons "mlscons.IH" tsmed_mlscons_true tsmed_mlscons_false)
       apply (metis (no_types, lifting) fold_inf inject_lnsuc lscons_conv mlscons.IH mlscons.hyps mlscons.prems(1) mlscons.prems(2) slen_scons tsmed_mlscons_true2 tsmed_nbot tsmed_strict(2))
      by (metis (no_types, lifting) fold_inf inject_lnsuc lscons_conv mlscons.IH mlscons.hyps mlscons.prems(1) mlscons.prems(2) slen_scons tsmed_mlscons_false2 tsmed_mlscons_true tsmed_nbot tsmed_strict(2)) 
  next
    case (3 as)
    then show ?thesis       
      apply(cases rule: oracases [of ora2], auto simp add: conc2cons "mlscons.IH" tsmed_mlscons_true tsmed_mlscons_false)
      apply (metis (no_types, lifting) fold_inf inject_lnsuc lscons_conv mlscons.IH mlscons.hyps mlscons.prems(1) mlscons.prems(2) slen_scons tsmed_mlscons_false2 tsmed_nbot tsmed_strict(2))
      by (metis (no_types, lifting) fold_inf inject_lnsuc lscons_conv mlscons.IH mlscons.hyps mlscons.prems(1) mlscons.prems(2) slen_scons tsmed_mlscons_false2 tsmed_nbot tsmed_strict(2)) 
  qed
    
qed


text {* Two medium with fairness requirement can be reduced to one medium with 
        fairness requirement. *}
lemma tsmed2infmed: assumes "#({True} \<ominus> ora1)=\<infinity>" and "#({True} \<ominus> ora2)=\<infinity>" 
  obtains ora3 where "tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>ora3" and "#({True} \<ominus> ora3)=\<infinity>"
  by (meson assms(1) assms(2) newora_fair sfilterl4 tsmed2med)

    
end