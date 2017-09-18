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

definition tsMedium :: "('a tstream \<rightarrow> 'a tstream) set" where
"tsMedium \<equiv> { (\<Lambda> ts. tsMed\<cdot>ts\<cdot>ora) | ora. #({True} \<ominus> ora) = \<infinity> }"

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
lemma 
  "newOracle\<cdot>(<[True, True, False, True]>)\<cdot>(<[True, False, True]>) = <[True, False, False, True]>"
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
lemma tsmed_tstickcount [simp]: "#ora = \<infinity> \<Longrightarrow> #\<surd>(tsMed\<cdot>msg\<cdot>ora) = #\<surd>msg"
  by (simp add: tsmed_insert)

text {* If just infinite ticks will be sent just infinite ticks will be transmitted. *}
lemma tsmed_tsinftick [simp]: "#ora=\<infinity> \<Longrightarrow> tsMed\<cdot>tsInfTick\<cdot>ora = tsInfTick"
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


lemma tsmed_tsmap: 
  "#ora=\<infinity> \<Longrightarrow> tsMed\<cdot>(tsMap f\<cdot>msg)\<cdot>ora = tsMap f\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
  apply (induct msg arbitrary: ora, auto)
  apply (metis tsmap_delayfun tsmed_delayfun tsmed_strict(2))
  apply (rule_tac x=ora in scases, simp_all)
  apply (rename_tac y x)
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

lemma tsmed_tsabs: "#ora = \<infinity> \<Longrightarrow> tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora) = sMed\<cdot>(tsAbs\<cdot>msg)\<cdot>ora"
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
  assumes "#({True} \<ominus> ora) = \<infinity>" and "#(tsAbs\<cdot>msg) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
  by (metis assms(1) assms(2) sfilterl4 smed_slen_inf tsmed_tsabs)

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

lemma newora_f2 [simp]: "ora2\<noteq>\<bottom> \<Longrightarrow> (newOracle\<cdot>(\<up>False \<bullet> ora1)\<cdot>ora2) = \<up>False \<bullet> newOracle\<cdot>ora1\<cdot>ora2"
  by (metis newora_f scases)
  
lemma newora_t [simp]: "(newOracle\<cdot>(\<up>True \<bullet> ora1)\<cdot>(\<up>ora \<bullet> ora2)) = \<up>ora \<bullet> newOracle\<cdot>ora1\<cdot>ora2"
by (simp add: conc2cons)

lemma newora_fair_adm: "adm (\<lambda>a. \<forall>x. #a \<le> #({True} \<ominus> x) \<longrightarrow> #({True} \<ominus> newOracle\<cdot>x\<cdot>a) = #({True} \<ominus> a))"
proof (rule adm_all, rule admI, rule+)
  fix x Y
  assume ch_Y: "chain Y" and as1:"\<forall>i. #(Y i) \<le> #({True} \<ominus> x) \<longrightarrow> #({True} \<ominus> newOracle\<cdot>x\<cdot>(Y i)) = #({True} \<ominus> Y i)"
    and as2: " #(\<Squnion>i. Y i) \<le> #({True} \<ominus> x)"
  have "\<And>i. #(Y i) \<sqsubseteq> #(\<Squnion>i. Y i)"
    using ch_Y is_ub_thelub monofun_cfun_arg by blast
  hence "\<And>i. #(Y i) \<le> #({True} \<ominus> x)"
    using as2 lnle_conv trans_lnle by blast
  thus "#({True} \<ominus> newOracle\<cdot>x\<cdot>(\<Squnion>i. Y i)) = #({True} \<ominus> (\<Squnion>i. Y i))"
  proof -
    have "(\<Squnion>n. #({True} \<ominus> newOracle\<cdot>x\<cdot>(Y n))) = (\<Squnion>n. #({True} \<ominus> Y n))"
      using \<open>\<And>i. #(Y i) \<le> #({True} \<ominus> x)\<close> as1 by presburger
    then show ?thesis
      by (simp add: ch_Y contlub_cfun_arg)
  qed
qed    

lemma new_ora_ntimes: "ora2\<noteq>\<bottom>\<Longrightarrow>newOracle\<cdot>((sntimes n (\<up>False)) \<bullet> ora1)\<cdot>ora2 =(sntimes n (\<up>False)) \<bullet> newOracle\<cdot>ora1\<cdot>ora2"
  apply(induction n)
   by auto
    
lemma newora_fair_h:  "#ora2 \<le> #({True} \<ominus> ora1) \<longrightarrow> #({True} \<ominus> (newOracle\<cdot>ora1\<cdot>ora2))=#({True} \<ominus> ora2)"  
  proof(induction ora2 arbitrary: ora1 rule: ind)
    case 1
    then show ?case
      using newora_fair_adm by blast
  next
    case 2
    then show ?case by simp
  next
    case (3 a s)
    show ?case 
    proof
      assume as: "#(\<up>a \<bullet> s) \<le> #({True} \<ominus> ora1)"
      hence "0 < #({True} \<ominus> ora1)" using lnless_def by auto
      obtain n where n_def: "(sntimes n (\<up>False)) \<bullet> \<up>True \<sqsubseteq> ora1"
        using \<open>0 < #({True} \<ominus> ora1)\<close> lnless_def sbool_ntimes_f by fastforce
      obtain newora where newora_def: "ora1 = (sntimes n (\<up>False)) \<bullet> \<up>True \<bullet> newora"
        using approxl3 assoc_sconc n_def by blast
      have h1: "newOracle\<cdot>ora1\<cdot>(\<up>a \<bullet> s) = (sntimes n (\<up>False)) \<bullet> \<up>a \<bullet> (newOracle\<cdot>newora\<cdot>s) "
        by (simp add: n_def new_ora_ntimes newora_def)
      have h2: "#({True} \<ominus> ora1) = lnsuc\<cdot>(#({True} \<ominus> newora))"
        by (simp add: n_def newora_def)
      thus "#({True} \<ominus> newOracle\<cdot>ora1\<cdot>(\<up>a \<bullet> s)) = #({True} \<ominus> \<up>a \<bullet> s)"
        by (metis "3.IH" as h1 lnsuc_lnle_emb sfilter_in sfilter_nin sfilter_ntimes slen_scons)
             
    qed
  qed
    
lemma newora_fair: assumes "#({True} \<ominus> ora1)=\<infinity>" and "#({True} \<ominus> ora2)=\<infinity>"
  shows "#({True} \<ominus> (newOracle\<cdot>ora1\<cdot>ora2))=\<infinity>"
  by (simp add: assms(1) assms(2) newora_fair_h)

    
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
    proof (cases rule: oracases [of ora1])
      case 1
      then show ?thesis by simp
    next
      case (2 as)
      then show ?thesis
        by (metis delayfun.IH delayfun.prems(1) delayfun.prems(2) inf_scase lscons_conv newora_t stream.con_rews(2) tsmed_delayfun up_defined)
    next
      case (3 as)
      then show ?thesis
        by (metis delayfun(2) delayfun(3) delayfun.IH inf_scase lscons_conv newora_f2 stream.con_rews(2) tsmed_delayfun up_defined)        
    qed
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

text {* Two medium with fairness requirement can be reduced to one medium with fairness requirement. *}
lemma tsmed2infmed: assumes "#({True} \<ominus> ora1)=\<infinity>" and "#({True} \<ominus> ora2)=\<infinity>" 
  obtains ora3 where "tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>ora3" and "#({True} \<ominus> ora3)=\<infinity>"
by (meson assms(1) assms(2) newora_fair sfilterl4 tsmed2med)

(* property 4 *) 

lemma ora_inf: "#({True} \<ominus> p) = \<infinity> \<Longrightarrow> #p = \<infinity>"
  using sfilterl4 by auto

lemma smed_smap:
  "sMed\<cdot>(smap f\<cdot>msg)\<cdot>ora = smap f\<cdot>(sMed\<cdot>msg\<cdot>ora)"
  apply (induct msg arbitrary: ora rule: ind, simp_all)
  apply (rule_tac x=ora in scases, simp_all)
  by (case_tac "aa=True", simp_all)

lemma sprojsnd_srcdups_slen: "#(srcdups\<cdot>(sprojsnd\<cdot>s)) \<le> #(sprojsnd\<cdot>(srcdups\<cdot>s))"
  apply (induction s rule: ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg lub_mono2)
  apply (rule_tac x=s in scases, simp_all)
  apply (case_tac "a=aa", simp_all)
  apply (case_tac a, case_tac aa, simp_all)
  apply (case_tac a, case_tac aa)
  apply (case_tac "ab=ac", simp_all)
  apply (case_tac "b=ba", simp_all)
  using less_lnsuc trans_lnle by blast

lemma smed_slen2smed:
  "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>msg\<cdot>ora))) \<noteq> \<infinity> \<Longrightarrow> #({True} \<ominus> ora) = \<infinity> 
     \<Longrightarrow> #(sprojfst\<cdot>(srcdups\<cdot>msg)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>msg\<cdot>ora))) 
     \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>msg)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>msg\<cdot>ora))) 
     \<Longrightarrow> sprojfst\<cdot>(srcdups\<cdot>msg) = sprojfst\<cdot>(srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora))"
sorry
(*
  by (metis slen_sprojfst smed_slen2smed2)
*)

lemma tsmed_tsabs_slen2tsmed_tsabs:
  "#(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>msg))) \<noteq> \<infinity> \<Longrightarrow> #({True} \<ominus> ora) = \<infinity> 
    \<Longrightarrow> #(tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>msg))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>msg)))
    \<Longrightarrow> #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>msg))) = #(tsAbs\<cdot>(tsRemDups\<cdot>(tsProjSnd\<cdot>(tsMed\<cdot>msg\<cdot>ora))))
    \<Longrightarrow> tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>msg)) = tsAbs\<cdot>(tsProjFst\<cdot>(tsRemDups\<cdot>(tsMed\<cdot>msg\<cdot>ora)))"
  apply (simp add: tsprojfst_tsabs tsprojsnd_tsabs tsremdups_tsabs tsmed_tsabs ora_inf)
  using smed_slen2smed by auto

lemma smed_slen2smed2_adm: 
  "adm (\<lambda>a. #(srcdups\<cdot>a) \<noteq> \<infinity> \<longrightarrow> (\<forall>x. #({True} \<ominus> x) = \<infinity> \<longrightarrow>
          #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>a\<cdot>x))) = #(srcdups\<cdot>a) \<longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>a)) = #(srcdups\<cdot>a) \<longrightarrow> 
            srcdups\<cdot>a = srcdups\<cdot>(sMed\<cdot>a\<cdot>x)))"
sorry

lemma srcdups_nfst2snd: "a \<noteq> shd s \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> srcdups\<cdot>s" 
  by (metis srcdups_neq srcdups_shd srcdups_srt strict_sdropwhile surj_scons)
    
lemma srcdups_fst2snd: "s \<noteq> \<epsilon> \<Longrightarrow> a = shd s \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> s) = srcdups\<cdot>s"
  by (metis srcdups_eq surj_scons)

lemma sprojsnd_srcdups_slen_fst: "#(srcdups\<cdot>(sprojsnd\<cdot>(\<up>a))) = Fin 1"
  by (simp add: sprojsnd_def)

lemma smed_slen2smed2:
  "#(srcdups\<cdot>msg) \<noteq> \<infinity> \<Longrightarrow> #({True} \<ominus> ora) = \<infinity> 
     \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>msg\<cdot>ora))) = #(srcdups\<cdot>msg) 
     \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>msg))= #(srcdups\<cdot>msg)
     \<Longrightarrow> (srcdups\<cdot>msg) = (srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora))"
  apply (induction msg arbitrary: ora rule: ind, simp_all)
  apply (simp add: smed_slen2smed2_adm)
  apply (case_tac "s=\<epsilon>")
  apply (rule_tac ts=ora in oracases, simp) 
  apply (metis smed_bot1 smed_t)
  apply (metis slen_empty_eq smed_bot1 smed_f strict_sprojsnd strict_srcdups)
  apply (case_tac "shd s=a")
  apply (rule_tac ts=ora in oracases, simp)
  apply (case_tac "sMed\<cdot>s\<cdot>as=\<epsilon>")
  sorry

(* ----------------------------------------------------------------------- *)
section {* tsMedium lemmata *}
(* ----------------------------------------------------------------------- *)  

lemma ora_exists: "#({a} \<ominus> (\<up>a \<infinity>)) = \<infinity>"
  by simp
    
lemma tsmed_exists: "(\<Lambda> ts. tsMed\<cdot>ts\<cdot>(\<up>True \<infinity>)) \<in> tsMedium"
  apply (subst tsMedium_def)
  using ora_exists by blast
    
lemma tsmedium_nempty [simp]: "tsMedium \<noteq> {}"
  by (metis empty_iff tsmed_exists)
 
end