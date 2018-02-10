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
lemma neworacle_test:
  "newOracle\<cdot>(<[True, True, False, True]>)\<cdot>(<[True, False, True]>) = <[True, False, False, True]>"
  proof-
    have test_simp: "newOracle\<cdot>(updis True && updis True && updis False && updis True && \<epsilon>)\<cdot>
      (updis True && updis False && updis True && \<epsilon>) =
       updis True && updis False && updis False && updis True && \<epsilon>"
      by fixrec_simp
    thus ?thesis 
      by (simp only: list2s_0 list2s_Suc)
  qed

lemma oracases [case_names bottom true false]:
  assumes bottom: "ts=\<bottom> \<Longrightarrow> P ts"
    and true: "\<And>as. ts= (\<up>True \<bullet> as) \<Longrightarrow> P ts"
    and false: "\<And>as. ts=(\<up>False \<bullet> as) \<Longrightarrow> P ts"
  shows "P ts"
  by (metis (full_types) bottom false scases true)

text {* Assumption for medium lemmata: #({True} \<ominus> ora)=\<infinity> *}
lemma tsmed_insert: "tsMed\<cdot>msg\<cdot>ora = tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
  by (simp add: tsMed_def)
                                           
lemma smed_insert: "sMed\<cdot>msg\<cdot>ora = sprojfst\<cdot>(sfilter {x. snd x}\<cdot>(szip\<cdot>msg\<cdot>ora))"
  by (simp add: sMed_def)    

lemma tsmed_strict [simp]: 
  "tsMed\<cdot>\<bottom>\<cdot>\<epsilon> = \<bottom>"
  "tsMed\<cdot>msg\<cdot>\<epsilon> = \<bottom>"
  "tsMed\<cdot>\<bottom>\<cdot>ora = \<bottom>"
  by (simp add: tsMed_def)+

lemma tsmed_mlscons_true:
  assumes "msg\<noteq>\<bottom>" 
    and " #ora=\<infinity>" 
  shows "tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>((updis True) && ora) = tsMLscons\<cdot>(updis m)\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
  using assms  
  proof-
    assume msg_nbot: "msg\<noteq>\<bottom>"
    assume ora_inf: "#ora=\<infinity>"
    hence thesis_simp: "tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>(updis m &&\<surd> msg)\<cdot>(updis True && ora))) =
      updis m &&\<surd> tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
      by (metis Inf'_neq_0 assms(1) mem_Collect_eq slen_empty_eq snd_conv tsfilter_mlscons_in 
          tsfilter_nbot tsprojfst_mlscons tszip_mlscons tszip_nbot)
    thus ?thesis 
       by (simp add: tsmed_insert)
  qed

lemma tsmed_mlscons_false:
  assumes "msg\<noteq>\<bottom>" 
    and " #ora=\<infinity>" 
  shows "tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>((updis False) && ora) = tsMed\<cdot>msg\<cdot>ora"
  using assms 
  proof-
    assume msg_nbot: "msg\<noteq>\<bottom>"
    assume ora_inf: "#ora=\<infinity>"
    hence thesis_simp: "tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>(updis m &&\<surd> msg)\<cdot>(updis False && ora))) =
      tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
      by (metis Inf'_neq_0 assms(1) mem_Collect_eq slen_empty_eq snd_conv tsfilter_mlscons_nin 
          tszip_mlscons tszip_nbot)
    thus ?thesis 
      by (simp add: tsmed_insert)
  qed

lemma tsmed_delayfun: 
  assumes "ora\<noteq>\<epsilon>" 
  shows "tsMed\<cdot>(delayFun\<cdot>msg)\<cdot>ora = delayFun\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
  using assms by (simp add: tsMed_def tszip_delayfun tsfilter_delayfun tsprojfst_delayfun)

lemma tsmed_nbot [simp]: 
  assumes "msg\<noteq>\<bottom>" 
    and "#ora=\<infinity>" 
  shows " tsMed\<cdot>msg\<cdot>ora \<noteq> \<bottom>"
  using assms by (simp add: tsmed_insert)

text {* If infinite ticks will be sent infinite ticks will be transmitted. *}
lemma tsmed_tstickcount [simp]: 
  assumes "#ora = \<infinity>" 
  shows "#\<surd>(tsMed\<cdot>msg\<cdot>ora) = #\<surd>msg"
  using assms by (simp add: tsmed_insert)

text {* If just infinite ticks will be sent just infinite ticks will be transmitted. *}
lemma tsmed_tsinftick [simp]: 
  assumes "#ora=\<infinity>" 
  shows "tsMed\<cdot>tsInfTick\<cdot>ora = tsInfTick"
  using assms
  proof-
    assume  ora_inf: "#ora = \<infinity>"
    hence thesis_simp: "tsProjFst\<cdot>(Abs_tstream (insert \<surd> (Msg ` Collect snd) \<ominus>
      Rep_tstream (tsZip\<cdot>(Abs_tstream \<up>\<surd>\<infinity>)\<cdot>ora))) = Abs_tstream \<up>\<surd>\<infinity>"
      by (metis (no_types, lifting)
          Inf'_neq_0 Rep_tstream_inject delayfun_insert insertI1 s2sinftimes sfilter_in
          sinftimes_unfold slen_empty_eq tick_msg tsInfTick.abs_eq tsInfTick.rep_eq
          tsconc_rep_eq tsprojfst_delayfun tszip_delayfun)
    thus ?thesis 
      by (simp add: tsmed_insert tsInfTick_def tsfilter_insert)
  qed

(* Frage? Fälle weglassen *)
text {* Medium without oracle will transmit all messages and ticks. *}
lemma tsmed_inftrue [simp]: "tsMed\<cdot>msg\<cdot>((\<up>True) \<infinity>) = msg"
  proof (induction msg, simp_all)
    case (delayfun msg)
    then show ?case 
      by (metis lscons_conv sinftimes_unfold stream.con_rews(2) 
          tsmed_delayfun up_defined)
  next
    case (mlscons msg t)
    then show ?case 
      by (metis lscons_conv sinftimes_unfold slen_sinftimes strict_icycle
          tsmed_mlscons_true tsmed_strict(2))
  qed

text {* Not every message will be transmitted. *}    
lemma tsmed_tsabs_slen: 
  assumes "#ora=\<infinity>" 
  shows " #(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) \<le> #(tsAbs\<cdot>msg)"
  using assms
  proof-
    assume ora_inf: "#ora = \<infinity>" 
    hence "#(tsAbs\<cdot>(tsFilter (Collect snd)\<cdot>(tsZip\<cdot>msg\<cdot>ora))) \<le> #(tsAbs\<cdot>msg)"
      by (metis tsfilter_tsabs_slen tszip_tsabs_slen)
    thus ?thesis 
      by (simp add: tsmed_insert) 
  qed

lemma tsmed_tsmap:
  assumes "#ora=\<infinity>" 
  shows "tsMed\<cdot>(tsMap f\<cdot>msg)\<cdot>ora = tsMap f\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
  using assms
  proof (induction msg arbitrary: ora)
    case adm
    then show ?case 
      by simp
  next
    case bottom
    then show ?case
      by simp
  next
    case (delayfun msg)
    then show ?case 
      by (metis tsmap_delayfun tsmed_delayfun tsmed_strict(2))
  next
    case (mlscons msg t)
    then show ?case
      proof (cases rule: oracases [of ora])
        case bottom
        then show ?thesis 
          by simp
      next
        case (true as)
        then show ?thesis 
          by (metis (no_types, lifting) fold_inf lnat.injects lscons_conv mlscons.IH mlscons.hyps 
              mlscons.prems slen_scons tsmap_mlscons tsmap_nbot tsmed_mlscons_true tsmed_nbot)
      next
        case (false as)
        then show ?thesis 
          by (metis (no_types, lifting) fold_inf lnat.injects lscons_conv mlscons.IH mlscons.hyps 
              mlscons.prems slen_scons tsmap_mlscons tsmap_nbot tsmed_mlscons_false)
      qed
  qed

lemma h3:
  assumes "#ora=\<infinity>"
    and "#(tsAbs\<cdot>msg) = \<infinity>" 
    and "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = #({True} \<ominus> ora)"
  shows "#(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(\<up>True \<bullet> ora))) = #({True} \<ominus> \<up>True \<bullet> ora)"
  using assms by (metis (no_types, lifting) Inf'_neq_0 lscons_conv sfilter_in singletonI 
    slen_empty_eq slen_updis_eq tsabs_bot tsabs_mlscons tsmed_mlscons_true tsmed_nbot)

lemma h4:
  assumes "#ora=\<infinity>"
    and "#(tsAbs\<cdot>msg) = \<infinity>" 
    and "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = #({True} \<ominus> ora)"
  shows "#(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(\<up>False \<bullet> ora))) = #({True} \<ominus> \<up>False  \<bullet> ora)"
  using assms by (metis Inf'_neq_0 lscons_conv sfilter_nin singletonD
    slen_empty_eq tsabs_bot tsmed_mlscons_false)
       
lemma h5: 
  assumes "#ora=\<infinity>" 
    and "#(tsAbs\<cdot>msg) = \<infinity>" 
    and "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = #({True} \<ominus> ora)"
  shows"#(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(\<up>a \<bullet> ora))) = #({True} \<ominus> \<up>a \<bullet> ora)"
  using assms by (metis (full_types) h3 h4)

lemma tsmed_tsabs: 
  assumes "#ora = \<infinity>" 
  shows "tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora) = sMed\<cdot>(tsAbs\<cdot>msg)\<cdot>ora"
  using assms
  proof-
  assume ora_inf: "#ora = \<infinity>"
    have thesis_simp: "tsAbs\<cdot>(tsProjFst\<cdot>(tsFilter (Collect snd)\<cdot>(tsZip\<cdot>msg\<cdot>ora))) = 
      sprojfst\<cdot>(Collect snd \<ominus> szip\<cdot>(tsAbs\<cdot>msg)\<cdot>ora)"
      by (simp add: ora_inf tsfilter_tsabs tsprojfst_tsabs tszip_tsabs)
    thus ?thesis 
    by (simp add: tsMed_def sMed_def)
  qed
    
lemma smed_t [simp]: "sMed\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>True \<bullet> ora) = \<up>a \<bullet> (sMed\<cdot>as\<cdot>ora)"
  by (simp add: sMed_def)

lemma smed_f [simp]: "sMed\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>False \<bullet> ora) = (sMed\<cdot>as\<cdot>ora)"
  by (simp add: sMed_def) 

lemma smed_bot1 [simp]: "sMed\<cdot>\<bottom>\<cdot>ora = \<bottom>"
  by (simp add: sMed_def)

lemma smed_bot2 [simp]: "sMed\<cdot>msg\<cdot>\<bottom> = \<bottom>"
  by (simp add: sMed_def)    

lemma smed_slen_inf [simp]: 
  assumes "#msg=\<infinity>"
  shows "#(sMed\<cdot>msg\<cdot>ora) = #({True} \<ominus> ora)"
  using assms
  proof (induction ora arbitrary: msg rule:ind, simp_all)
    case (3 a s)
    have h1: "a = True \<Longrightarrow> ?case"
      using "3.IH" "3.prems" inf_scase by force 
    have h2: "a = False \<Longrightarrow> ?case"
      using "3.IH" "3.prems" inf_scase by force      
    then show ?case 
      using h1 h2 by blast
  qed

lemma smed_inftrue: "sMed\<cdot>msg\<cdot>((\<up>True) \<infinity>) = msg"  
  proof (induction msg rule: ind, simp_all)
    have lscons_simp: "\<And>a s. sprojfst\<cdot>({x. snd x} \<ominus> szip\<cdot>s\<cdot>\<up>True\<infinity>) = s 
      \<Longrightarrow>sprojfst\<cdot>({x. snd x} \<ominus> szip\<cdot>(\<up>a \<bullet> s)\<cdot>\<up>True\<infinity>) = \<up>a \<bullet> s"
      by (metis sinftimes_unfold smed_insert smed_t)
    thus "\<And>a s. sMed\<cdot>s\<cdot>\<up>True\<infinity> = s \<Longrightarrow> sMed\<cdot>(\<up>a \<bullet> s)\<cdot>\<up>True\<infinity> = \<up>a \<bullet> s"
      by (simp add: smed_insert) 
  qed
  
lemma tsmed_tsabs_slen_inf [simp]:
  assumes "#({True} \<ominus> ora) = \<infinity>" 
    and "#(tsAbs\<cdot>msg) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
  by (metis assms(1) assms(2) sfilterl4 smed_slen_inf tsmed_tsabs)

lemma tsmed_tsdom: 
  assumes "#ora=\<infinity>"
  shows "tsDom\<cdot>(tsMed\<cdot>msg\<cdot>ora) \<subseteq> tsDom\<cdot>msg"
  using assms
  proof (induction msg arbitrary: ora, simp_all)
    case (delayfun msg)
    then show ?case
      by (metis tsdom_delayfun tsmed_delayfun tsmed_strict(2)) 
  next
    case (mlscons msg t)
    then show ?case 
    proof -
      have lscons_conv_for_True: "\<up>True \<bullet> ora= (updis True) && ora"
        by (simp add:lscons_conv)  
      hence tsmed_mlscons_true_less_assms: "#ora=\<infinity>  \<Longrightarrow> tsMed\<cdot>(tsMLscons\<cdot>(updis t)\<cdot>msg)\<cdot>(\<up>True \<bullet> ora) 
        = tsMLscons\<cdot>(updis t)\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
        using tsmed_mlscons_true by force
      have ora_split: "ora = \<up>(shd ora) \<bullet> srt\<cdot>ora \<and> #(srt\<cdot>ora) = \<infinity>"
        by (metis Inf'_neq_0 fold_inf inject_lnsuc mlscons.prems 
            slen_empty_eq srt_decrements_length surj_scons)    
      have tsdom_ora_srt: "tsDom\<cdot>(tsMed\<cdot>msg\<cdot>(srt\<cdot>ora)) \<subseteq> {t} \<union> tsDom\<cdot>msg"
        by (metis Inf'_neq_0 fold_inf inject_lnsuc mlscons.IH 
            mlscons.prems slen_empty_eq srt_decrements_length sup.coboundedI2)      
      { assume "({t} \<union> tsDom\<cdot>(tsMed\<cdot>msg\<cdot>(srt\<cdot>ora)) \<subseteq> {t} \<union> tsDom\<cdot>msg) \<noteq>
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

lemma conc2cons: "\<up>a \<bullet>as = updis a && as"
  by (simp add: lscons_conv)    
    
lemma newora_f [simp]: 
  "(newOracle\<cdot>(\<up>False \<bullet> ora1)\<cdot>(\<up>ora \<bullet> ora2)) = \<up>False \<bullet> newOracle\<cdot>ora1\<cdot>(\<up>ora \<bullet> ora2)"
  by (simp add: conc2cons)

lemma newora_f2 [simp]: 
  "ora2\<noteq>\<bottom> \<Longrightarrow> (newOracle\<cdot>(\<up>False \<bullet> ora1)\<cdot>ora2) = \<up>False \<bullet> newOracle\<cdot>ora1\<cdot>ora2"
  by (metis newora_f scases)
  
lemma newora_t [simp]: "(newOracle\<cdot>(\<up>True \<bullet> ora1)\<cdot>(\<up>ora \<bullet> ora2)) = \<up>ora \<bullet> newOracle\<cdot>ora1\<cdot>ora2"
  by (simp add: conc2cons)

lemma newora_fair_adm: 
  "adm (\<lambda>a. \<forall>x. #a \<le> #({True} \<ominus> x) \<longrightarrow> #({True} \<ominus> newOracle\<cdot>x\<cdot>a) = #({True} \<ominus> a))"
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

lemma new_ora_ntimes: 
  assumes "ora2\<noteq>\<bottom>" 
  shows "newOracle\<cdot>((sntimes n (\<up>False)) \<bullet> ora1)\<cdot>ora2 =(sntimes n (\<up>False)) \<bullet> newOracle\<cdot>ora1\<cdot>ora2"
  using assms
  proof (induction n, simp_all)
  qed

lemma newora_fair_h:  
  "#ora2 \<le> #({True} \<ominus> ora1) \<longrightarrow> #({True} \<ominus> (newOracle\<cdot>ora1\<cdot>ora2))=#({True} \<ominus> ora2)"  
  proof(induction ora2 arbitrary: ora1 rule: ind)
    case 1
    then show ?case
      using newora_fair_adm by blast
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    show ?case 
    proof
      assume as: "#(\<up>a \<bullet> s) \<le> #({True} \<ominus> ora1)"
      hence "0 < #({True} \<ominus> ora1)" 
        using lnless_def by auto
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
    
lemma newora_fair: 
  assumes "#({True} \<ominus> ora1)=\<infinity>" 
    and "#({True} \<ominus> ora2)=\<infinity>"
  shows "#({True} \<ominus> (newOracle\<cdot>ora1\<cdot>ora2))=\<infinity>"
  by (simp add: assms(1) assms(2) newora_fair_h)
    
lemma smed2med: 
  shows "sMed\<cdot>(sMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = sMed\<cdot>msg\<cdot>(newOracle\<cdot>ora1\<cdot>ora2 )"
  proof(induction msg arbitrary: ora1 ora2 rule: ind, simp_all)
    case (3 a s)
    then show ?case 
    proof (cases rule: oracases [of ora1])
      case bottom
      then show ?thesis by simp
    next
      case (true as)
      then show ?thesis 
        by (cases rule: oracases [of ora2], auto simp add: "3.IH")
    next
      case (false as)
      then show ?thesis       
        by (cases rule: oracases [of ora2], auto simp add: "3.IH")
    qed
  qed

lemma tsmed_mlscons_false2 [simp]: 
  assumes "msg\<noteq>\<bottom>" 
    and "ora\<noteq>\<bottom>" 
  shows "tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(\<up>False \<bullet> ora) = tsMed\<cdot>msg\<cdot>ora"
  using assms
  proof -
    assume msg_nbot: "msg \<noteq> \<bottom>"
    assume ora_nbot: "ora \<noteq> \<epsilon>"
    have thesis_simp: "tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>(updis m &&\<surd> msg)\<cdot>(updis False && ora))) =
      tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
      by (metis (full_types) msg_nbot ora_nbot mem_Collect_eq snd_conv tsfilter_mlscons_nin tsmlscons_bot2 tszip_mlscons)
    thus ?thesis
      by(simp add: tsmed_insert conc2cons)
  qed

lemma tsmed_mlscons_true2 [simp]: 
  assumes "msg\<noteq>\<bottom>" 
    and "ora\<noteq>\<bottom>"
  shows "tsMed\<cdot>(tsMLscons\<cdot>(updis m)\<cdot>msg)\<cdot>(\<up>True \<bullet> ora) = updis m &&\<surd> tsMed\<cdot>msg\<cdot>ora"
  using assms
  proof-
    assume msg_nbot: "msg \<noteq> \<bottom>"
    assume ora_nbot: "ora \<noteq> \<epsilon>"
    have thesis_simp: "tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>(updis m &&\<surd> msg)\<cdot>(updis True && ora))) =
      updis m &&\<surd> tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
      by (metis (no_types, lifting) ora_nbot mem_Collect_eq snd_conv tsfilter_mlscons_in 
          tsfilter_strict tsmlscons_bot2 tsprojfst_mlscons tsprojfst_strict tszip_mlscons)
    thus ?thesis
      by(simp add: tsmed_insert conc2cons)
  qed

text {* Two medium can be reduced to one medium. *}
lemma tsmed2med: 
  assumes "#ora1=\<infinity>"
    and "#ora2=\<infinity>" 
  shows "tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>(newOracle\<cdot>ora1\<cdot>ora2)"
  using assms
  proof(induction msg arbitrary: ora1 ora2, simp_all)
    case (delayfun msg)
    then show ?case
    proof (cases rule: oracases [of ora1])
      case bottom
      then show ?thesis by simp
    next
      case (true as)
      then show ?thesis
        by (metis delayfun.IH delayfun.prems(1) delayfun.prems(2) inf_scase lscons_conv 
            newora_t stream.con_rews(2) tsmed_delayfun up_defined)
    next
      case (false as)
      then show ?thesis
        by (metis delayfun(2) delayfun(3) delayfun.IH inf_scase lscons_conv newora_f2 
            stream.con_rews(2) tsmed_delayfun up_defined)        
    qed
  next
    case (mlscons msg t)
    then show ?case 
    proof (cases rule: oracases [of ora1])
      case bottom
      then show ?thesis 
        by simp
    next
      case (true as)
      then show ?thesis
      proof (cases rule: oracases [of ora2])
        case bottom
        then show ?thesis
          by simp 
      next
        case (true asa)
        fix asa :: "bool stream"
        assume ora1_true: "ora1 = \<up>True \<bullet> as"
        assume ora2_true: "ora2 = \<up>True \<bullet> asa"
        then show ?thesis
        proof-
          have thesis_simp: "tsMed\<cdot>(tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(updis True && as))\<cdot>(updis True && asa) =
            tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(updis True && newOracle\<cdot>as\<cdot>asa)"
            by (metis (no_types, lifting) fold_inf inject_lnsuc lscons_conv mlscons.IH mlscons.hyps 
                mlscons.prems(1) mlscons.prems(2) ora1_true ora2_true slen_scons 
                tsmed_mlscons_true2 tsmed_nbot tsmed_strict(2))
          thus ?thesis
            by (simp add: lscons_conv ora1_true ora2_true)    
        qed
      next
        case (false asa)
        fix asa :: "bool stream"
        assume ora1_true: "ora1 = \<up>True \<bullet> as"
        assume ora2_false: "ora2 = \<up>False \<bullet> asa"
        then show ?thesis
        proof-
          have thesis_simp: "tsMed\<cdot>(tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(updis True && as))\<cdot>(updis False && asa) =
            tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(updis False && newOracle\<cdot>as\<cdot>asa)"
            by (metis (no_types, lifting) ora1_true ora2_false fold_inf inject_lnsuc lscons_conv mlscons.IH mlscons.hyps
            mlscons.prems(1) mlscons.prems(2) slen_scons tsmed_mlscons_false2 tsmed_mlscons_true 
            tsmed_nbot tsmed_strict(2))
          thus ?thesis
            by (simp add: lscons_conv ora1_true ora2_false)
        qed 
      qed
    next
      case (false as)
      then show ?thesis  
      proof (cases rule: oracases [of ora2])
        case bottom
        then show ?thesis 
          by simp
      next
        case (true asa)
        fix asa :: "bool stream"
        assume ora1_false: "ora1 = \<up>False \<bullet> as"
        assume ora2_true: "ora2 = \<up>True \<bullet> asa"
        then show ?thesis
        proof-
          have thesis_simp: "tsMed\<cdot>(tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(updis False && as))\<cdot>(updis True && asa) =
            tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(updis False && newOracle\<cdot>as\<cdot>(updis True && asa))"
            by (metis (no_types, lifting) ora1_false ora2_true fold_inf inject_lnsuc lscons_conv mlscons.IH 
                mlscons.hyps mlscons.prems(1) mlscons.prems(2) slen_scons tsmed_mlscons_false2 
                tsmed_nbot tsmed_strict(2))
          thus ?thesis
            by (simp add: lscons_conv ora1_false ora2_true)
        qed
      next
        case (false asa)
        fix asa :: "bool stream"
        assume ora1_false: "ora1 = \<up>False \<bullet> as"
        assume ora2_false: "ora2 = \<up>False \<bullet> asa"
        then show ?thesis 
        proof-
          have thesis_simp: "tsMed\<cdot>(tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(updis False && as))\<cdot>(updis False && asa) =
            tsMed\<cdot>(updis t &&\<surd> msg)\<cdot>(updis False && newOracle\<cdot>as\<cdot>(updis False && asa))"
            by (metis (no_types, lifting) ora1_false ora2_false fold_inf inject_lnsuc lscons_conv mlscons.IH mlscons.hyps 
                mlscons.prems(1) mlscons.prems(2) slen_scons tsmed_mlscons_false2 tsmed_nbot 
                tsmed_strict(2)) 
          thus ?thesis
            by (simp add: lscons_conv ora1_false ora2_false)
        qed
      qed  
    qed  
  qed

text {* Two medium with fairness requirement can be reduced to one medium with fairness requirement. *}
lemma tsmed2infmed: 
  assumes "#({True} \<ominus> ora1)=\<infinity>" 
    and "#({True} \<ominus> ora2)=\<infinity>" 
  obtains ora3 where "tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>ora3" 
    and "#({True} \<ominus> ora3)=\<infinity>"
  by (meson assms(1) assms(2) newora_fair sfilterl4 tsmed2med)

(* Frage? *)
(* property 4 *)
lemma ora_inf: 
  assumes "#({True} \<ominus> p) = \<infinity>" 
  shows " #p = \<infinity>"
  using sfilterl4 assms  by auto

lemma smed_smap: "sMed\<cdot>(smap f\<cdot>msg)\<cdot>ora = smap f\<cdot>(sMed\<cdot>msg\<cdot>ora)"
  proof (induct msg arbitrary: ora rule: ind)
    case 1
    then show ?case
      by simp
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    then show ?case
      by (cases rule: oracases [of ora], simp_all)
  qed


(* TODO *)
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

lemma sprojsnd_srcdups_slen: "#(srcdups\<cdot>(sprojsnd\<cdot>s)) \<le> #(sprojsnd\<cdot>(srcdups\<cdot>s))"
  proof (induction s rule: ind)
    case 1
    then show ?case 
      proof (rule admI)
        fix Y :: "nat \<Rightarrow> ('b \<times> 'a) stream"
        assume Y_chain: "chain Y"
        assume adm_assump: "\<forall>i. #(srcdups\<cdot>(sprojsnd\<cdot>(Y i))) \<le> #(sprojsnd\<cdot>(srcdups\<cdot>(Y i)))"
        then show "#(srcdups\<cdot>(sprojsnd\<cdot>(\<Squnion>i. Y i))) \<le> #(sprojsnd\<cdot>(srcdups\<cdot>(\<Squnion>i. Y i)))"
          by (simp add: Y_chain adm_assump contlub_cfun_arg lub_mono2)
      qed
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    then show ?case 
      proof (cases rule: scases [of s])
        case bottom
        then show ?thesis sorry
      next
        case (scons b bs)
        then show ?thesis sorry
      qed
  oops

lemma smed_slen: "#(sMed\<cdot>msg\<cdot>ora) \<le> #msg"
  proof-
    have thesis_simp: "#(sprojfst\<cdot>({x. snd x} \<ominus> szip\<cdot>msg\<cdot>ora)) \<le> #msg"
      by (metis min.bounded_iff slen_sfilterl1 slen_sprojfst szip_len)
    thus ?thesis
      by (simp add: smed_insert)
  qed

lemma smed_slen2shd:
  assumes "#msg \<noteq> \<infinity>"
    and "#(sMed\<cdot>msg\<cdot>ora) = #msg" 
  shows "shd (sMed\<cdot>msg\<cdot>ora) = shd msg"
  using assms
  proof (rule_tac x=msg in scases, simp_all)
    fix a :: "'a" and s :: "'a stream" and as :: "bool stream"
    assume s_fin: "#s \<noteq> \<infinity>"
    assume msg_lscons: "msg = \<up>a \<bullet> s"
    show "#(sMed\<cdot>(\<up>a \<bullet> s)\<cdot>ora) = lnsuc\<cdot>(#s) \<Longrightarrow> shd (sMed\<cdot>(\<up>a \<bullet> s)\<cdot>ora) = a"
    proof (rule_tac ts=ora in oracases, simp_all)
      show "\<And>as. #(sMed\<cdot>s\<cdot>as) = lnsuc\<cdot>(#s) \<Longrightarrow> ora = \<up>False \<bullet> as \<Longrightarrow> shd (sMed\<cdot>s\<cdot>as) = a"
        by (metis antisym_conv2 dual_order.refl inf_ub le2lnle s_fin smed_slen)
    qed
  qed

lemma smed_slen2s:
  "#msg \<noteq> \<infinity> \<and> #(sMed\<cdot>msg\<cdot>ora) = #msg \<Longrightarrow> sMed\<cdot>msg\<cdot>ora = msg"
  proof (induction msg arbitrary: ora rule: ind)
    case 1
    then show ?case
    proof (rule adm_all, rule adm_imp, simp_all)
      fix x :: "bool stream"
      show "adm (\<lambda>xa. #xa = \<infinity> \<or> #(sMed\<cdot>xa\<cdot>x) \<noteq> #xa)"
        by (metis (mono_tags, lifting) admI inf_chainl4 l42)
    qed
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    then show ?case
    proof (rule_tac oracases [of ora], simp_all)
      fix as :: "bool stream"
      assume s_len: "#s \<noteq> \<infinity> \<and> #(sMed\<cdot>s\<cdot>as) = #s"
      assume thesis: "(\<And>ora. #(sMed\<cdot>s\<cdot>ora) = #s \<Longrightarrow> sMed\<cdot>s\<cdot>ora = s)"
      show "ora = \<up>True \<bullet> as \<Longrightarrow> \<up>a \<bullet> sMed\<cdot>s\<cdot>as = \<up>a \<bullet> s"
        by (simp add: "3.IH" s_len)
    next
      fix as :: "bool stream"
      assume s_len: "#s \<noteq> \<infinity> \<and> #(sMed\<cdot>s\<cdot>as) = lnsuc\<cdot>(#s)"
      assume thesis: "(\<And>ora. #(sMed\<cdot>s\<cdot>ora) = #s \<Longrightarrow> sMed\<cdot>s\<cdot>ora = s)"
      show "ora = \<up>False \<bullet> as \<Longrightarrow> sMed\<cdot>s\<cdot>as = \<up>a \<bullet> s"
        by (metis "3.prems" antisym_conv1 inf_ub ln_less not_less slen_scons 
            smed_f smed_inftrue smed_slen)
    qed
  qed

lemma srcdups_nfst2snd: 
  assumes "a \<noteq> shd s" 
  shows "srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> srcdups\<cdot>s" 
  using assms by (metis srcdups_neq srcdups_shd srcdups_srt strict_sdropwhile surj_scons)
    
lemma srcdups_fst2snd: 
  assumes "s \<noteq> \<epsilon>" 
    and "a = shd s" 
  shows "srcdups\<cdot>(\<up>a \<bullet> s) = srcdups\<cdot>s"
  using assms by (metis srcdups_eq surj_scons)

lemma dropwhile_shd_f: 
  assumes "shd s \<noteq> a" 
  shows "sdropwhile (\<lambda>x. x = a)\<cdot>s = s"
  using assms by (metis (full_types) sdropwhile_f strict_sdropwhile surj_scons)
     
lemma drop2med: "sdrop n\<cdot>s = sMed\<cdot>s\<cdot>((sntimes n (\<up>False)) \<bullet> ((\<up>True)\<infinity>))" 
  proof (induction n arbitrary: s)
    case 0
    then show ?case 
      by (simp add: smed_inftrue)
  next
    case (Suc n)
    then show ?case 
      by (rule_tac x=s in scases, simp_all)
  qed

lemma dropwhile_inf_bot: "sdropwhile (\<lambda>x. x = a)\<cdot>\<up>a\<infinity> = \<epsilon>"
  proof -
    have h2:"\<forall>a. sdom\<cdot>\<up>a\<infinity> = {a}" 
      by simp
    have "\<forall>a b s.(sdropwhile (\<lambda>x. x = a)\<cdot>(sinftimes (\<up>a))) \<noteq> \<up>b \<bullet> s"  
      apply auto
      apply (case_tac "b=a")
      using sdropwhile_resup apply blast
      by (metis (no_types) Un_absorb h2 insert_commute insert_is_Un sdom2un 
          singleton_insert_inj_eq' srcdups_dom srcdups_step)
    then have "\<forall>a.(sdropwhile (\<lambda>x. x = a)\<cdot>(sinftimes (\<up>a))) = \<epsilon>"
      by (metis scases)
    thus ?thesis 
      by auto
  qed

lemma slen_dropwhile_takewhile: 
  "sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> #(stakewhile (\<lambda>x. x = a)\<cdot>s) \<noteq> \<infinity>"
  apply (erule_tac contrapos_pp,simp)
  using stakewhile_sinftimesup [of a s] apply (simp)
  by (simp add: dropwhile_inf_bot)

lemma dropwhile2drop: 
  "sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> \<exists>n .sdropwhile (\<lambda>x. x = a)\<cdot>s = sdrop n\<cdot>s"
  by (metis stakewhile_sdropwhilel1 ninf2Fin slen_dropwhile_takewhile)

lemma dropwhile2smed: "\<exists>ora. sdropwhile (\<lambda>x. x = a)\<cdot>s = sMed\<cdot>s\<cdot>ora"
  apply (case_tac "sdropwhile (\<lambda>x. x = a)\<cdot>s = \<epsilon>")
  apply (metis (no_types) smed_bot2)
  by (metis dropwhile2drop drop2med)

lemma stakewhileDropwhile_rev: "s = stakewhile f\<cdot>s \<bullet> (sdropwhile f\<cdot>s)"
  by (simp add: stakewhileDropwhile)

text {* @{term sdropwhile} after @{term stakewhile} gives the empty stream *}
lemma dtw: "sdropwhile f\<cdot>(stakewhile f\<cdot>s) = \<epsilon>"
  apply (rule ind [of _ s], auto)
  by (case_tac "f a", auto)

lemma split_stream_rev: "s = stake n\<cdot>s \<bullet> sdrop n\<cdot>s " 
  by simp

lemma szip_slen_conc: "#ora \<le> #sa \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora =  szip\<cdot>sa\<cdot>ora"
  apply (induction k arbitrary: ora sa sb,simp_all)
  apply (rule_tac x=sa in scases,simp_all)
  by (rule_tac x=ora in scases,simp_all)

lemma szip_slen_conc2: 
  "#ora > #sa \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop k\<cdot>ora)"
  apply (induction k arbitrary: ora sa sb,simp_all)
  apply (rule_tac x=sa in scases,simp_all)
  by (rule_tac x=ora in scases,simp_all)

lemma add_sfilter_rev:
  "#x = Fin k \<Longrightarrow> sfilter t\<cdot>x \<bullet> sfilter t\<cdot>y = sfilter t\<cdot>(x \<bullet> y)" 
  by (simp add: add_sfilter)

lemma smed_conc: "\<exists>ora2. sMed\<cdot>(sa \<bullet> sb)\<cdot>ora = sMed\<cdot>sa\<cdot>ora \<bullet> sMed\<cdot>sb\<cdot>ora2"
  apply (case_tac "#sa = \<infinity>",simp)
  apply (metis (no_types) sconc_snd_empty smed_bot2)
  using ninf2Fin [of "#sa"] apply auto
  apply (case_tac "#ora \<le> #sa")
  apply (rule_tac x=\<epsilon> in exI,simp)
  apply (simp add: smed_insert szip_slen_conc)
  apply (rule_tac x="sdrop k\<cdot>ora" in exI)
  apply (simp add: smed_insert sprojfst_def)
  apply (fold smap_split) 
  apply (subst add_sfilter_rev [of "szip\<cdot>sa\<cdot>ora" k])
  apply (simp add: min.absorb1)
  by (simp add: szip_slen_conc2)

lemma smed_dtw: "sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>(stakewhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora) = \<epsilon>"
  apply (induction s arbitrary: a ora rule: ind,simp_all) 
  apply (case_tac "aa=a",simp_all)
  by (rule_tac ts=ora in oracases,simp_all)

lemma sdropwhile_conc: 
  assumes "#sa = Fin k" 
  shows "sdropwhile (\<lambda>x. x = a)\<cdot>sa = \<epsilon> 
         \<Longrightarrow> sdropwhile (\<lambda>x. x = a)\<cdot>(sa \<bullet> sb) = sdropwhile (\<lambda>x. x = a)\<cdot>sb"
  apply (induction sa arbitrary: a sb rule: finind,simp_all)
  using assms apply auto[1]
  apply (case_tac "aa=a",simp)
  by (metis (full_types) sdropwhile_f srcdups_srt srcdups_step srcdupsimposs2 
      stream.sel_rews(2) strict_srcdups)

lemma dropwhile_med: 
  "\<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>s\<cdot>ora) = sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2"
  apply (case_tac "s= \<epsilon>",simp)
  apply (case_tac "(sMed\<cdot>s\<cdot>ora) = \<epsilon>",simp)
  using smed_bot2 apply blast 
  apply (case_tac "shd s \<noteq> a")
  apply (case_tac "shd (sMed\<cdot>s\<cdot>ora)  \<noteq> a")
  apply (simp add: dropwhile_shd_f,blast)
  apply (simp) 
  apply (metis dropwhile_shd_f dropwhile2smed smed2med,simp)
  apply (subst stakewhileDropwhile_rev [of s "(\<lambda>x. x = a)"])
  using smed_conc [of "stakewhile (\<lambda>x. x = a)\<cdot>s" "sdropwhile (\<lambda>x. x = a)\<cdot>s" ora] apply auto
  apply (case_tac "#(sMed\<cdot>(stakewhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora) = \<infinity>")
  apply (metis sconc_fst_inf smed_bot2 smed_dtw)
  by (metis sdropwhile_conc smed_dtw ninf2Fin dropwhile2smed smed2med)

lemma med_dropwhile_t: 
  "(sMed\<cdot>sa\<cdot>as) \<noteq> \<epsilon> \<Longrightarrow> shd (sMed\<cdot>sa\<cdot>as) = a \<Longrightarrow> srcdups\<cdot>(sMed\<cdot>sa\<cdot>as) = \<up>a \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>sa\<cdot>as))"
  apply(rule_tac x="sMed\<cdot>sa\<cdot>as" in scases,simp_all)
  by (simp add: srcdups_step)

lemma dropwhile_f: "s \<noteq> \<epsilon> \<Longrightarrow> shd s \<noteq> a \<Longrightarrow> s =  sdropwhile (\<lambda>x. x = a)\<cdot>s"
  by (metis (full_types) sdropwhile_f surj_scons)

lemma ora_t_ex: "\<exists>ora1. P (\<up>True\<bullet>ora1) \<Longrightarrow> \<exists>ora2. P ora2"
  by auto    
    
lemma ora_f_ex: "\<exists>ora1. P (\<up>False\<bullet>ora1) \<Longrightarrow> \<exists>ora2. P ora2"
  by auto   

lemma srcdups_fin:"#(srcdups\<cdot>msg) = Fin n \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow>\<exists>n2.  #(srcdups\<cdot>sa) = Fin n2" 
  apply (case_tac "shd sa = aa")
  apply (metis Fin_02bot lnzero_def only_empty_has_length_0 srcdups_eq strict_srcdups surj_scons)
  by (metis fold_inf infI slen_scons srcdups_nfst2snd)  
 
lemma newOra_srcdups_ex: 
  assumes "#(srcdups\<cdot>msg) = Fin n" 
  shows "\<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2"
  apply (induction "srcdups\<cdot>msg"  arbitrary: msg  ora1 rule: finind)
  using assms apply simp
  apply (metis smed_bot1 srcdups_nbot)
  apply (rule_tac x=msg in scases,simp)
  apply (rule_tac ts=ora1 in oracases,simp_all)
  using smed_bot2 apply blast
  apply (rule ora_t_ex)
  apply (simp add: srcdups_step)
  apply (metis inject_scons dropwhile_med)
  apply (case_tac "sa = \<epsilon>")
  apply (metis smed_bot1 smed_bot2 strict_srcdups)
  apply (case_tac "shd sa \<noteq> aa")
  apply (simp add: srcdups_nfst2snd)
  apply (rule ora_f_ex,simp)
  using inject_scons apply blast
  apply (simp add: srcdups_step)
  apply (case_tac "sMed\<cdot>sa\<cdot>as = \<epsilon>")
  apply (metis smed_bot2 strict_srcdups)
  apply (case_tac "shd (sMed\<cdot>sa\<cdot>as) = aa")
  apply (rule ora_t_ex,simp)
  apply (simp add: med_dropwhile_t)
  apply (metis inject_scons dropwhile_med)
  apply (rule ora_f_ex,simp)
  apply (subst dropwhile_f [of "sMed\<cdot>sa\<cdot>as" aa],simp_all)
  by (metis inject_scons dropwhile_med)

lemma srcdups_smed_h: " #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)"
  proof (induction s arbitrary: p rule: ind)
    case 1
    then show ?case 
      apply(rule adm_all)
      apply(rule admI)
      by(simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
  next
    case 2
    then show ?case by simp
  next
    case (3 a s)
    then show ?case 
      apply (case_tac "s= \<epsilon>")
      apply (cases rule: oracases,simp)
      apply (metis eq_refl smed_bot1 smed_t)
      apply (metis bot_is_0 eq_bottom_iff le_cases lnle_def smed_bot1 smed_f strict_slen strict_srcdups) 
      apply (cases rule: oracases,simp_all)
      apply (case_tac "sMed\<cdot>s\<cdot>as = \<epsilon>")
      apply (simp add: neq02Suclnle srcdups_nbot)
      apply (case_tac "shd s = a")
      apply (case_tac "shd (sMed\<cdot>s\<cdot>as) = a")
      apply (simp add: srcdups_fst2snd) 
      apply (cases rule: oracases,simp_all)
      apply (metis inject_scons smed_t surj_scons)
      apply (metis smed_f smed_t srcdups_fst2snd surj_scons)
      apply (simp add: srcdups_nfst2snd)
      apply (metis dropwhile2smed lnsuc_lnle_emb slen_scons smed2med srcdups_step)
      by (metis (no_types, lifting) less_lnsuc srcdups_nfst2snd srcdups_fst2snd slen_scons trans_lnle)
  qed              
 (* Frage? *)
lemma smed_slen2smed2: 
  assumes "#(srcdups\<cdot>s) \<noteq> \<infinity>" "#({True} \<ominus> p) = \<infinity>" "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) = #(srcdups\<cdot>s)"  
          "#(srcdups\<cdot>(sprojsnd\<cdot>s))= #(srcdups\<cdot>s)" 
  shows "(srcdups\<cdot>s) = (srcdups\<cdot>(sMed\<cdot>s\<cdot>p))" 
  using assms proof (erule_tac contrapos_np)
    have h1: "srcdups\<cdot>s \<noteq> srcdups\<cdot>(sMed\<cdot>s\<cdot>p) \<Longrightarrow> #(srcdups\<cdot>s) = \<infinity> \<or> #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<noteq> #(srcdups\<cdot>s)"
      by (metis infI newOra_srcdups_ex smed_slen2s)   
    have "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) \<noteq> #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<Longrightarrow>  #(srcdups\<cdot>(sprojsnd\<cdot>s)) \<noteq> #(srcdups\<cdot>s)"
      by (metis (no_types) antisym_conv assms(3) slen_sprojsnd sprojsnd_srcdups_slen srcdups_smed_h) 
    then have "#({True} \<ominus> p) = \<infinity> \<Longrightarrow>
      #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) = #(srcdups\<cdot>s) \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>s)) = #(srcdups\<cdot>s) 
      \<Longrightarrow> srcdups\<cdot>s \<noteq> srcdups\<cdot>(sMed\<cdot>s\<cdot>p) \<Longrightarrow> #(srcdups\<cdot>s) \<noteq> #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<Longrightarrow> #(srcdups\<cdot>s) = \<infinity>"
      by simp   
    from this h1 show "#({True} \<ominus> p) = \<infinity> \<Longrightarrow>
    #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) = #(srcdups\<cdot>s) \<Longrightarrow>
    #(srcdups\<cdot>(sprojsnd\<cdot>s)) = #(srcdups\<cdot>s) \<Longrightarrow> srcdups\<cdot>s \<noteq> srcdups\<cdot>(sMed\<cdot>s\<cdot>p) \<Longrightarrow> #(srcdups\<cdot>s) = \<infinity>"
    by fastforce
  qed 

(* Frage? Einrückung?  *)

lemma smed_slen2smed:
  "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>msg\<cdot>ora))) \<noteq> \<infinity> \<Longrightarrow> #({True} \<ominus> ora) = \<infinity> 
     \<Longrightarrow> #(sprojfst\<cdot>(srcdups\<cdot>msg)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>msg\<cdot>ora))) 
     \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>msg)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>msg\<cdot>ora))) 
     \<Longrightarrow> sprojfst\<cdot>(srcdups\<cdot>msg) = sprojfst\<cdot>(srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora))"
  by (metis slen_sprojfst smed_slen2smed2)

(* property 0 *)

lemma prop0_h:"#(srcdups\<cdot>(s\<bullet>s2)) \<le> #(srcdups\<cdot>(s\<bullet>\<up>b\<bullet>s2))"
  proof(induction rule: ind [of _ s])
    case 1
    then show ?case
      apply(rule admI)
      by (metis inf_chainl4 l42 order_refl sconc_fst_inf)
  next
    case 2
    then show ?case 
    proof -
      { assume "\<not> #(srcdups\<cdot>(\<epsilon> \<bullet> s2)) \<le> #(srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2))"
        { assume "srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2) \<noteq> \<up>b \<bullet> srcdups\<cdot>(\<up>(shd s2) \<bullet> srt\<cdot>s2)"
          { assume "srcdups\<cdot> (\<up>b \<bullet> \<up>(shd s2) \<bullet> srt\<cdot>s2) \<noteq> \<up>b \<bullet> srcdups\<cdot>(\<up>(shd s2) \<bullet> srt\<cdot>s2)"
            moreover
            { assume "srcdups\<cdot>(\<up>b \<bullet> \<up>(shd s2) \<bullet> srt\<cdot>s2) = srcdups\<cdot>(\<up>(shd s2) \<bullet> srt\<cdot>s2) 
                      \<and> srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2) \<noteq> srcdups\<cdot>(\<epsilon> \<bullet> s2)"
              then have "\<up>(shd s2) \<bullet> srt\<cdot>s2 \<noteq> s2"
                by force }
            ultimately have "\<up>(shd s2) \<bullet> srt\<cdot>s2 = s2 \<longrightarrow> #(srcdups\<cdot>(\<epsilon> \<bullet> s2)) \<le> #(srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2))"
              by (metis (no_types) eq_iff srcdups_eq2 srcdups_neq) }
          then have "\<up>(shd s2) \<bullet> srt\<cdot>s2 = s2 \<longrightarrow> #(srcdups\<cdot>(\<epsilon> \<bullet> s2)) \<le> #(srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2))"
            by force }
        moreover
        { assume "\<up>(shd s2) \<bullet> srt\<cdot>s2 \<noteq> s2"
          then have "s2 = \<epsilon>"
            by (metis surj_scons)
          then have ?thesis
            by force }
        ultimately have ?thesis
          by fastforce }
      then show ?thesis
        by metis
    qed
  next
    case (3 a s)
    then have case_epseq:"a=b \<Longrightarrow> #(srcdups\<cdot>(\<up>a \<bullet> s2)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> \<up>b \<bullet> s2))"
      by simp
    have case_epsneq:"a\<noteq>b \<Longrightarrow> #(srcdups\<cdot>(\<up>a \<bullet> s2)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> \<up>b \<bullet> s2))"
      apply (subst srcdups_neq,simp)
      apply (cases "s2=\<epsilon>",simp)
      apply (cases "b=shd s2")
      apply (metis eq_refl srcdups_eq srcdups_neq surj_scons)
      using surj_scons[of s2] srcdups_neq[of b "shd s2" "srt\<cdot>s2"] apply auto
      proof - (* Frage? - *)
        assume a1: "\<up>(shd s2) \<bullet> srt\<cdot>s2 = s2"
        have "#(srcdups\<cdot>s2) \<le> lnsuc\<cdot>(lnsuc\<cdot>(#(srcdups\<cdot>s2)))"
          by (meson dual_order.trans less_lnsuc)
        then show "#(srcdups\<cdot>(\<up>a \<bullet> s2)) \<le> lnsuc\<cdot>(lnsuc\<cdot>(#(srcdups\<cdot>s2)))"
          using a1 by (metis (no_types) less_lnsuc slen_scons srcdups_eq2 srcdups_neq)
      qed
    have case_eq: "s\<noteq>\<epsilon> \<Longrightarrow> a = shd s \<Longrightarrow> ?case"
      by (metis "3.IH" sconc_scons srcdups_eq surj_scons)
    have "s\<noteq>\<epsilon> \<Longrightarrow> a\<noteq>shd s \<Longrightarrow> ?case"
    proof -
      assume a1: "s \<noteq> \<epsilon>"
      assume a2: "a \<noteq> shd s"
      have "\<up>(shd s) \<bullet> srt\<cdot>s = s"
        using a1 by (meson surj_scons)
      then show ?thesis
        using a2 by (metis (no_types) "3.IH" lnsuc_lnle_emb sconc_scons slen_scons srcdups_neq)
    qed
    then show ?case
      using case_epseq case_epsneq case_eq by fastforce
  qed
   
lemma prop0_h2: 
  assumes "#p=\<infinity>"
  shows"#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>b\<bullet>p)))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<bullet>p))))"
  apply (cases "b", simp)
  proof (induction ts)
    case adm
    then show ?case
      apply (rule adm_imp,simp)
      apply (rule admI)
      by (simp add: contlub_cfun_arg assms contlub_cfun_fun lub_mono2)
  next
    case bottom
    then show ?case
      by simp
  next
    case (delayfun ts)
    then show ?case
      by (simp add: tsmed_delayfun)
  next
    case (mlscons ts t)
    have f1:"tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>(\<up>b \<bullet> p) = tsMed\<cdot>ts\<cdot>p"
      using tsmed_mlscons_false[of ts "p" t]  
      by (simp add: assms lscons_conv mlscons.hyps mlscons.prems)
    then show ?case 
      apply (simp add: f1)
      by (metis assms bot_is_0 lnle_def lscons_conv minimal mlscons.hyps prop0_h sconc_fst_empty 
          slen_empty_eq strict_srcdups tsabs_bot tsabs_mlscons tsmed_mlscons_true)
  qed

lemma prop0_h2_2: 
  assumes "#p=\<infinity>"
  shows"#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>p))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<bullet>(srt\<cdot>p)))))"
  using prop0_h2[of "srt\<cdot>p" ts "shd p"]
  by (metis Inf'_neq_0 assms fold_inf inject_lnsuc slen_empty_eq srt_decrements_length surj_scons)

  
lemma prop0_h3_h:"tsMed\<cdot>ts\<cdot>p\<noteq>\<bottom> \<Longrightarrow> tsAbs\<cdot>(updis t &&\<surd> tsMed\<cdot>ts\<cdot>p) = \<up>t \<bullet> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>p))"
  by (simp add: lscons_conv tsabs_mlscons)

lemma tsmed_shd_adm_h2:"chain Y \<Longrightarrow> Y i\<noteq>\<epsilon> \<Longrightarrow> shd (Y i) = shd (\<Squnion>i. Y i)"
  by (simp add: below_shd is_ub_thelub)
    
lemma tsmed_shd:
  "#ora1=\<infinity> \<Longrightarrow> #ora2=\<infinity> 
   \<Longrightarrow> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(updis True && ora1))) = shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(updis True && ora2)))"
  proof (induction ts)
    case adm
    then show ?case
      apply (rule adm_imp,auto)+
      apply (rule admI) 
      apply(simp add: contlub_cfun_arg contlub_cfun_fun)
      proof-
        fix Y::"nat \<Rightarrow>'a tstream"
        assume a1: "chain Y"
        assume a2: "\<forall>i. shd (tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora1))) 
                    = shd (tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora2)))"
        have c1:"chain (\<lambda>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora1)))"
          by (simp add: a1)
        have c2:"chain (\<lambda>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora2)))"
          by (simp add: a1)
        show "shd (\<Squnion>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora1))) = shd (\<Squnion>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora2)))"
          by (metis (no_types, lifting) a2 c1 c2 lub_eq_bottom_iff tsmed_shd_adm_h2)
      qed
  next
    case bottom
    then show ?case 
      by simp
  next
    case (delayfun ts)
    then show ?case
      by (metis stream.con_rews(2) tsabs_delayfun tsmed_delayfun)
  next
    case (mlscons ts t)
    then show ?case
      by (metis prop0_h3_h shd1 tsmed_mlscons_true tsmed_nbot)
  qed

lemma tsmed_srcdups_shd:
  "#ora1=\<infinity> \<Longrightarrow> #ora2=\<infinity> \<Longrightarrow> shd (srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(updis True && ora1)))) 
   = shd (srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(updis True && ora2))))"
  by (metis srcdups_shd2 strict_srcdups tsmed_shd)  
    
(*maybe nice to have
  Frage?  
lemma prop0_ind_h2:
  shows"#p2=\<infinity> \<Longrightarrow> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(p1 \<bullet> p2)))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>((p1 \<bullet> \<up>True \<bullet> srt\<cdot>p2)))))"
*)

lemma prop0_h2_ind_h: 
  assumes "#p=\<infinity>"
  shows"#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>b \<bullet> p)))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<bullet>p))))"
  apply(cases "b", simp)
  proof(induction ts)
    case adm
    then show ?case
      apply(rule adm_imp,simp)
      apply(rule admI)
      by(simp add: contlub_cfun_arg assms contlub_cfun_fun lub_mono2)
  next
    case bottom
    then show ?case
      by simp
  next
    case (delayfun ts)
    then show ?case
      by (simp add: tsmed_delayfun)
  next
    case (mlscons ts t)
    have f1:"tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>(\<up>b \<bullet> p) = tsMed\<cdot>ts\<cdot>p"
      using tsmed_mlscons_false[of ts "p" t]  
      by (simp add: assms lscons_conv mlscons.hyps mlscons.prems)
    then show ?case 
      apply (simp add: f1)
      by (metis assms lscons_conv mlscons.hyps prop0_h prop0_h3_h tsmed_mlscons_true tsmed_nbot)
  qed    
        
lemma prop0_h3: 
  "#p=\<infinity> \<Longrightarrow> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>p))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<infinity>))))"
  proof (induction ts arbitrary: p)
    case adm
    then show ?case
      apply simp
      apply (rule adm_all)
      apply (rule adm_imp, auto)
      apply (rule admI)
      by (simp add: contlub_cfun_fun contlub_cfun_arg lub_mono2)
  next
    case bottom
    then show ?case
      by simp
  next
    case (delayfun ts)
    then show ?case
      by (metis (no_types, lifting) tsabs_delayfun tsmed_delayfun tsmed_strict(2))
  next
    case (mlscons ts t)
    have h1:"tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>(\<up>True\<bullet>(srt\<cdot>p)) = updis t &&\<surd> tsMed\<cdot>ts\<cdot>(srt\<cdot>p)"
      by (metis (no_types, lifting) Inf'_neq_0 fold_inf inject_lnsuc lscons_conv mlscons.hyps mlscons.prems slen_empty_eq srt_decrements_length tsmed_mlscons_true)
    have h2:"tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>\<up>True\<infinity> = updis t &&\<surd> tsMed\<cdot>ts\<cdot>\<up>True\<infinity>"
      by (metis tsmed_inftrue)
    have h5:"tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)) \<noteq> \<epsilon> \<Longrightarrow> t\<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<infinity>))) \<Longrightarrow> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))) =lnsuc\<cdot>(#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))))"
    proof -
      assume a1: "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)) \<noteq> \<epsilon>"
      assume a2: "t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))"
      have "p \<noteq> \<epsilon>"
        using mlscons.prems by force
      then have "lnsuc\<cdot>(#(srt\<cdot>p)) = \<infinity>"
        by (metis (no_types) mlscons.prems slen_scons surj_scons)
      then have "tsAbs\<cdot>ts \<noteq> \<epsilon>"
        using a1 by (metis bot_is_0 fold_inf inject_lnsuc leD lnless_def minimal slen_empty_eq tsmed_tsabs_slen)
      then show ?thesis
        using a2 by (metis (no_types) slen_scons srcdups_neq surj_scons tsmed_inftrue)
    qed
    have "#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>(\<up>True\<bullet>(srt\<cdot>p)))))\<le>#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>\<up>True\<infinity>)))"
      apply (simp only: h1 h2)
      apply (subst prop0_h3_h)
      apply (metis Inf'_neq_0 fold_inf inject_lnsuc mlscons.hyps mlscons.prems only_empty_has_length_0 srt_decrements_length tsmed_nbot)
      apply (subst prop0_h3_h)
      apply (simp add: mlscons.hyps)
      proof-
        have srt_len:"#(srt\<cdot>p) = \<infinity>"
          by (metis Inf'_neq_0 fold_inf inject_lnsuc mlscons.prems slen_empty_eq srt_decrements_length)
        then have h1:"#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)))) \<le>#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p)))))"
          by (metis Inf'_neq_0 prop0_h2_ind_h fold_inf lnat.sel_rews(2) only_empty_has_length_0 srt_decrements_length surj_scons)
        have h2:"#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
        proof (cases "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))) = \<epsilon>")
          case True
          then show ?thesis
            by (metis lnle_def minimal monofun_cfun_arg)
        next
          case False
          then show ?thesis
          proof(cases "t= shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))")
            case True
            assume a1: "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))) \<noteq> \<epsilon>"
            assume a2: "t = shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))"
            have h10:"\<And>s a. #(srcdups\<cdot>s) \<le> #(srcdups\<cdot>(\<up>(a::'a) \<bullet> s))"
              by (metis (full_types) prop0_h sconc_fst_empty)
            then have "#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)))) \<le> #(srcdups\<cdot> (\<up>t \<bullet> tsAbs\<cdot> (tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
              using srt_len dual_order.trans mlscons.IH by blast
            then show "#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
              using a2 a1
            proof -
              have "\<not> #(srcdups\<cdot> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))) < #(srcdups\<cdot> (\<up>t \<bullet> tsAbs\<cdot> (tsMed\<cdot>ts\<cdot> (\<up>True \<bullet> srt\<cdot> (srt\<cdot>p)))))"
                by (metis (no_types) Inf'_neq_0 srt_len a1 a2 leD mlscons.IH only_empty_has_length_0 slen_scons srcdups_eq surj_scons)
              then show ?thesis
                by (meson h10 le_less_trans not_le_imp_less)
            qed
          next
            case False
            assume a1: "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))) \<noteq> \<epsilon>"
            assume a2: "t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))"
            have "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>) \<noteq>\<epsilon>"
              by (metis Inf'_neq_0 srt_len a1 leD lnless_def lnzero_def minimal slen_empty_eq slen_scons srt_decrements_length tsmed_inftrue tsmed_tsabs_slen)
            then have "shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p)))) = shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))"
              by (metis tsmed_shd sinftimes_unfold deconstruct_infstream_h lscons_conv mlscons.prems slen_sinftimes stream.con_rews(2) stream.sel_rews(5) sup'_def up_defined)
            then have "t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))"
              using a2 by simp
            then show "#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
            proof -
              have f1: "lnsuc\<cdot> (#(srcdups\<cdot> (tsAbs\<cdot> (tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p)))))) \<le> lnsuc\<cdot> (#(srcdups\<cdot> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))))"
                by (metis (no_types) Inf'_neq_0 srt_len lnsuc_lnle_emb mlscons.IH only_empty_has_length_0 slen_scons surj_scons)
              have f2: "\<forall>s. s = \<epsilon> \<or> \<up>(shd s::'a) \<bullet> srt\<cdot>s = s"
                by (metis surj_scons)
              have f3: "\<forall>a aa s. (a::'a) = aa \<or> srcdups\<cdot>(\<up>a \<bullet> \<up>aa \<bullet> s) = \<up>a \<bullet> srcdups\<cdot>(\<up>aa \<bullet> s)"
                by (meson srcdups_neq)
              then have "srcdups\<cdot> (\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)) = \<up>t \<bullet> srcdups\<cdot> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))"
                using f2 by (metis (no_types) \<open>t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))\<close> \<open>tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>) \<noteq> \<epsilon>\<close>)
              then show ?thesis
                using f3 f2 f1 by (metis (no_types) \<open>shd (tsAbs\<cdot> (tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p)))) = shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))\<close> \<open>t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))\<close> a1 slen_scons)
            qed
          qed    
        qed
        show "#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
          using h1 h2 order.trans by blast
      qed
      then show ?case
        using trans_lnle mlscons.prems prop0_h2_2 by blast 
  qed

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