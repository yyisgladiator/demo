(*  Title:        Medium.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Medium Component of the ABP on Timed Streams
*)

chapter {* Medium of the Alternating Bit Protocol *}
                                                            
theory Medium
imports TStream sMed

begin
default_sort countable

(* ----------------------------------------------------------------------- *)
section {* definition *}
(* ----------------------------------------------------------------------- *)

text{* Timed version of a medium, that loses messages. *}
definition tsMed :: "'a tstream \<rightarrow> bool stream \<rightarrow> 'a tstream" where
"tsMed \<equiv> \<Lambda> msg ora. tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"


(* ----------------------------------------------------------------------- *)
subsection {* basic properties of tsMed *}
(* ----------------------------------------------------------------------- *)

text{* "Lossy" medium that gets messages and an oracle and will transmit the k-th message if
       the k-th element in the oracle is True, otherwise the message will be discarded. *}
lemma tsmed_insert: "tsMed\<cdot>msg\<cdot>ora = tsProjFst\<cdot>(tsFilter {x. snd x}\<cdot>(tsZip\<cdot>msg\<cdot>ora))"
  by (simp add: tsMed_def)
                                              
text{* The medium is strict. *}
lemma tsmed_strict [simp]: 
  "tsMed\<cdot>\<bottom>\<cdot>\<epsilon> = \<bottom>"
  "tsMed\<cdot>msg\<cdot>\<epsilon> = \<bottom>"
  "tsMed\<cdot>\<bottom>\<cdot>ora = \<bottom>"
  by (simp add: tsMed_def)+

text{* If the first element in the oracle is True then the current message will be transmitted. *}
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

text{* If the first element in the oracle is False then the current message will not be transmitted. *}
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

text{* Ticks in the message stream will be ignored. *}
lemma tsmed_delayfun: 
  assumes "ora\<noteq>\<epsilon>" 
  shows "tsMed\<cdot>(delayFun\<cdot>msg)\<cdot>ora = delayFun\<cdot>(tsMed\<cdot>msg\<cdot>ora)"
  using assms by (simp add: tsMed_def tszip_delayfun tsfilter_delayfun tsprojfst_delayfun)

text{* Only if nothing is sent nothing will be transmitted. *}
lemma tsmed_nbot [simp]: 
  assumes "msg\<noteq>\<bottom>" 
    and "#ora=\<infinity>" 
  shows "tsMed\<cdot>msg\<cdot>ora \<noteq> \<bottom>"
  using assms by (simp add: tsmed_insert)

text {* As many ticks will be transmitted as were sent. *}
lemma tsmed_tstickcount [simp]: 
  assumes "#ora = \<infinity>" 
  shows "#\<surd>(tsMed\<cdot>msg\<cdot>ora) = #\<surd>msg"
  using assms by (simp add: tsmed_insert)

text {* If only infinite ticks will be sent only infinite ticks will be transmitted. *}
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

text {* Medium without oracle will transmit all messages and ticks. *}
lemma tsmed_inftrue [simp]: "tsMed\<cdot>msg\<cdot>((\<up>True) \<infinity>) = msg"
  proof (induction msg)
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
      by (metis lscons_conv sinftimes_unfold stream.con_rews(2) 
          tsmed_delayfun up_defined)
  next
    case (mlscons msg t)
    then show ?case 
      by (metis lscons_conv sinftimes_unfold slen_sinftimes strict_icycle
          tsmed_mlscons_true tsmed_strict(2))
  qed

text {* Not every message will be transmitted forcibly. *}    
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

text{* Removing all the ticks after transmission through a timed medium yields the same result as
       removing all the ticks before transmission through an untimed medium. *}
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

text{* If infinitely many messages are sent, infinitely many messages will be transmitted. *}
lemma tsmed_tsabs_slen_inf [simp]:
  assumes "#({True} \<ominus> ora) = \<infinity>" 
    and "#(tsAbs\<cdot>msg) = \<infinity>"
  shows "#(tsAbs\<cdot>(tsMed\<cdot>msg\<cdot>ora)) = \<infinity>"
  by (metis assms(1) assms(2) sfilterl4 smed_slen_inf tsmed_tsabs)

text{* The transmitted messages are a subset of the messages that are meant to be transmitted. *}
lemma tsmed_tsdom: 
  assumes "#ora=\<infinity>"
  shows "tsDom\<cdot>(tsMed\<cdot>msg\<cdot>ora) \<subseteq> tsDom\<cdot>msg"
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
subsection {* additional properties of tsMed *}
(* ----------------------------------------------------------------------- *)

text{* If doesn't matter if a function is applied to the messages before or after 
       transmission through the medium. *}
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
      by(simp add: tsmed_insert lscons_conv)
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
      by (simp add: lscons_conv tsmed_insert)
  qed

text {* Two mediums can be reduced to one medium. *}
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

text {* Two mediums with fairness requirement can be reduced to one medium with fairness requirement. *}
lemma tsmed2infmed: 
  assumes "#({True} \<ominus> ora1)=\<infinity>" 
    and "#({True} \<ominus> ora2)=\<infinity>" 
  obtains ora3 where "tsMed\<cdot>(tsMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = tsMed\<cdot>msg\<cdot>ora3" 
    and "#({True} \<ominus> ora3)=\<infinity>"
  by (meson assms(1) assms(2) newora_fair sfilterl4 tsmed2med)
   
lemma prop0_h2: 
  assumes "#p=\<infinity>"
  shows"#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>b\<bullet>p)))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<bullet>p))))"
  proof (cases "b", simp)
    show "\<not> b \<Longrightarrow> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>b \<bullet> p)))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> p))))"
      proof (induction ts)
        case adm
        then show ?case
          proof (rule adm_imp, simp)
            have "\<And>Y. chain Y \<Longrightarrow> \<forall>i. #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(\<up>b \<bullet> p))))
              \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(\<up>True \<bullet> p)))) 
              \<Longrightarrow> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(\<Squnion>i. Y i)\<cdot>(\<up>b \<bullet> p)))) 
              \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(\<Squnion>i. Y i)\<cdot>(\<up>True \<bullet> p))))"
              by (simp add: contlub_cfun_arg assms contlub_cfun_fun lub_mono2)
            thus "adm (\<lambda>x. #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>x\<cdot>(\<up>b \<bullet> p)))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>x\<cdot>(\<up>True \<bullet> p)))))"
              by (rule admI)
          qed
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
          proof (simp add: f1)
            show "#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>p))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>(\<up>True \<bullet> p))))"
              by (metis assms bot_is_0 lnle_def lscons_conv minimal mlscons.hyps prop0_h sconc_fst_empty 
                  slen_empty_eq strict_srcdups tsabs_bot tsabs_mlscons tsmed_mlscons_true)
          qed
      qed
  qed

lemma prop0_h2_2: 
  assumes "#p=\<infinity>"
  shows"#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>p))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<bullet>(srt\<cdot>p)))))"
  using prop0_h2[of "srt\<cdot>p" ts "shd p"]
  by (metis Inf'_neq_0 assms fold_inf inject_lnsuc slen_empty_eq srt_decrements_length surj_scons)
  
lemma prop0_h3_h:"tsMed\<cdot>ts\<cdot>p\<noteq>\<bottom> \<Longrightarrow> tsAbs\<cdot>(updis t &&\<surd> tsMed\<cdot>ts\<cdot>p) = \<up>t \<bullet> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>p))"
  by (simp add: lscons_conv tsabs_mlscons)

lemma chain_lub_shd: assumes Y_chain: "chain Y" and chain_elem_nbot: "Y i \<noteq> \<epsilon>" 
  shows "shd (Y i) = shd (\<Squnion>i. Y i)"
  using Y_chain below_shd chain_elem_nbot is_ub_thelub by auto

lemma tsmed_shd: assumes "#ora1=\<infinity>" and "#ora2=\<infinity>"
  shows "shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(updis True && ora1))) = shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(updis True && ora2)))"
  using assms
  proof (induction ts)
    case adm
    then show ?case
      proof (rule adm_imp)
        show "adm (\<lambda>x. #ora1 \<noteq> \<infinity>)"
          by simp
      next
        show "adm (\<lambda>x. #ora2 = \<infinity> \<longrightarrow> 
              shd (tsAbs\<cdot>(tsMed\<cdot>x\<cdot>(updis True && ora1))) = shd (tsAbs\<cdot>(tsMed\<cdot>x\<cdot>(updis True && ora2))))"
          proof(rule adm_imp)
            show "adm (\<lambda>x. #ora2 \<noteq> \<infinity>)"
              by simp
          next
            show "adm (\<lambda>x. shd (tsAbs\<cdot>(tsMed\<cdot>x\<cdot>(updis True && ora1))) 
                             = shd (tsAbs\<cdot>(tsMed\<cdot>x\<cdot>(updis True && ora2))))"
              proof (rule admI)
                fix Y :: "nat \<Rightarrow> 'c tstream"
                assume Y_chain: "chain Y"
                assume adm_hyp: "\<forall>i. shd (tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora1))) 
                               = shd (tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora2)))"
                have tsmed_ora1_chain: "chain (\<lambda>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora1)))"
                  by (simp add: Y_chain)
                have tsmed_ora2_chain: "chain (\<lambda>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora2)))"
                  by (simp add: Y_chain)
                have tsmed_chains_shd_eq: "shd (\<Squnion>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora1))) 
                                          = shd (\<Squnion>i. tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(updis True && ora2)))"
                  using chain_lub_shd
                  by (metis (no_types, lifting) adm_hyp lub_eq_bottom_iff tsmed_ora1_chain 
                      tsmed_ora2_chain)
                then show "shd (tsAbs\<cdot>(tsMed\<cdot>(\<Squnion>i. Y i)\<cdot>(updis True && ora1))) 
                             = shd (tsAbs\<cdot>(tsMed\<cdot>(\<Squnion>i. Y i)\<cdot>(updis True && ora2)))"
                  by (simp add: Y_chain contlub_cfun_fun contlub_cfun_arg)
              qed
          qed
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

lemma prop0_h2_ind_h: 
  assumes "#p=\<infinity>"
  shows"#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>b \<bullet> p)))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<bullet>p))))"
  proof(cases "b")
    case True
    then show ?thesis
      by simp
  next
    case False
    then show ?thesis
      proof(induction ts)
        case adm
        then show ?case
          proof(rule adm_imp,simp)
            have thesis_simp: "\<And>Y. chain Y \<Longrightarrow> \<forall>i. #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(\<up>b \<bullet> p))))
              \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>(\<up>True \<bullet> p)))) \<Longrightarrow>
              #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>(\<Squnion>i. Y i)\<cdot>(\<up>b \<bullet> p))))
              \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>(\<Squnion>i. Y i)\<cdot>(\<up>True \<bullet> p))))"
              by (simp add: contlub_cfun_arg assms contlub_cfun_fun lub_mono2)
            thus "adm (\<lambda>x. #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>x\<cdot>(\<up>b \<bullet> p))))
              \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>x\<cdot>(\<up>True \<bullet> p)))))"
              by (rule admI)
          qed
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
          by (metis f1 assms lscons_conv mlscons.hyps prop0_h prop0_h3_h tsmed_mlscons_true tsmed_nbot)
      qed 
  qed
        
lemma prop0_h3: 
  "#p=\<infinity> \<Longrightarrow> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>p))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True\<infinity>))))"
  proof (induction ts arbitrary: p)
    case adm
    then show ?case
      proof (rule adm_all, rule adm_imp, simp)
        have thesis_simp: "\<And>x Y. chain Y \<Longrightarrow>
          \<forall>i. #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>x))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(Y i)\<cdot>\<up>True\<infinity>))) \<Longrightarrow>
          #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(\<Squnion>i. Y i)\<cdot>x))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(\<Squnion>i. Y i)\<cdot>\<up>True\<infinity>)))"
          by (simp add: contlub_cfun_fun contlub_cfun_arg lub_mono2)
        thus "\<And>x. adm (\<lambda>xa. #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>xa\<cdot>x))) \<le> #(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>xa\<cdot>\<up>True\<infinity>))))"
          by (rule admI)
      qed
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
      have g1: "p \<noteq> \<epsilon>"
        using mlscons.prems by force
      then have g2: "lnsuc\<cdot>(#(srt\<cdot>p)) = \<infinity>"
        by (metis (no_types) mlscons.prems slen_scons surj_scons)
      then have g3: "tsAbs\<cdot>ts \<noteq> \<epsilon>"
        using a1 by (metis bot_is_0 fold_inf inject_lnsuc leD lnless_def minimal slen_empty_eq tsmed_tsabs_slen)
      then show ?thesis
        using a2 by (metis (no_types) slen_scons srcdups_neq surj_scons tsmed_inftrue)
    qed
    have "#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>(\<up>True\<bullet>(srt\<cdot>p)))))\<le>#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>(updis t &&\<surd> ts)\<cdot>\<up>True\<infinity>)))"
      proof (simp only: h1 h2, subst prop0_h3_h)
        show "tsMed\<cdot>ts\<cdot>(srt\<cdot>p) \<noteq> \<bottom>"
          by (metis Inf'_neq_0 fold_inf inject_lnsuc mlscons.hyps mlscons.prems only_empty_has_length_0 srt_decrements_length tsmed_nbot)
        show "#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)))) \<le> 
          #(srcdups\<cdot>(tsAbs\<cdot>(updis t &&\<surd> tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
          proof (subst prop0_h3_h)
            show "tsMed\<cdot>ts\<cdot>\<up>True\<infinity> \<noteq> \<bottom>"
              by (simp add: mlscons.hyps)
            show "#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)))) \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
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
                        then have g4: "#(srcdups\<cdot>(tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)))) 
                          \<le> #(srcdups\<cdot> (\<up>t \<bullet> tsAbs\<cdot> (tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
                          using srt_len dual_order.trans mlscons.IH by blast
                        then show "#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))) 
                          \<le> #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
                          using a2 a1
                          proof -
                            have g5: "\<not> #(srcdups\<cdot> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))) < 
                              #(srcdups\<cdot> (\<up>t \<bullet> tsAbs\<cdot> (tsMed\<cdot>ts\<cdot> (\<up>True \<bullet> srt\<cdot> (srt\<cdot>p)))))"
                              by (metis (no_types) Inf'_neq_0 srt_len a1 a2 leD mlscons.IH 
                                  only_empty_has_length_0 slen_scons srcdups_eq surj_scons)
                            then show ?thesis
                              by (meson h10 le_less_trans not_le_imp_less)
                          qed
                      next
                        case False
                        assume a1: "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))) \<noteq> \<epsilon>"
                        assume a2: "t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))"
                        have g6: "tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>) \<noteq>\<epsilon>"
                          by (metis Inf'_neq_0 srt_len a1 leD lnless_def lnzero_def minimal 
                              slen_empty_eq slen_scons srt_decrements_length 
                              tsmed_inftrue tsmed_tsabs_slen)
                        then have g7: "shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p)))) = 
                          shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))"
(* TODO *)
                          by (smt a1 fold_inf inject_lnsuc lscons_conv mlscons.hyps sinftimes_unfold 
                              slen_empty_eq slen_sinftimes srcdups_shd srt_decrements_length srt_len 
                              strict_icycle surj_scons tsmed_inftrue tsmed_srcdups_shd tsmed_strict(2))
                        then have g8: "t \<noteq> shd (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))"
                          using a2 by simp
                        then show "#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p))))) \<le> 
                          #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
                          proof -
                            have f1: "lnsuc\<cdot> (#(srcdups\<cdot> (tsAbs\<cdot> (tsMed\<cdot>ts\<cdot>(\<up>True \<bullet> srt\<cdot>(srt\<cdot>p)))))) \<le> 
                              lnsuc\<cdot> (#(srcdups\<cdot> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))))"
                              by (metis (no_types) Inf'_neq_0 srt_len lnsuc_lnle_emb mlscons.IH 
                                  only_empty_has_length_0 slen_scons surj_scons)
                            have f2: "\<forall>s. s = \<epsilon> \<or> \<up>(shd s::'a) \<bullet> srt\<cdot>s = s"
                              by (metis surj_scons)
                            have f3: "\<forall>a aa s. (a::'a) = aa \<or> srcdups\<cdot>(\<up>a \<bullet> \<up>aa \<bullet> s) = 
                              \<up>a \<bullet> srcdups\<cdot>(\<up>aa \<bullet> s)"
                              by (meson srcdups_neq)
                            then have f4: "srcdups\<cdot> (\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)) = 
                              \<up>t \<bullet> srcdups\<cdot> (tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>))"
                              using g8 srcdups_nfst2snd by blast                            
                            then show ?thesis
                              using a2 f1 srcdups_nfst2snd by force                              
                          qed
                      qed    
                  qed
                show "#(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>(srt\<cdot>p)))) \<le> 
                  #(srcdups\<cdot>(\<up>t \<bullet> tsAbs\<cdot>(tsMed\<cdot>ts\<cdot>\<up>True\<infinity>)))"
                  using h1 h2 order.trans by blast
              qed
          qed
      qed
    then show ?case
      using trans_lnle mlscons.prems prop0_h2_2 by blast 
  qed

(* ----------------------------------------------------------------------- *)
section {* tsMedium lemmata *}
(* ----------------------------------------------------------------------- *)  

definition tsMedium :: "('a tstream \<rightarrow> 'a tstream) set" where
"tsMedium \<equiv> { (\<Lambda> ts. tsMed\<cdot>ts\<cdot>ora) | ora. #({True} \<ominus> ora) = \<infinity> }"

lemma ora_exists: "#({a} \<ominus> (\<up>a \<infinity>)) = \<infinity>"
  by simp
    
lemma tsmed_exists: "(\<Lambda> ts. tsMed\<cdot>ts\<cdot>(\<up>True \<infinity>)) \<in> tsMedium"
  proof- 
    have thesis_simp: "(\<Lambda> ts. tsMed\<cdot>ts\<cdot>\<up>True\<infinity>) \<in> {\<Lambda> ts. tsMed\<cdot>ts\<cdot>ora |ora. #({True} \<ominus> ora) = \<infinity>}"
      using ora_exists by blast
    thus ?thesis
      by (subst tsMedium_def)
  qed
    
lemma tsmedium_nempty [simp]: "tsMedium \<noteq> {}"
  by (metis empty_iff tsmed_exists)

end