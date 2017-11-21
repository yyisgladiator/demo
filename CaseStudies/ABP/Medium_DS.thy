(*  Title:        Medium.thy
    Author:       Dennis Slotboom
    e-mail:       dennis.slotboom@rwth-aachen.de

    Description:  Medium Component of the ABP on Timed Streams
*)

chapter {* Medium of the Alternating Bit Protocol *}
                                                            
theory Medium_DS
imports "../../TStream" Medium

begin
default_sort countable

lemma dropwhile_shd_f: "shd s \<noteq> a \<Longrightarrow> sdropwhile (\<lambda>x. x = a)\<cdot>s = s"
  by (metis (full_types) sdropwhile_f strict_sdropwhile surj_scons)
     
lemma drop2med: "sdrop n\<cdot>s = sMed\<cdot>s\<cdot>((sntimes n (\<up>False)) \<bullet> ((\<up>True)\<infinity>))" 
  apply (induction n arbitrary: s)
  apply (simp add: smed_inftrue)
  apply (rule_tac x=s in scases)
  by simp_all

lemma dropwhile_inf_bot: "sdropwhile (\<lambda>x. x = a)\<cdot>\<up>a\<infinity> = \<epsilon>"
  proof -
  have h2:"\<forall>a. sdom\<cdot>\<up>a\<infinity> = {a}" by simp
  have "\<forall>a b s.(sdropwhile (\<lambda>x. x = a)\<cdot>(sinftimes (\<up>a))) \<noteq> \<up>b \<bullet> s"
    apply auto    
    apply (case_tac "b=a")
    using sdropwhile_resup apply blast
    by (metis (no_types) Un_absorb h2 insert_commute insert_is_Un sdom2un singleton_insert_inj_eq' srcdups_dom srcdups_step)
  then have "\<forall>a.(sdropwhile (\<lambda>x. x = a)\<cdot>(sinftimes (\<up>a))) = \<epsilon>"
    by (metis scases)
  thus ?thesis 
  by auto
  qed

lemma slen_dropwhile_takewhile: "sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> #(stakewhile (\<lambda>x. x = a)\<cdot>s) \<noteq> \<infinity>"
  apply (erule_tac contrapos_pp,simp)
  using stakewhile_sinftimesup [of a s] apply (simp)
  by (simp add: dropwhile_inf_bot)

lemma dropwhile2drop: "sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> \<exists>n .sdropwhile (\<lambda>x. x = a)\<cdot>s = sdrop n\<cdot>s"
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

lemma split_stream_rev: "s = stake n\<cdot>s \<bullet> sdrop n\<cdot>s " by simp

lemma szip_slen_conc: "#ora \<le> #sa \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora =  szip\<cdot>sa\<cdot>ora"
  apply (induction k arbitrary: ora sa sb,simp_all)
  apply (rule_tac x=sa in scases,simp_all)
  by (rule_tac x=ora in scases,simp_all)

lemma szip_slen_conc2: "#ora > #sa \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop k\<cdot>ora)"
  apply (induction k arbitrary: ora sa sb,simp_all)
  apply (rule_tac x=sa in scases,simp_all)
  by (rule_tac x=ora in scases,simp_all)

lemma add_sfilter_rev:
  "#x = Fin k \<Longrightarrow> sfilter t\<cdot>x \<bullet> sfilter t\<cdot>y = sfilter t\<cdot>(x \<bullet> y)" by (simp add: add_sfilter)

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

lemma sdropwhile_conc: assumes "#sa = Fin k" shows "sdropwhile (\<lambda>x. x = a)\<cdot>sa = \<epsilon> \<Longrightarrow> sdropwhile (\<lambda>x. x = a)\<cdot>(sa \<bullet> sb) = sdropwhile (\<lambda>x. x = a)\<cdot>sb"
  apply (induction sa arbitrary: a sb rule: finind,simp_all)
  using assms apply auto[1]
  apply (case_tac "aa=a",simp)
  by (metis (full_types) sdropwhile_f srcdups_srt srcdups_step srcdupsimposs2 stream.sel_rews(2) strict_srcdups)

lemma dropwhile_med: "\<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>s\<cdot>ora) = sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2"
  apply (case_tac "s= \<epsilon>",simp)
  apply (case_tac "(sMed\<cdot>s\<cdot>ora) = \<epsilon>",simp)
  using smed_bot2 apply blast 
  apply(case_tac "shd s \<noteq> a")
  apply(case_tac "shd (sMed\<cdot>s\<cdot>ora)  \<noteq> a")
  apply (simp add: dropwhile_shd_f,blast)
  apply (simp) 
  apply (metis dropwhile_shd_f dropwhile2smed smed2med,simp)
  apply (subst stakewhileDropwhile_rev [of s "(\<lambda>x. x = a)"])
  using smed_conc [of "stakewhile (\<lambda>x. x = a)\<cdot>s" "sdropwhile (\<lambda>x. x = a)\<cdot>s" ora] apply auto
  apply (case_tac "#(sMed\<cdot>(stakewhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora) = \<infinity>")
  apply (metis sconc_fst_inf smed_bot2 smed_dtw)
  by (metis sdropwhile_conc smed_dtw ninf2Fin dropwhile2smed smed2med)

lemma med_dropwhile_t: "(sMed\<cdot>sa\<cdot>as) \<noteq> \<epsilon> \<Longrightarrow> shd (sMed\<cdot>sa\<cdot>as) = a \<Longrightarrow> srcdups\<cdot>(sMed\<cdot>sa\<cdot>as) = \<up>a \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>sa\<cdot>as))"
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
 
lemma newOra_srcdups_ex: assumes "#(srcdups\<cdot>msg) = Fin n" shows "\<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2"
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

lemma prop4s_h3: assumes  "#(srcdups\<cdot>s) \<noteq> \<infinity>" "#({True} \<ominus> p) = \<infinity>" "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) = #(srcdups\<cdot>s)"  
       "#(srcdups\<cdot>(sprojsnd\<cdot>s))= #(srcdups\<cdot>s)" shows 
       "(srcdups\<cdot>s) = (srcdups\<cdot>(sMed\<cdot>s\<cdot>p))" 
  using assms proof (erule_tac contrapos_np)
  have h1: "srcdups\<cdot>s \<noteq> srcdups\<cdot>(sMed\<cdot>s\<cdot>p) \<Longrightarrow> #(srcdups\<cdot>s) = \<infinity> \<or> #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<noteq> #(srcdups\<cdot>s)"
    by (metis infI newOra_srcdups_ex smed_slen2s)   
  have "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) \<noteq> #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<Longrightarrow>  #(srcdups\<cdot>(sprojsnd\<cdot>s)) \<noteq> #(srcdups\<cdot>s)"
    by (metis (no_types) antisym_conv assms(3) slen_sprojsnd sprojsnd_srcdups_slen srcdups_smed_h) 
  then have "#({True} \<ominus> p) = \<infinity> \<Longrightarrow>
    #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) = #(srcdups\<cdot>s) \<Longrightarrow>
    #(srcdups\<cdot>(sprojsnd\<cdot>s)) = #(srcdups\<cdot>s) \<Longrightarrow> srcdups\<cdot>s \<noteq> srcdups\<cdot>(sMed\<cdot>s\<cdot>p) \<Longrightarrow> #(srcdups\<cdot>s) \<noteq> #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<Longrightarrow> #(srcdups\<cdot>s) = \<infinity>"
    by simp   
  from this h1 show "#({True} \<ominus> p) = \<infinity> \<Longrightarrow>
    #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) = #(srcdups\<cdot>s) \<Longrightarrow>
    #(srcdups\<cdot>(sprojsnd\<cdot>s)) = #(srcdups\<cdot>s) \<Longrightarrow> srcdups\<cdot>s \<noteq> srcdups\<cdot>(sMed\<cdot>s\<cdot>p) \<Longrightarrow> #(srcdups\<cdot>s) = \<infinity>"
    by fastforce
  qed  
    
end