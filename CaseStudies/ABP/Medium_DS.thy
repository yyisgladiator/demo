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

fixrec newOracle_srcdups :: "'a stream \<rightarrow> 'a stream \<rightarrow> bool stream" where
"newOracle_srcdups\<cdot>\<bottom>\<cdot>bs = \<bottom> " |
"newOracle_srcdups\<cdot>as\<cdot>\<bottom> = \<bottom> " |
"newOracle_srcdups\<cdot>((up\<cdot>a) && as)\<cdot>((up\<cdot>b) && bs) = 
  (if a=b then (updis True) && newOracle_srcdups\<cdot>as\<cdot>bs
   else (updis False) && newOracle_srcdups\<cdot>((up\<cdot>a) && as)\<cdot>bs)"

lemma newOra_srcdups_t:
  "s1 \<noteq> \<epsilon> \<Longrightarrow> s2 \<noteq> \<epsilon> \<Longrightarrow> shd s1 = shd s2 \<Longrightarrow> newOracle_srcdups\<cdot>s1\<cdot>s2 = \<up>True \<bullet> newOracle_srcdups\<cdot>(srt\<cdot>s1)\<cdot>(srt\<cdot>s2)"
  by (metis lscons_conv newOracle_srcdups.simps(3) surj_scons)

lemma newOra_srcdups_f:
  "s1 \<noteq> \<epsilon> \<Longrightarrow> s2 \<noteq> \<epsilon> \<Longrightarrow> shd s1 \<noteq> shd s2 \<Longrightarrow> newOracle_srcdups\<cdot>s1\<cdot>s2 = \<up>False \<bullet> newOracle_srcdups\<cdot>(s1)\<cdot>(srt\<cdot>s2)"
  by (smt inject_scons lscons_conv newOracle_srcdups.simps(3) surj_scons)

lemma ora_t_ex: "\<exists>ora1. P (\<up>True\<bullet>ora1) \<Longrightarrow> \<exists>ora2. P ora2"
  by auto    
    
lemma ora_f_ex: "\<exists>ora1. P (\<up>False\<bullet>ora1) \<Longrightarrow> \<exists>ora2. P ora2"
  by auto     
    
 (*lemma newOra_srcdups_ex_h:
  "s1 = sMed\<cdot>s2\<cdot>ora1 \<Longrightarrow> \<exists>ora2. srcdups\<cdot>(s1) = sMed\<cdot>(srcdups\<cdot>s2)\<cdot>ora2"
  proof(induction ora1 arbitrary: s1 s2 rule: ind)
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case
      by (metis smed_bot2 strict_srcdups) 
  next
    case (3 a s)
    then show ?case
      apply (cases rule:scases [of s2],simp_all)
      apply (case_tac "a=True",simp)
      apply (case_tac "(sMed\<cdot>sa\<cdot>s) = \<epsilon>")
      apply (rule_tac x="\<up>True" in exI)
      apply (metis (no_types) sconc_snd_empty smed_bot2 smed_t srcdups_step strict_sdropwhile strict_srcdups) 
      apply (case_tac "sa = \<epsilon>",simp) 
      apply (case_tac "aa = shd sa")
      apply (case_tac "aa = shd (sMed\<cdot>sa\<cdot>s)") 
      apply (subst srcdups_fst2snd,simp,simp)
      apply (subst srcdups_fst2snd,simp,simp)
      apply blast
        apply (subst srcdups_nfst2snd,simp)  
        apply (simp add: srcdups_step) 
        apply (rule  ora_t_ex,simp)
        
     
      sorry
  qed  
  
  apply (rule_tac x="newOracle_srcdups\<cdot>(srcdups\<cdot>s1)\<cdot>(srcdups\<cdot>s2)" in exI)
  proof(induction "(srcdups\<cdot>s1)" arbitrary:  s1 s2 ora1 rule:ind) 
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case
      by simp
  next
    case (3 a s)
    then show ?case
      apply (case_tac "shd (srcdups\<cdot>s1) = shd (srcdups\<cdot>s2)")
      apply (simp add: newOra_srcdups_t)  
     
      sorry
  qed
   *)

lemma smed_t2: "s \<noteq> \<epsilon> \<Longrightarrow>  sMed\<cdot>s\<cdot>(\<up>True \<bullet> ora) = \<up>(shd s) \<bullet> sMed\<cdot>(srt\<cdot>s)\<cdot>ora"
  by (metis smed_t surj_scons)
  
lemma srt_srcdups: "srt\<cdot>(srcdups\<cdot>s) = srcdups\<cdot>(sdropwhile (\<lambda>x. x=(shd s))\<cdot>s)"
  by (metis srcdups_fst2snd srcdups_srt stream.sel_rews(2) strict_sdropwhile strict_srcdups)

fixrec drop_false_ora :: "'a discr \<rightarrow> 'a stream \<rightarrow> bool stream \<rightarrow> bool stream" where
"drop_false_ora\<cdot>c\<cdot>\<bottom>\<cdot>bs = \<bottom> " |
"drop_false_ora\<cdot>c\<cdot>as\<cdot>\<bottom> = \<bottom> " |
"drop_false_ora\<cdot>c\<cdot>((up\<cdot>a) && as)\<cdot>((up\<cdot>b) && bs) =
  (if c=a then drop_false_ora\<cdot>c\<cdot>as\<cdot>bs
   else ((up\<cdot>b) && bs))" 

lemma drop_false_ora_f: "drop_false_ora\<cdot>(Discr a)\<cdot>(\<up>a \<bullet> sa)\<cdot>(\<up>b \<bullet> sb) = drop_false_ora\<cdot>(Discr a)\<cdot>(sa)\<cdot>(sb)"
  by (simp add: conc2cons)

lemma drop_false_ora_t: "a \<noteq> as \<Longrightarrow> drop_false_ora\<cdot>(Discr a)\<cdot>(\<up>as \<bullet> sa)\<cdot>(sb) = sb"
  apply (rule scases [of sb],simp)
  by (simp add: conc2cons)

lemma drop_ora: assumes "s \<noteq> \<epsilon>"  "(sMed\<cdot>s\<cdot>ora) \<noteq> \<epsilon>" shows "shd s \<noteq> shd (sMed\<cdot>s\<cdot>ora) \<Longrightarrow> 
  sMed\<cdot>s\<cdot>ora = sMed\<cdot>(sdropwhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>(drop_false_ora\<cdot>(Discr(shd s))\<cdot>s\<cdot>ora)" 
  proof(induction s arbitrary: ora rule:ind)
    case 1
    then show ?case
      apply (rule adm_all)
      apply (rule admI)
      sorry
  next
    case 2
    then show ?case by simp
  next
    case (3 a s)
    then show ?case
      apply (cases rule: oracases[of ora]) 
      using assms apply simp
      using assms apply simp_all 
      apply (simp add: drop_false_ora_f)
      apply (case_tac "a =shd s",simp)
      by (smt drop_false_ora_t sdropwhile_f smed_bot1 strict_sdropwhile surj_scons)     
  qed

lemma smed_false:assumes "s \<noteq> \<epsilon>"  "(sMed\<cdot>s\<cdot>ora) \<noteq> \<epsilon>" "shd s \<noteq> shd (sMed\<cdot>s\<cdot>ora)" obtains ora2 where "sMed\<cdot>s\<cdot>ora = sMed\<cdot>(sdropwhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora2"
  using drop_ora assms by auto

lemma newOra_srcdups_h: " s \<noteq> \<epsilon> \<and> sMed\<cdot>s\<cdot>as \<noteq> \<epsilon> \<and>  shd s \<noteq> shd (sMed\<cdot>s\<cdot>as) \<Longrightarrow>
       srcdups\<cdot>(sMed\<cdot>s\<cdot>as) =
       sMed\<cdot>(srcdups\<cdot>(sdropwhile (\<lambda>x. x = shd s)\<cdot>s))\<cdot>
                  (newOracle_srcdups\<cdot>(srcdups\<cdot>(sMed\<cdot>s\<cdot>as))\<cdot>(srcdups\<cdot>(sdropwhile (\<lambda>x. x = shd s)\<cdot>s)))"
apply (induction s arbitrary: as rule:ind,simp_all)
apply (rule adm_all)
apply (rule adm_imp,simp)
apply (rule scases)
apply (rule admI)

sorry

lemma newOra_srcdups_h2: " s \<noteq> \<epsilon> \<Longrightarrow>
       sMed\<cdot>s\<cdot>as \<noteq> \<epsilon> \<Longrightarrow>
       a \<noteq> shd s \<Longrightarrow>
       srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>as) = sMed\<cdot>(\<up>a \<bullet> srcdups\<cdot>s)\<cdot>(newOracle_srcdups\<cdot>(srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>as))\<cdot>(\<up>a \<bullet> srcdups\<cdot>s))"
sorry

(*lemma induct_lem: "(\<And>s::'a stream. \<forall>(sa \<sqsubseteq> s). P sa \<Longrightarrow> P s) \<Longrightarrow> \<forall>(sa\<sqsubseteq>s). P sa"*)
lemma newOra_srcdups_ex:
  "\<exists> ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2"
   apply (induction ora1  arbitrary: msg rule: ind,simp_all)
   apply (rule adm_all)
   apply (rule admI)
   
   apply (rule_tac x="(newOracle_srcdups\<cdot>(srcdups\<cdot>(sMed\<cdot>x\<cdot>(\<Squnion>i. Y i)))\<cdot>(srcdups\<cdot>x))" in exI)
   oops            
              
lemma newOra_srcdups: 
  "srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>(newOracle_srcdups\<cdot>(srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora))\<cdot>(srcdups\<cdot>msg))"
(*  apply (induction ora  arbitrary: msg rule: ind,simp_all)
  apply (rule_tac x=msg in scases,simp)
  apply (case_tac "sa= \<epsilon>",simp)
  apply (case_tac "a = True",simp)
  apply (metis (no_types, lifting) lscons_conv newOracle_srcdups.simps(3) smed_bot1 smed_t srcdups_step strict_sdropwhile strict_srcdups sup'_def)
  apply (metis (full_types) lscons_conv newOracle_srcdups.simps(1) smed_bot1 smed_bot2 smed_f strict_srcdups sup'_def)
  apply (case_tac "(sMed\<cdot>sa\<cdot>s) = \<epsilon>")
  apply (case_tac "a = True",simp)
  apply (metis conc2cons newOracle_srcdups.simps(1) newOracle_srcdups.simps(3) smed_bot2 smed_t srcdups_step sup'_def)
  apply simp
  apply (case_tac "a = True",simp)
  apply (case_tac "shd sa = aa")
  apply (case_tac "shd (sMed\<cdot>sa\<cdot>s) = aa") 
  apply (simp add: srcdups_fst2snd)
  apply (simp add: srcdups_fst2snd srcdups_nfst2snd)
  apply (smt conc2cons newOra_srcdups_f newOracle_srcdups.simps(3) smed_f smed_t srcdups_fst2snd srcdups_nbot srcdups_shd2 srcdups_srt srcdups_step)
  apply (case_tac "shd (sMed\<cdot>sa\<cdot>s) = aa") 
  apply (simp add: srcdups_fst2snd srcdups_nfst2snd)
  apply (subst newOra_srcdups_t)
  using srcdups_nbot apply blast
  apply simp+
  *)


  apply (induction msg arbitrary: ora rule: ind, simp_all)
  apply (rule_tac ts=ora in oracases,simp)
  apply simp
  apply (case_tac "s= \<epsilon>")
  apply (simp add: newOra_srcdups_t) 
  apply (metis sconc_snd_empty smed_bot2 smed_t)
  apply (case_tac "(sMed\<cdot>s\<cdot>as) = \<epsilon>")
  apply (simp add: srcdups_step newOra_srcdups_t)
  apply (metis sconc_snd_empty smed_bot2 smed_t)
  apply (case_tac "a = shd s")
  apply (case_tac "a = shd (sMed\<cdot>s\<cdot>as)") 
  apply (subst srcdups_fst2snd,simp,simp)+   
  apply fastforce 
  apply (subst srcdups_nfst2snd,simp)
  apply (subst srcdups_fst2snd,simp,simp)
  apply (subst srcdups_nfst2snd,simp)  
  apply (subst srcdups_fst2snd,simp,simp)
  apply (subst newOra_srcdups_t,simp)
  using srcdups_nbot apply blast
  apply simp
  apply (simp add: srcdups_nbot smed_t2 srt_srcdups)
  using newOra_srcdups_h apply force
  apply (simp add: srcdups_nfst2snd)
  using newOra_srcdups_h2 apply force
  apply simp
  apply (case_tac "shd s = a")
  apply (metis newOracle_srcdups.simps(1) smed_bot1 smed_bot2 srcdups_eq strict_srcdups surj_scons)
  apply (simp add: srcdups_nfst2snd)
  apply (case_tac "s= \<epsilon>")
  apply (simp add: newOra_srcdups_t) 
  apply (case_tac "(sMed\<cdot>s\<cdot>as) = \<epsilon>")
  apply (simp add: srcdups_step newOra_srcdups_t)
  apply (case_tac "shd (sMed\<cdot>s\<cdot>as) = a")
  apply (metis newOra_srcdups_h2 srcdups_fst2snd) 
  apply (subst newOra_srcdups_f)
  by (simp add: srcdups_nbot,simp+)
   
lemma newOra_srcdups_obtains: obtains ora2 where "srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2"
  using newOra_srcdups by auto

(*
lemma sprojsnd_srcdups:
  "#(srcdups\<cdot>s) \<noteq> \<infinity> \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>s)) = #(srcdups\<cdot>s)
     \<Longrightarrow> srcdups\<cdot>(sprojsnd\<cdot>s) = sprojsnd\<cdot>(srcdups\<cdot>s)"
(*
  apply (induction s rule: ind, simp_all)
  apply (rule adm_imp, rule admI)
  apply (simp add: contlub_cfun_arg)
  apply (rule admI, auto)
  apply (simp add: contlub_cfun_arg)
*)
  proof(induction s rule: ind)
    case 1
    then show ?case
    proof (rule admI, auto)
      fix Y :: "nat \<Rightarrow> ('a \<times> 'b) stream"
      assume chy: "chain Y" and
         as1: "\<forall>i. #(srcdups\<cdot>(Y i)) \<noteq> \<infinity> \<longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>(Y i))) = #(srcdups\<cdot>(Y i)) \<longrightarrow> srcdups\<cdot>(sprojsnd\<cdot>(Y i)) = sprojsnd\<cdot>(srcdups\<cdot>(Y i))"
         and as2: "#(srcdups\<cdot>(\<Squnion>i::nat. Y i)) \<noteq> \<infinity>"
         and as3: "#(srcdups\<cdot>(sprojsnd\<cdot>(\<Squnion>i::nat. Y i))) = #(srcdups\<cdot>(\<Squnion>i::nat. Y i))"
         have h1: "\<And>i. #(srcdups\<cdot>(Y i)) \<noteq> \<infinity>"
           by (metis as2 chy inf_less_eq is_ub_thelub lnle_conv monofun_cfun_arg)
         have "\<And>i. #(srcdups\<cdot>(sprojsnd\<cdot>(Y i))) = #(srcdups\<cdot>(Y i))"  sorry
         thus "srcdups\<cdot>(sprojsnd\<cdot>(\<Squnion>i::nat. Y i)) = sprojsnd\<cdot>(srcdups\<cdot>(\<Squnion>i::nat. Y i))"
           by (smt as1 ch2ch_Rep_cfunR chy contlub_cfun_arg h1 lub_eq)
      qed
  next
    case 2
    then show ?case by simp
  next 
    case (3 a s)
    then show ?case
      apply (cases rule: scases [of s])
      apply (cases a,simp)
      apply (cases a,simp)
      apply (case_tac aa,simp) 
      apply (case_tac "b=ba")
      apply (case_tac "(aaa,b) = (ab,ba)")  
      apply simp_all
  by (metis antisym_conv2 inf_ub le2lnle order_refl slen_sprojsnd sprojsnd_scons sprojsnd_srcdups_slen)
  qed
*)
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
      apply (smt inject_scons smed_bot2 smed_f smed_t srcdups_eq surj_scons surj_scons)
      apply (smt less_lnsuc lnsuc_lnle_emb srcdups_nfst2snd srcdups_fst2snd slen_scons trans_lnle)
      by (metis (no_types, lifting) less_lnsuc srcdups_nfst2snd srcdups_fst2snd slen_scons trans_lnle) 
  qed              
    
lemma smed_sprojsnd: "sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p) = sMed\<cdot>(sprojsnd\<cdot>s)\<cdot>p" 
  by (simp add: sprojsnd_def smed_smap)

(*    
lemma prop4s_h3_h1: "a\<noteq>shd s \<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a\<bullet>srcdups\<cdot>s" 
  by (metis srcdups_neq srcdups_shd srcdups_srt strict_sdropwhile surj_scons)
    
lemma prop4s_h3_h2: "a = shd s \<Longrightarrow> s\<noteq>\<epsilon>\<Longrightarrow> srcdups\<cdot>(\<up>a \<bullet> s) = srcdups\<cdot>s"
  using srcdups_eq[of "shd s" "srt\<cdot>s"] surj_scons[of s] by auto    
    
lemma prop4s_h3_h3: "#(srcdups\<cdot>(sprojsnd\<cdot>(\<up>a))) = Fin 1"
  by (simp add: sprojsnd_def)
    
lemma prop4s_h3_h4: "s \<noteq> \<epsilon> \<Longrightarrow> shd s = a \<Longrightarrow>
    srcdups\<cdot>(\<up>(snd a) \<bullet> smap snd\<cdot>s) = srcdups\<cdot>(smap snd\<cdot>s)"
  by (simp add: smap_hd_rst)    
    
lemma prop4s_h3_h5: "sMed\<cdot>s\<cdot>as \<noteq> \<epsilon> \<Longrightarrow> shd (smap snd\<cdot>(sMed\<cdot>s\<cdot>as)) \<noteq> snd a \<Longrightarrow> 
    srcdups\<cdot>(\<up>(snd a) \<bullet> smap snd\<cdot>(sMed\<cdot>s\<cdot>as)) = \<up>(snd a) \<bullet> srcdups\<cdot>(smap snd\<cdot>(sMed\<cdot>s\<cdot>as))"
  by (simp add: prop4s_h3_h1)    
    
lemma prop4s_h3_h6: " #(srcdups\<cdot>(smap snd\<cdot>s)) \<noteq> \<infinity> \<Longrightarrow>  lnsuc\<cdot>(#(srcdups\<cdot>(smap snd\<cdot>(sMed\<cdot>s\<cdot>as)))) = #(srcdups\<cdot>(smap snd\<cdot>s)) \<Longrightarrow> false"
 oops

lemma prop4s_h3_h7: "s \<noteq> \<epsilon> \<Longrightarrow> shd (smap snd\<cdot>s) \<noteq> snd a \<Longrightarrow> 
    srcdups\<cdot>(\<up>(snd a) \<bullet> smap snd\<cdot>s) = \<up>(snd a) \<bullet> srcdups\<cdot>(smap snd\<cdot>s)"
  by (simp add: prop4s_h3_h1)   
    
lemma prop4s_h3_h8: "s \<noteq> \<epsilon> \<Longrightarrow> shd (smap snd\<cdot>s) =  snd a \<Longrightarrow>
    srcdups\<cdot>(\<up>(snd a) \<bullet> smap snd\<cdot>s) = srcdups\<cdot>(smap snd\<cdot>s)"
  by (simp add: smap_hd_rst)      
    
lemma prop4s_h3_h9: "#(srcdups\<cdot>s) \<noteq> \<infinity> \<Longrightarrow>
         #(srcdups\<cdot>(smap snd\<cdot>s)) = lnsuc\<cdot>(#(srcdups\<cdot>s)) \<Longrightarrow> False" 
proof -
  have "(srcdups\<cdot>(smap snd\<cdot>s)) = (srcdups\<cdot>(sprojsnd\<cdot>s))"
    by (simp add: sprojsnd_def)
  from this have "#(srcdups\<cdot>(smap snd\<cdot>s)) \<le> (#(srcdups\<cdot>s))"
    using sprojsnd_srcdups_slen
    by (metis slen_sprojsnd)
  from this show "#(srcdups\<cdot>s) \<noteq> \<infinity> \<Longrightarrow>
         #(srcdups\<cdot>(smap snd\<cdot>s)) = lnsuc\<cdot>(#(srcdups\<cdot>s)) \<Longrightarrow> False"
    using le2lnle less_le by fastforce  
  qed

lemma prop4s_h3_h10: " #(srcdups\<cdot>(smap snd\<cdot>s)) \<noteq> \<infinity> \<Longrightarrow>
          #(srcdups\<cdot>(smap snd\<cdot>(sMed\<cdot>s\<cdot>as))) = lnsuc\<cdot>(#(srcdups\<cdot>(smap snd\<cdot>s))) \<Longrightarrow> False"     
  proof -
  have h1: "(srcdups\<cdot>(smap snd\<cdot>(sMed\<cdot>s\<cdot>p))) = (srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p)))"
    by (simp add: sprojsnd_def)
  have h2: "(srcdups\<cdot>(smap snd\<cdot>s)) = (srcdups\<cdot>(sprojsnd\<cdot>s))"   
    by (simp add: sprojsnd_def)
  have "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) \<le> (#(srcdups\<cdot>(sprojsnd\<cdot>s)))"
    by(simp add: smed_sprojsnd srcdups_smed_h)
  from this h1 h2 show "#(srcdups\<cdot>(smap snd\<cdot>s)) \<noteq> \<infinity> \<Longrightarrow>
          #(srcdups\<cdot>(smap snd\<cdot>(sMed\<cdot>s\<cdot>as))) = lnsuc\<cdot>(#(srcdups\<cdot>(smap snd\<cdot>s))) \<Longrightarrow> False"
    by (metis inf_ub leD less_le ln_less smed_smap srcdups_smed_h)
qed
  
lemma prop4s_h3_h11: "#(srcdups\<cdot>s)\<noteq> \<infinity> \<Longrightarrow> lnsuc\<cdot>(#(srcdups\<cdot>(smap snd\<cdot>(sMed\<cdot>s\<cdot>as)))) = #(srcdups\<cdot>s) \<Longrightarrow>
    (#(srcdups\<cdot>(smap snd\<cdot>(sMed\<cdot>s\<cdot>as)))) = #(srcdups\<cdot>s) \<Longrightarrow> False"
  using ln_less lnless_def by fastforce  
    
lemma prop4s_h3_h12: "sprojsnd\<cdot>(sa \<bullet> sb) = sprojsnd\<cdot>sa \<bullet> sprojsnd\<cdot>sb"
  sorry
*)    


lemma prop4s_h3: assumes  "#(srcdups\<cdot>s) \<noteq> \<infinity>" "#({True} \<ominus> p) = \<infinity>" "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) = #(srcdups\<cdot>s)"  
       "#(srcdups\<cdot>(sprojsnd\<cdot>s))= #(srcdups\<cdot>s)" shows 
       "(srcdups\<cdot>s) = (srcdups\<cdot>(sMed\<cdot>s\<cdot>p))" 
  using assms proof (erule_tac contrapos_np)
  have h1: "srcdups\<cdot>s \<noteq> srcdups\<cdot>(sMed\<cdot>s\<cdot>p) \<Longrightarrow> #(srcdups\<cdot>s) \<noteq> \<infinity> \<Longrightarrow> #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<noteq> #(srcdups\<cdot>s)"
    apply (erule_tac contrapos_np,simp)
    by (metis newOra_srcdups_obtains smed_slen2s)
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
    
  (*      using assms proof(induction p arbitrary: s rule:ind)
        case 1
  then show ?case sorry
next
  case 2
  then show ?case by simp
next
  case (3 a ora)
  then show ?case
    apply (cases rule: scases [of s],simp)
    apply (case_tac "a =True",simp)  
    apply (case_tac "s=\<epsilon>",simp)  
    apply (case_tac "sMed\<cdot>s\<cdot>ora= \<epsilon>",simp) 
    apply (simp only: prop4s_h3_h3)
    apply (smt Fin_02bot Fin_Suc One_nat_def bot_is_0 inject_lnsuc sconc_snd_empty slen_empty_eq slen_scons srcdups_ex) 
    apply (simp add:sprojsnd_def) 
    apply (case_tac "shd s= aa")  
    
    apply (case_tac "shd (sMed\<cdot>s\<cdot>ora)\<noteq> aa") 
    apply (simp add: prop4s_h3_h1)
    apply (case_tac "shd (smap snd\<cdot>(sMed\<cdot>s\<cdot>ora)) = snd aa")
    apply (case_tac "shd (smap snd\<cdot>s) = snd aa")
    apply (metis (no_types, hide_lams) prop4s_h3_h8 srcdups_eq srcdups_shd2 surj_scons)
    apply (metis prop4s_h3_h4 prop4s_h3_h7 srcdupsimposs)
    apply (case_tac "shd (smap snd\<cdot>s) = snd aa")
      
      apply (simp add: srcdups_step)
    sorry 
qed*)
   (*   using assms proof(induction s arbitrary: p rule:ind)
       case 1
       then show ?case proof(rule adm_imp)
         have "adm (\<lambda>x.  #(srcdups\<cdot>x) = \<infinity>)"
           by simp
         then  show " adm (\<lambda>x. \<not> #(srcdups\<cdot>x) \<noteq> \<infinity>)" 
           by auto
          
         show " adm (\<lambda>x. \<forall>xa. #({True} \<ominus> xa) = \<infinity> \<longrightarrow> 
                     #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>x\<cdot>xa))) = #(srcdups\<cdot>x) \<longrightarrow> 
                     #(srcdups\<cdot>(sprojsnd\<cdot>x)) = #(srcdups\<cdot>x) \<longrightarrow> 
                     srcdups\<cdot>x = srcdups\<cdot>(sMed\<cdot>x\<cdot>xa))"
           apply(rule adm_all)
           apply(rule adm_imp)
           apply(simp)
           apply(rule adm_imp)  
           sorry  
         qed
     next
       case 2
       then show ?case by simp
     next
       case (3 a s)
       then show ?case 
         apply (case_tac "s = \<epsilon>")
         apply (cases rule: oracases,simp) 
         apply (metis (no_types, lifting) smed_bot1 smed_t)
          apply (metis (no_types, lifting) slen_empty_eq smed_bot1 smed_f  strict_sprojsnd strict_srcdups)      
           
         apply (case_tac "shd s= a")
         
         apply (cases rule: oracases)
         apply (simp add: prop4s_h3_h2)  
         apply simp  
         apply (case_tac "sMed\<cdot>s\<cdot>as= \<epsilon>") 
         apply (simp add: prop4s_h3_h3  prop4s_h3_h2)
         apply (metis Fin_02bot Fin_Suc bot_is_0 inject_lnsuc sconc_snd_empty slen_empty_eq 
                  srcdups_nbot srcdups_shd srt_decrements_length surj_scons)
         apply (case_tac "shd (sMed\<cdot>s\<cdot>as)= a")
         apply (simp add: prop4s_h3_h2)  
         apply (simp add: sprojsnd_def)
         apply (metis (no_types, lifting) smap_scons srcdups_eq surj_scons) 
         apply (simp add: prop4s_h3_h1)  
           apply (simp add: sprojsnd_def) 
           apply (case_tac "shd (smap snd\<cdot>(sMed\<cdot>s\<cdot>as)) = snd a")
         apply (smt prop4s_h3_h4 slen_empty_eq slen_smap srcdups_eq srcdups_shd2 surj_scons)
           apply (simp add: prop4s_h3_h4 prop4s_h3_h5)
           apply (simp add: srcdups_step)
           
         apply (meti prop4s_h3_h11)
         apply (simp add: sprojsnd_def) 
        apply (case_tac "shd (smap snd\<cdot>s) = snd a")
           apply (simp add: prop4s_h3_h4)
         apply (simp add: prop4s_h3_h4)
         apply (simp add: prop4s_h3_h1)
         apply (cases rule: oracases,simp)
          apply simp  
          apply (case_tac "sMed\<cdot>s\<cdot>as= \<epsilon>") 
           apply (simp add: prop4s_h3_h3)
         apply (metis Fin_02bot Fin_Suc bot_is_0 lnat.injects slen_empty_eq)
           apply (case_tac "shd (sMed\<cdot>s\<cdot>as)= a")
           apply (simp add: prop4s_h3_h2)
           apply (simp add: sprojsnd_def)
            apply (simp add: prop4s_h3_h4)
         apply (case_tac "shd (smap snd\<cdot>s) = snd a")
         apply (simp add: prop4s_h3_h8)
         using prop4s_h3_h9 apply blast
         apply (simp add: prop4s_h3_h1)
         apply (metis prop4s_h3_h10)
          apply (simp add: prop4s_h3_h1)
           apply (simp add: sprojsnd_def) 
         apply (case_tac "shd (smap snd\<cdot>s) = snd a")  
           apply (simp add: prop4s_h3_h8)
           apply (case_tac "shd (smap snd\<cdot>(sMed\<cdot>s\<cdot>as)) = snd a")
           apply (simp add: prop4s_h3_h8)
         using prop4s_h3_h9 apply blast
         using prop4s_h3_h9 apply blast
         apply (metis (no_types, lifting) lnat.sel_rews(2) prop4s_h3_h1 prop4s_h3_h10 prop4s_h3_h8 slen_scons)
          apply (simp add: sprojsnd_def) 
          apply (case_tac "shd (smap snd\<cdot>s) = snd a")
         using prop4s_h3_h8 prop4s_h3_h9 apply fastforce
         by (metis "3.prems"(1) fold_inf prop4s_h3_h1 prop4s_h3_h10 slen_scons)   
  qed  
*)
end