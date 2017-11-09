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

fixrec newOra_h :: "('a \<times> bool) stream \<rightarrow> bool stream" where
"newOra_h\<cdot>\<epsilon> = \<epsilon>" |
"newOra_h\<cdot>(up\<cdot>c && \<epsilon>) = up\<cdot>(snd c) && \<epsilon>" |
"newOra_h\<cdot>((updis c1) && (updis c2) && cs) = 
  (if ((fst c1) \<noteq> (fst c2)) then (updis (snd c1)) && newOra_h\<cdot>((updis c2) && cs)
   else (updis True) && newOra_h\<cdot>(sdropwhile (\<lambda> z. fst z = fst c1)\<cdot>cs))" 

definition newOra :: "'a stream \<rightarrow> bool stream \<rightarrow> bool stream" where
"newOra\<cdot>as\<cdot>bs \<equiv> newOra_h\<cdot>(srcdups\<cdot>(szip\<cdot>as\<cdot>bs))" 

lemma newOra_srcdups_t:
  "s1 \<noteq> \<epsilon> \<Longrightarrow> s2 \<noteq> \<epsilon> \<Longrightarrow> shd s1 = shd s2 \<Longrightarrow> newOracle_srcdups\<cdot>s1\<cdot>s2 = \<up>True \<bullet> newOracle_srcdups\<cdot>(srt\<cdot>s1)\<cdot>(srt\<cdot>s2)"
  by (metis lscons_conv newOracle_srcdups.simps(3) surj_scons)

lemma newOra_srcdups_f:
  "s1 \<noteq> \<epsilon> \<Longrightarrow> s2 \<noteq> \<epsilon> \<Longrightarrow> shd s1 \<noteq> shd s2 \<Longrightarrow> newOracle_srcdups\<cdot>s1\<cdot>s2 = \<up>False \<bullet> newOracle_srcdups\<cdot>(s1)\<cdot>(srt\<cdot>s2)"
  by (smt inject_scons lscons_conv newOracle_srcdups.simps(3) surj_scons)

lemma smed_t2: "s \<noteq> \<epsilon> \<Longrightarrow>  sMed\<cdot>s\<cdot>(\<up>True \<bullet> ora) = \<up>(shd s) \<bullet> sMed\<cdot>(srt\<cdot>s)\<cdot>ora"
  by (metis smed_t surj_scons)
  
lemma srt_srcdups: "srt\<cdot>(srcdups\<cdot>s) = srcdups\<cdot>(sdropwhile (\<lambda>x. x=(shd s))\<cdot>s)"
  by (metis srcdups_fst2snd srcdups_srt stream.sel_rews(2) strict_sdropwhile strict_srcdups)

lemma srcdups_step_srt:"s\<noteq> \<epsilon> \<Longrightarrow> (srcdups\<cdot>s) =\<up>(shd s) \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x=(shd s))\<cdot>s)"
  by (metis (full_types) srcdups_srt srcdups_step srt_srcdups surj_scons)

(*
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
*)
lemma newOra_srcdups_h: " s \<noteq> \<epsilon> \<and> sMed\<cdot>s\<cdot>as \<noteq> \<epsilon> \<and>  shd s \<noteq> shd (sMed\<cdot>s\<cdot>as) \<Longrightarrow>
       srcdups\<cdot>(sMed\<cdot>s\<cdot>as) =
       sMed\<cdot>(srcdups\<cdot>(sdropwhile (\<lambda>x. x = shd s)\<cdot>s))\<cdot>
                  (newOracle_srcdups\<cdot>(srcdups\<cdot>(sMed\<cdot>s\<cdot>as))\<cdot>(srcdups\<cdot>(sdropwhile (\<lambda>x. x = shd s)\<cdot>s)))"
apply (induction s arbitrary: as rule:ind,simp_all)
apply (rule adm_all)
apply (rule adm_imp,simp)
apply (rule admI)

oops

lemma newOra_srcdups_h2: " s \<noteq> \<epsilon> \<Longrightarrow>
       sMed\<cdot>s\<cdot>as \<noteq> \<epsilon> \<Longrightarrow>
       a \<noteq> shd s \<Longrightarrow>
       srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>as) = sMed\<cdot>(\<up>a \<bullet> srcdups\<cdot>s)\<cdot>(newOracle_srcdups\<cdot>(srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>as))\<cdot>(\<up>a \<bullet> srcdups\<cdot>s))"
oops
(*
lemma induct_lem: "(\<And>s::'a stream. \<forall>sb. \<exists>sa. s = sa \<bullet> sb \<Longrightarrow> P sb \<Longrightarrow> P s) \<Longrightarrow> \<forall>sb. \<exists>sa. s = sa \<bullet> sb \<Longrightarrow> P sb"
apply(induct s)
apply(rule adm_imp,simp)
apply(rule adm_imp)
apply(rule admI)
apply (rule adm_all)
*)


lemma newOra_srcdups2: 
  "srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>(srcdupsOra\<cdot>(sMed\<cdot>msg\<cdot>ora))"
  apply (simp add: sMed_def)

  apply (induction ora  arbitrary: msg rule: ind,simp)
  apply (simp add: srcdupsOra_def)
  apply (rule_tac x=msg in scases,simp)
  apply (case_tac "sa= \<epsilon>",simp)
  apply (case_tac "a = True",simp)
  apply metis (no_types, lifting) lscons_conv newOracle_srcdups.simps(3) smed_bot1 smed_t srcdups_step strict_sdropwhile strict_srcdups sup'_def)
  apply metis (full_types) lscons_conv newOracle_srcdups.simps(1) smed_bot1 smed_bot2 smed_f strict_srcdups sup'_def)
  apply (case_tac "(sMed\<cdot>sa\<cdot>s) = \<epsilon>")
  apply (case_tac "a = True",simp)
  apply metis conc2cons newOracle_srcdups.simps(1) newOracle_srcdups.simps(3) smed_bot2 smed_t srcdups_step sup'_def)
  apply simp
  apply (case_tac "a = True",simp)
  apply (case_tac "shd sa = aa")
  apply (case_tac "shd (sMed\<cdot>sa\<cdot>s) = aa") 
  apply (simp add: srcdups_fst2snd)
  apply (simp add: srcdups_fst2snd srcdups_nfst2snd)
  apply smt conc2cons newOra_srcdups_f newOracle_srcdups.simps(3) smed_f smed_t srcdups_fst2snd srcdups_nbot srcdups_shd2 srcdups_srt srcdups_step)
  apply (case_tac "shd (sMed\<cdot>sa\<cdot>s) = aa") 
  apply (simp add: srcdups_fst2snd srcdups_nfst2snd)
  oops       
     
lemma dropwhile_med: "\<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>s\<cdot>ora1) = sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2"
sorry

lemma ora_t_ex: "\<exists>ora1. P (\<up>True\<bullet>ora1) \<Longrightarrow> \<exists>ora2. P ora2"
  by auto    
    
lemma ora_f_ex: "\<exists>ora1. P (\<up>False\<bullet>ora1) \<Longrightarrow> \<exists>ora2. P ora2"
  by auto     
 
lemma newOra_srcdups_ex: assumes "#(srcdups\<cdot>msg) = Fin n" shows "\<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2"
   apply (induction "srcdups\<cdot>msg"  arbitrary: msg  ora1 rule: finind)
   using assms apply simp
   apply (metis smed_bot1 srcdups_nbot)
   apply (rule_tac x=msg in scases,simp)
   apply (simp add: srcdups_step)
   apply (rule_tac ts=ora1 in oracases,simp_all)
   using smed_bot2 apply blast
   apply (rule ora_t_ex)
   apply (simp add: srcdups_step)
   apply (subst dropwhile_med)
   sorry


lemma newOra_srcdups: 
  "srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>(newOracle_srcdups\<cdot>(srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora))\<cdot>(srcdups\<cdot>msg))"
   proof (induction "srcdups\<cdot>msg"  arbitrary: msg  ora rule: ind)
     case 1
     then show ?case
       apply (rule adm_all,rule adm_imp)
       sorry
   next
     case 2
     then show ?case
       by (metis smed_bot1 srcdups_nbot)
   next
     case (3 a s)
     then show ?case
      apply (rule_tac x=msg in scases,simp)
      apply (simp add: srcdups_step)
      apply (rule_tac ts=ora in oracases,simp_all)
      apply (simp add: srcdups_step newOra_srcdups_t)
      using dropwhile_med apply force
 sorry
   oops
   
(*
 apply (induction ora  arbitrary: msg rule: ind,simp_all)
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

  apply(simp add: srt_srcdups)
  apply (subst  srcdups_step_srt,simp+)
 *) 
(*

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
   (simp add: srcdups_nbot,simp+) sorry *)

   
lemma newOra_srcdups_obtains: obtains ora2 where "srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2"
  using newOra_srcdups b auto  
oops

definition srcdupsOra :: "'a stream \<rightarrow> bool stream" where
"srcdupsOra \<equiv> \<Lambda> s. sprojfst\<cdot>(sscanl (\<lambda> (ora, prev) cur. (prev=cur, cur)) (undefined, undefined)\<cdot>s)"


fixrec src2med :: "'a stream \<rightarrow> bool stream" where 
"src2med\<cdot>\<epsilon> = \<epsilon>" |
"src2med\<cdot>((up\<cdot>a) && as) = 
  (if a=b then (updis True) && newOracle_srcdups\<cdot>as\<cdot>bs
   else (updis False) && newOracle_srcdups\<cdot>((up\<cdot>a) && as)\<cdot>bs)"

lemma srcdups2smed: "srcdups\<cdot>s = sMed\<cdot>s\<cdot>(srcdupsOra\<cdot>s)" oops

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

lemma srcdups_smed2: "#(srcdups\<cdot>msg) \<noteq> \<infinity> \<and> #(srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora)) =  #(srcdups\<cdot>msg) \<Longrightarrow> srcdups\<cdot>msg = srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora)"
  oops
 
(*
lemma srcdups_smed: " #(srcdups\<cdot>s) \<noteq> \<infinity> \<and> #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) = #(srcdups\<cdot>s) \<Longrightarrow> srcdups\<cdot>s = srcdups\<cdot>(sMed\<cdot>s\<cdot>p)"
proof (induction s arbitrary: p rule: ind)
    case 1
    then show ?case 
    apply(rule adm_all)
    apply(rule adm_imp,simp)
    apply(rule admI)
    apply(simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
 apply(rule admI)
    apply(simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
sorry
  next
    case 2
    then show ?case by simp
  next
    case (3 a s)
    then show ?case 
sorry
oops
*)    

lemma smed_slen2smed:
 " #(sMed\<cdot>s\<cdot>(srcdupsOra\<cdot>s)) \<noteq> \<infinity> \<and> #(sMed\<cdot>s\<cdot>(newOracle\<cdot>p\<cdot>(srcdupsOra\<cdot>(sMed\<cdot>s\<cdot>p)))) = #(sMed\<cdot>s\<cdot>(srcdupsOra\<cdot>s)) \<Longrightarrow>
    sMed\<cdot>s\<cdot>(srcdupsOra\<cdot>s) = sMed\<cdot>s\<cdot>(newOracle\<cdot>p\<cdot>(srcdupsOra\<cdot>(sMed\<cdot>s\<cdot>p)))" 
  apply (induction s arbitrary: p rule: ind, simp_all)
  apply (rule adm_all, rule adm_imp, simp_all, rule admI)
  apply (metis (mono_tags, lifting) admI inf_chainl4 l42
  apply (rule_tac ts=ora in oracases, simp_all)
  apply fastforce
  apply (meti antisym_conv2 inf_ub less2eq less_lnsuc ln_less smed_slen)
oops

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