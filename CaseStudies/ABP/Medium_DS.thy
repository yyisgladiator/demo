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
    then show ?case sorry
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

(*    
lemma prop4s_h3_h6: " #(srcdups\<cdot>(smap snd\<cdot>s)) \<noteq> \<infinity> \<Longrightarrow>  lnsuc\<cdot>(#(srcdups\<cdot>(smap snd\<cdot>(sMed\<cdot>s\<cdot>as)))) = #(srcdups\<cdot>(smap snd\<cdot>s)) \<Longrightarrow> False"
 sorry
*)

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
    
lemma prop4s_h3: assumes  "#(srcdups\<cdot>s) \<noteq> \<infinity>" "#({True} \<ominus> p) = \<infinity>" "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) = #(srcdups\<cdot>s)"  
       "#(srcdups\<cdot>(sprojsnd\<cdot>s))= #(srcdups\<cdot>s)" shows 
       "(srcdups\<cdot>s) = (srcdups\<cdot>(sMed\<cdot>s\<cdot>p))" 
     using assms proof(induction s arbitrary: p rule:ind)
       case 1
       then show ?case sorry
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
         apply (simp add: prop4s_h3_h2)
         apply (cases rule: oracases)
         apply (simp add: prop4s_h3_h2)  
         apply simp  
         apply (case_tac "sMed\<cdot>s\<cdot>as= \<epsilon>") 
         apply (simp add: prop4s_h3_h3)
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
  apply (metis (no_types, lifting) "3.prems"(2) "3.prems"(3) "3.prems"(4) prop4s_h3_h2 smed_slen2smed2 smed_t srcdups_nfst2snd)
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
 
end