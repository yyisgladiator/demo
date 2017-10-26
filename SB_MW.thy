theory SB_MW
imports SB

begin

chapter\<open>definitions\<close>  
  
  
definition sbHd :: "'m SB \<rightarrow> (channel \<rightharpoonup> 'm discr\<^sub>\<bottom>)" where
"sbHd \<equiv> \<Lambda> sb. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))" 

(* sbRt is defined in SB.thy *)

definition sbLscons :: "(channel \<rightharpoonup> 'm discr\<^sub>\<bottom>) \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"sbLscons \<equiv> \<lambda> f sb. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom f))) \<leadsto> (lscons\<cdot>(f \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>"

definition convDiscrUp :: "(channel \<rightharpoonup> 'm) \<Rightarrow> (channel \<rightharpoonup> 'm discr\<^sub>\<bottom>)" where
"convDiscrUp sb \<equiv> (\<lambda>c. (c \<in> dom sb) \<leadsto> (Iup (Discr (sb \<rightharpoonup> c))))"

definition convSB :: "(channel \<rightharpoonup> 'm discr\<^sub>\<bottom>) \<Rightarrow> 'm SB" where
"convSB sb \<equiv> (\<lambda>c. (c \<in> dom sb) \<leadsto> (lscons\<cdot>(sb \<rightharpoonup> c)\<cdot>\<epsilon>))\<Omega>"


chapter\<open>helper lemmas\<close>
  
section\<open>sbHd\<close>  

  
lemma sbHd_mono: "monofun (\<lambda> sb::'a SB. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c))))"  
proof(rule monofunI) 
  fix x y ::"'a SB"
  assume "x \<sqsubseteq> y"
  then show "(\<lambda> sb::'a SB. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))) x \<sqsubseteq> (\<lambda> sb::'a SB. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))) y"
    by (smt \<open>x \<sqsubseteq> y\<close> cont_pref_eq1I fun_below_iff monofun_cfun_fun po_eq_conv sbdom_eq some_below)
qed  
  
lemma sbHd_cont_pre: assumes "chain Y" shows "(\<lambda>c. (c \<in> sbDom\<cdot>(\<Squnion>i. Y i))\<leadsto>lshd\<cdot>((\<Squnion>i. Y i) . c)) \<sqsubseteq> (\<Squnion>i. (\<lambda>c. (c \<in> sbDom\<cdot>(Y i))\<leadsto>lshd\<cdot>(Y i . c)))"
proof - 
  fix c
  have "(\<lambda>c. (c \<in> sbDom\<cdot>(\<Squnion>i. Y i))\<leadsto>lshd\<cdot>((\<Squnion>i. Y i) . c)) c \<sqsubseteq> (\<Squnion>i. (\<lambda>c. (c \<in> sbDom\<cdot>(Y i))\<leadsto>lshd\<cdot>(Y i . c)) c)"
  proof(cases "c \<in> sbDom\<cdot>(\<Squnion>i. Y i)")
    case True
    have f1: "\<And>i. sbDom\<cdot>(\<Squnion>i. Y i) =  sbDom\<cdot>(Y i)"
      by (simp add: assms sbChain_dom_eq2)
    then show ?thesis 
      apply(simp add: True)
    proof -
      have "Some (lshd\<cdot>(\<Squnion>n. Y n . c)) \<sqsubseteq> (\<Squnion>n. Some (lshd\<cdot>(Y n . c)))"
        by (metis assms ch2ch_Rep_cfunL ch2ch_Rep_cfunR if_then_lub)
      then show "Some (lshd\<cdot>(Lub Y . c)) \<sqsubseteq> (\<Squnion>n. Some (lshd\<cdot>(Y n . c)))"
        by (simp add: assms sbgetch_lub)
    qed
  next
    case False
    then show ?thesis 
      using assms sbChain_dom_eq2 by fastforce
  qed  
  then show ?thesis
    by (smt assms ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun fun_below_iff if_then_lub is_ub_thelub lub_eq lub_fun monofun_cfun_arg monofun_cfun_fun po_class.chain_def po_eq_conv sbChain_dom_eq2 some_below)
qed  
    
lemma sbHd_cont: "cont (\<lambda> sb::'a SB. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c))))"  
  apply(rule contI2)
  by(simp_all add: sbHd_mono sbHd_cont_pre)
  
(* 
section\<open>sbLscons\<close>

lemma sbLscons_mono: assumes "\<forall>c \<in> dom f. sdom\<cdot>(lscons\<cdot>(f \<rightharpoonup> c)\<cdot>\<epsilon>) \<subseteq> ctype c" shows 
  "monofun (\<lambda> sb. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom f))) \<leadsto> (lscons\<cdot>(f \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>)"  
proof(rule monofunI)  
  fix x y ::"'a SB"
  assume "x \<sqsubseteq> y"
  thus "(\<lambda> sb. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom f))) \<leadsto> (lscons\<cdot>(f \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>) x \<sqsubseteq> 
        (\<lambda> sb. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom f))) \<leadsto> (lscons\<cdot>(f \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>) y"
  proof - 
    have f0: "sbDom\<cdot>x = sbDom\<cdot>y"
      using \<open>x \<sqsubseteq> y\<close> sbdom_eq by auto
    have f3: "sb_well (\<lambda>c. (c \<in> sbDom\<cdot>x \<inter> dom f)\<leadsto>f\<rightharpoonup>c && x . c)"
      apply(simp only: sb_well_def)
      apply(subst OptionCpo.if_then_dom, simp)
      sorry
    have f4: "sb_well (\<lambda>c. (c \<in> sbDom\<cdot>y \<inter> dom f)\<leadsto>f\<rightharpoonup>c && y . c)"
      apply(simp only: sb_well_def)
      apply(subst OptionCpo.if_then_dom, simp)
      sorry
    have f5: "dom (Rep_SB ((\<lambda>c. (c \<in> sbDom\<cdot>x \<inter> dom f)\<leadsto>f\<rightharpoonup>c && x . c)\<Omega>)) = sbDom\<cdot>x \<inter> dom f"
      apply(subst rep_abs, simp only: f3)
      by (metis OptionCpo.if_then_dom)
    have f6: "dom (Rep_SB ((\<lambda>c. (c \<in> sbDom\<cdot>y \<inter> dom f)\<leadsto>f\<rightharpoonup>c && y . c)\<Omega>)) = sbDom\<cdot>y \<inter> dom f"
      apply(subst rep_abs, simp only: f4)
        by (metis OptionCpo.if_then_dom)
    show ?thesis
      apply(subst less_SBI)
      using f0 f5 f6 apply auto[1]
      (* proof found by sledgehammer *)
      sorry
  qed    
qed    

lemma sbLscons_cont_pre: assumes "chain Y" 
  shows "(\<lambda>c. (c \<in> (sbDom\<cdot>(\<Squnion>i. Y i) \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>((\<Squnion>i. Y i) . c)))\<Omega> \<sqsubseteq> (\<Squnion>i. (\<lambda>c. (c \<in> (sbDom\<cdot>(Y i) \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>((Y i) . c)))\<Omega>)"    
proof - 
  have "dom (\<lambda>c. (c \<in> (sbDom\<cdot>(Y i) \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>((Y i) . c))) = sbDom\<cdot>(Y i) \<inter> (dom sb1)"
    sorry
  show ?thesis
    apply(subst less_SBI)
    
qed
  sorry  
  
lemma sbLscons_cont: "cont (\<lambda> sb. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>)"  
  apply(rule contI2)
  using sbLscons_mono apply auto[1]
  using sbLscons_cont_pre by blast
*)
    
end