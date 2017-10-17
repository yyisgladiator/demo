theory SB_MW
imports SB

begin

chapter\<open>definitions\<close>  
  
  
definition sbHd :: "'m SB \<rightarrow> (channel \<rightharpoonup> 'm discr\<^sub>\<bottom>)" where
"sbHd \<equiv> \<Lambda> sb. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))" 

(* sbRt is defined in SB.thy *)

definition sbLscons :: "(channel \<rightharpoonup> 'm discr\<^sub>\<bottom>) \<rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbLscons \<equiv> \<Lambda> sb1 sb. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>"

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
  

section\<open>sbLscons\<close>

  
lemma sbLscons_mono1: "monofun (\<lambda> sb1. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>)"  
proof(rule monofunI)  
  fix x y ::"(channel \<rightharpoonup> 'a discr\<^sub>\<bottom>)"
  assume "x \<sqsubseteq> y"
  thus "(\<lambda> sb1. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>) x \<sqsubseteq> 
        (\<lambda> sb1. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>) y"
    
    sorry
qed
    
lemma sbLscons_cont1_pre: assumes "chain Y" 
  shows "(\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom (\<Squnion>i. Y i)))) \<leadsto> (lscons\<cdot>((\<Squnion>i. Y i) \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega> \<sqsubseteq> (\<Squnion>i. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom (Y i)))) \<leadsto> (lscons\<cdot>((Y i) \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>)"    
  sorry
    
lemma sbLscons_cont1: "cont (\<lambda> sb1. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>)" 
  apply(rule contI2)
  using sbLscons_mono1 apply auto[1]
  using sbLscons_cont1_pre by blast

lemma sbLscons_mono2: "monofun (\<lambda> sb. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>)"  
proof(rule monofunI)  
  fix x y ::"'a SB"
  assume "x \<sqsubseteq> y"
  thus "(\<lambda> sb. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>) x \<sqsubseteq> 
        (\<lambda> sb. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>) y"
   
    sorry
qed    

lemma sbLscons_cont2_pre: assumes "chain Y" 
  shows "(\<lambda>c. (c \<in> (sbDom\<cdot>(\<Squnion>i. Y i) \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>((\<Squnion>i. Y i) . c)))\<Omega> \<sqsubseteq> (\<Squnion>i. (\<lambda>c. (c \<in> (sbDom\<cdot>(Y i) \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>((Y i) . c)))\<Omega>)"    
  
  sorry  
  
lemma sbLscons_cont2: "cont (\<lambda> sb. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>)"  
  apply(rule contI2)
  using sbLscons_mono2 apply auto[1]
  using sbLscons_cont2_pre by blast
  
end