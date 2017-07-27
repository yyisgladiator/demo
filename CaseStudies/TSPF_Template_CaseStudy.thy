(*  Title:  TSPF_Tempalte_CaseStudy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: A more modern  proof approach to instantiate TSPFs
                 The proofs can mostly be auto generated
*)

theory TSPF_Template_CaseStudy
  imports "../TSB" "../TSPF" "../TSPF_Comp"
    
begin


  default_sort message  
 
(* instantiate our message space*) 
instantiation nat :: message 
begin 
  definition ctype_nat :: "channel \<Rightarrow> nat set" where 
  "ctype c = range nat" 
 
instance .. 
end 
 
lemma [simp]: "cs \<subseteq> ((ctype c) :: nat set)" 
  apply(simp add: ctype_nat_def) 
  by(metis subset_UNIV subset_image_iff transfer_int_nat_set_return_embed) 

lemma tsb_well_nx1: fixes f :: "nat tstream \<rightarrow> nat tstream"
  shows "tsbDom\<cdot>b = cs \<Longrightarrow> tsb_well [ch2 \<mapsto> f\<cdot>(b  .  ch1)]"
    by (simp add: tsb_wellI)

(* an tspf with at least one input and one output channel is mono *)
lemma tspf_nx1_mono [simp]: fixes f :: "nat tstream \<rightarrow> nat tstream" assumes "{ch1} \<subseteq> cs"
  shows "monofun (\<lambda> tb. (tsbDom\<cdot>tb = cs) \<leadsto> ([ch2 \<mapsto> f\<cdot>(tb . ch1)]\<Omega>))" 
proof (rule tspf_monoI)
  have f1: "\<And> b. tsbDom\<cdot>b = cs \<Longrightarrow> tsb_well [ch2 \<mapsto> f\<cdot>(b  .  ch1)]"
    by (simp add: tsb_wellI)  
  thus "\<And>x y. tsbDom\<cdot>x = cs \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> [ch2 \<mapsto> f\<cdot>(x  .  ch1)]\<Omega> \<sqsubseteq> [ch2 \<mapsto> f\<cdot>(y  .  ch1)]\<Omega>"
    apply (subst tsb_below)
      apply (simp add: tsbdom_below tsbdom_rep_eq)
      apply (simp add: monofun_cfun_arg tsbgetch_below tsbdom_below tsbgetch_rep_eq)
      by simp
qed    

lemma lub_f_tsb_getch: fixes f :: "nat tstream \<rightarrow> nat tstream" 
              assumes "chain Y" and "{ch1} \<subseteq> tsbDom\<cdot>(\<Squnion>i. Y i)"  
              and "c \<in> tsbDom\<cdot>([ch2 \<mapsto> f\<cdot>((\<Squnion>i. Y i)  .  ch1)]\<Omega>) "
  shows "(\<Squnion>i. [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)]\<Omega>)  .  c = (\<Squnion>i. ([ch2 \<mapsto> f\<cdot>(Y i  .  ch1)]\<Omega>) .  c)"
proof (rule lubgetCh)
  have f1: "\<And> cs b. tsbDom\<cdot>b = cs \<Longrightarrow> tsb_well [ch2 \<mapsto> f\<cdot>(b  .  ch1)]"
    by (simp add: tsb_wellI)
  have f2: "\<And> i. tsbDom\<cdot>(Y i) =  tsbDom\<cdot>(\<Squnion>i. Y i)"
    by (simp add: assms(1))
  show tb_chain: "chain (\<lambda>i. [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)]\<Omega>)"
    by (simp add: chainI assms(1) f1 monofun_cfun_arg po_class.chainE tsb_below tsbdom_rep_eq 
                  tsbgetch_below tsbgetch_rep_eq)
      
                
  have f10: "\<And> i. tsbDom\<cdot>(Y i) = tsbDom\<cdot>(\<Squnion>i. Y i)"
    by (simp add: assms(1))
  have f11: "tsbDom\<cdot>(\<Squnion>i. [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)]\<Omega>) = {ch2}"
    by (simp add: tsbdom_lub assms(2) f1 f10 tsbdom_rep_eq tb_chain)  
  have f12: "tsbDom\<cdot>([ch2 \<mapsto> f\<cdot>((\<Squnion>i. Y i)  .  ch1)]\<Omega>) = tsbDom\<cdot>(\<Squnion>i. [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)]\<Omega>)"
    by (simp add: assms(2) f11 f1 tsbdom_rep_eq)
      
  show "c \<in> tsbDom\<cdot>(\<Squnion>i. [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)]\<Omega>) "
    using assms(3) f12 by blast
qed
  
(* an tspf with at least one input and one output channel is cont *)
lemma tspf_nx1_cont [simp]: fixes f :: "nat tstream \<rightarrow> nat tstream" assumes "{ch1} \<subseteq> cs"
  shows "cont (\<lambda> tb. (tsbDom\<cdot>tb = cs) \<leadsto> ([ch2 \<mapsto> f\<cdot>(tb . ch1)]\<Omega>))"
proof (rule tspf_contI)
  have f1: "\<And> b. tsbDom\<cdot>b = cs \<Longrightarrow> tsb_well [ch2 \<mapsto> f\<cdot>(b  .  ch1)]"
    apply (subst tsb_wellI)
    by (simp_all)
  
  show f_mono: "\<And>x y. tsbDom\<cdot>x = cs \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> 
                    [ch2 \<mapsto> f\<cdot>(x  .  ch1)]\<Omega> \<sqsubseteq> [ch2 \<mapsto> f\<cdot>(y  .  ch1)]\<Omega>"
    apply (rule tsb_below)
      apply (simp add: f1 tsbdom_below tsbdom_rep_eq)
      by (simp add: f1 monofun_cfun_arg tsbgetch_below tsbdom_below tsbgetch_rep_eq)

  have f2: "\<And>Y c. chain Y \<Longrightarrow>
           tsbDom\<cdot>(\<Squnion>i. Y i) = cs \<Longrightarrow>
           c \<in> tsbDom\<cdot>([ch2 \<mapsto> f\<cdot>((\<Squnion>i. Y i)  .  ch1)]\<Omega>) \<Longrightarrow>
           ([ch2 \<mapsto> f\<cdot>((\<Squnion>i. Y i)  .  ch1)]\<Omega>)  .  c \<sqsubseteq> (\<Squnion>i. ([ch2 \<mapsto> f\<cdot>(Y i  .  ch1)]\<Omega>)  .  c)"
      proof -
        fix Y :: "nat \<Rightarrow> nat TSB" and c :: channel
        assume a1: "chain Y"
        assume a2: "tsbDom\<cdot>(\<Squnion>i. Y i) = cs"
        assume a3: "c \<in> tsbDom\<cdot> ([ch2 \<mapsto> f\<cdot>((\<Squnion>i. Y i) . ch1)]\<Omega>)"
        obtain nn :: "(nat \<Rightarrow> nat tstream) \<Rightarrow> (nat \<Rightarrow> nat tstream) \<Rightarrow> nat" where
            f4: "\<forall>f fa. f (nn fa f) \<noteq> fa (nn fa f) \<or> Lub f = Lub fa"
          by (meson lub_eq)
        have f5: "\<forall>t. tsbDom\<cdot>t \<noteq> cs \<or> tsb_well [ch2 \<mapsto> f\<cdot>(t . ch1)]"
          using f1 by blast
        then have f6: "tsb_well [ch2 \<mapsto> f\<cdot>(Lub Y . ch1)]"
          using a2 by blast
        have f7: "\<forall>c ca. (c::channel) \<notin> {ca} \<or> c = ca"
          by (metis singletonD)
        have f8: "c \<in> {ch2}"
          using f5 a3 a2 by (simp add: tsbdom_rep_eq)
        have f9: "f\<cdot> (Y (nn (\<lambda>n. ([ch2 \<mapsto> f\<cdot>(Y n . ch1)]\<Omega>) . c) (\<lambda>n. f\<cdot>(Y n . ch1))) . ch1) 
                  = ([ch2 \<mapsto> f\<cdot> (Y (nn (\<lambda>n. ([ch2 \<mapsto> f\<cdot>(Y n . ch1)]\<Omega>) . c) 
                                  (\<lambda>n. f\<cdot>(Y n . ch1))) . ch1)]\<Omega>) . ch2"
          using f5 a2 a1 by (simp add: tsbgetch_rep_eq)
        have "c = ch2"
          using f8 f7 by metis
        then have "(\<Squnion>n. f\<cdot>(Y n . ch1)) = (\<Squnion>n. ([ch2 \<mapsto> f\<cdot>(Y n . ch1)]\<Omega>) . c)"
        using f9 f4 by meson
        then have "([ch2 \<mapsto> f\<cdot>(Lub Y . ch1)]\<Omega>) . c = (\<Squnion>n. ([ch2 \<mapsto> f\<cdot>(Y n . ch1)]\<Omega>) . c)"
          using f8 f6 a1 by (simp add: contlub_cfun_arg contlub_cfun_fun tsbgetch_rep_eq)
        then show "([ch2 \<mapsto> f\<cdot>((\<Squnion>n. Y n) . ch1)]\<Omega>) . c \<sqsubseteq> (\<Squnion>n. ([ch2 \<mapsto> f\<cdot>(Y n . ch1)]\<Omega>) . c)"
          by simp
      qed
  have f3: "ch1 \<in> cs"
    using assms by blast
  show "\<And>Y. chain Y \<Longrightarrow> tsbDom\<cdot>(\<Squnion>i. Y i) = cs \<Longrightarrow> 
                         [ch2 \<mapsto> f\<cdot>((\<Squnion>i. Y i)  .  ch1)]\<Omega> \<sqsubseteq> (\<Squnion>i. [ch2 \<mapsto> f\<cdot>(Y i  .  ch1)]\<Omega>)"
    apply (rule tsb_below)
      apply (metis (no_types, lifting) f_mono dom_fun_upd f1 option.simps(3) po_class.chain_def 
                                       tsbChain_dom_eq2 tsbdom_rep_eq)
      by (simp add: assms(1) lub_f_tsb_getch f2 f3)
qed
 
lemma tspf_nx1_general_dom [simp]: fixes f :: "nat tstream \<rightarrow> nat tstream" assumes "{ch1} \<subseteq> cs"
  and "tspf_well (\<Lambda> (tb::nat TSB). (tsbDom\<cdot>tb = cs) \<leadsto>  ([ch2 \<mapsto> f\<cdot>(tb . ch1)]\<Omega>))"
shows  "tspfDom\<cdot>(Abs_TSPF (\<Lambda> tb. (tsbDom\<cdot>tb = cs) \<leadsto> ([ch2 \<mapsto> f\<cdot>(tb . ch1)]\<Omega>))) = cs"  
  
proof -
  have f1: "cont (\<lambda> tb. (tsbDom\<cdot>tb = cs)\<leadsto>[ch2 \<mapsto> f\<cdot>(tb  .  ch1)]\<Omega>)"
    by (simp only: tspf_nx1_cont assms(1))
  
  hence "Rep_cfun (\<Lambda> tb. (tsbDom\<cdot>tb = cs)\<leadsto>[ch2 \<mapsto> f\<cdot>(tb  .  ch1)]\<Omega>) = (\<lambda> tb. (tsbDom\<cdot>tb = cs)\<leadsto>[ch2 \<mapsto> f\<cdot>(tb  .  ch1)]\<Omega>)"
    by simp
  show ?thesis
  apply (simp add: tspf_dom_insert Rep_CTSPF_def)
  apply (simp add: assms domIff2 f1)
    by (metis (mono_tags) TSB_def mem_Collect_eq someI_ex tsb_tsbleast)
qed
  
  
  section \<open>example Instantiations\<close>  
  
  subsection \<open>delay_fun\<close> 
  
lemma delay_tspf_cont[simp]: 
 "cont (\<lambda> tb:: nat TSB. (tsbDom\<cdot>tb = {ch1}) \<leadsto> ([ch2 \<mapsto> delayFun\<cdot>(tb . ch1)]\<Omega>))"
  by simp
    
lemma delay_tspf_well [simp]: 
  "tspf_well (\<Lambda> (tb::nat TSB). (tsbDom\<cdot>tb = {ch1}) \<leadsto> ([ch2 \<mapsto> delayFun\<cdot>(tb . ch1)]\<Omega>))"
proof -
  have f1: "\<And> tb. tsbDom\<cdot>tb = {ch1} \<Longrightarrow> #\<surd>tsb tb = #\<surd> (tb . ch1)"
    by (simp add: tsbtick_single_ch2)
  have f2: "\<And>b::nat TSB. tsbDom\<cdot>b = {ch1} \<Longrightarrow> tsbDom\<cdot>([ch2 \<mapsto> delayFun\<cdot>(b  .  ch1)]\<Omega>) = {ch2}"
    by (simp add: tsbdom_rep_eq tsb_well_nx1)
  show ?thesis  
  apply (rule tspf_wellI)
     apply (simp_all add: domIff2 f2)
     apply (subst tsbtick_single_ch1, simp add: tsb_well_nx1)
     by (simp add: f1 delayFun.rep_eq)
qed

lemma delay_tspf_dom [simp]: "tspfDom\<cdot>(Abs_CTSPF (\<lambda> (tb::nat TSB). (tsbDom\<cdot>tb = {ch1}) 
                      \<leadsto> ([ch2 \<mapsto> delayFun\<cdot>(tb . ch1)]\<Omega>))) = {ch1}"
  by (simp add: Abs_CTSPF_def)
 
lemma delay_tspf_ran [simp]: "tspfRan\<cdot>(Abs_CTSPF (\<lambda> (tb::nat TSB). (tsbDom\<cdot>tb = {ch1}) 
                      \<leadsto> ([ch2 \<mapsto> delayFun\<cdot>(tb . ch1)]\<Omega>))) = {ch2}"
  apply(simp add: tspfran_least)
  by (simp add: tsb_well_def tsbdom_rep_eq)
 
  subsection \<open>identity\<close> 
    
end