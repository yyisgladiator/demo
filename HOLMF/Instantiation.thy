theory Instantiation

imports Division GFP

begin




section \<open>set\<close>

instantiation set:: ( division ) div_pcpo
begin
definition DIV_set:: "'a::division set set set" where
"DIV_set = (Pow ` DIV)"

lemma set_div_union: "S \<subseteq> C \<Longrightarrow> C\<in>DIV \<Longrightarrow> \<Union>S \<in> C"
  by (smt DIV_set_def Pow_mono Pow_top Sup_subset_mono Union_Pow_eq contra_subsetD imageE)

lemma set_div_intersection: "S \<subseteq> C \<Longrightarrow> C\<in>DIV \<Longrightarrow> S\<noteq>{} \<Longrightarrow> \<Inter>S \<in> C"
proof -
  assume a1: "S \<subseteq> C"
  assume a2: "C \<in> DIV"
  assume a3: "S \<noteq> {}"
  have "C \<in> Pow ` DIV"
    using a2 DIV_set_def by fastforce
  then show ?thesis
    using a3 a1 by blast
qed

instance
  apply(intro_classes)
  apply (simp add: DIV_set_def div_non_empty)
  using DIV_set_def apply auto[1]
  apply (metis DIV_set_def PowI Union_Pow_eq Union_is_lub Union_mono f_inv_into_f)
  by (metis DIV_set_def Pow_bottom SetPcpo.less_set_def empty_subsetI f_inv_into_f)
end


instantiation set::(division) rev_div_cpo
begin

instance
proof(intro_classes)
  fix S:: "'a set set"
  fix C:: "'a set set"

  assume "longChain (Rev ` S)" and c_div: "C\<in>DIV" and s_c: "S\<subseteq>C" and "infinite (GFP.rev.Rev ` S)"
  have rev_below:"\<And>a b:: 'a set . Rev a \<sqsubseteq> Rev b \<longleftrightarrow> b \<subseteq> a"
    by (simp add: SetPcpo.less_set_def)
  hence "(Rev ` S) <<| (Rev (\<Inter> S))" 
    apply(auto simp add: is_lub_def is_ub_def)
    by (metis GFP.rev.exhaust Inf_greatest rev_below)
  moreover have "(\<Inter> S) \<in> C "
    using \<open>infinite (GFP.rev.Rev ` (S::'a set set))\<close> c_div s_c set_div_intersection by auto 
  thus "\<exists>x\<in>C. GFP.rev.Rev ` S <<| GFP.rev.Rev x"
    using calculation by blast 
  qed
end


instantiation set::(division) rev_div_upcpo
begin

instance
  apply(intro_classes)
  apply (auto simp add: less_set_def)
  by (metis (no_types, lifting) DIV_set_def Pow_iff Pow_top image_iff)
end



section \<open>fun div_cpo\<close>

instantiation "fun" :: (type, division) division
begin
definition DIV_fun:: "('s::type \<Rightarrow> 'm::division) set set" where
"DIV_fun = (setify ` (setify (\<lambda>a. DIV)))"   

lemma div_fun_s: fixes f g::"'s::type \<Rightarrow> 'm::div_cpo"
  assumes "D\<in>(DIV::('s \<Rightarrow> 'm) set set)" and "f\<in>D"
  shows "(\<exists>d2\<in>DIV::'m set set. f a\<in>d2)"
    using assms apply(simp add:  DIV_fun_def)
  unfolding DIV_fun_def
  by (smt setify_def bex_imageD mem_Collect_eq)

lemma div_fun_non_empty: "(DIV::('s::type \<Rightarrow> 'm::division) set set) \<noteq> {}"
  apply(simp add:  DIV_fun_def)
  apply(rule setify_notempty)
  by (simp add: div_non_empty)

lemma div_fun_non_empty2: "a\<in>(DIV::('s::type \<Rightarrow> 'm::division) set set) \<Longrightarrow> a \<noteq> {}"
  apply(simp add:  DIV_fun_def)
  by (smt setify_def setify_notempty div_inner_non_empty image_iff mem_Collect_eq)

lemma div_fun_s2: fixes f g::"'s::type \<Rightarrow> 'm::division"
  assumes "D\<in>(DIV::('s \<Rightarrow> 'm) set set)" and "f\<in>D" and "g\<in>D"
  shows "(\<exists>d2\<in>DIV::'m set set. f a\<in>d2 \<and> g a\<in>d2)"
  using assms apply(simp add: DIV_fun_def)
  by (smt setify_def image_iff mem_Collect_eq) 
instance
  apply(intro_classes)
  apply (simp add: div_fun_non_empty)
  using div_fun_non_empty2 by blast

end

instantiation "fun" :: (type, div_cpo) div_cpo
begin

lemma div_cpo_fun_chains: "longChain S \<Longrightarrow> longChain {s a | s. s\<in>S}"
apply(auto simp add: longChain_def)
  by (meson fun_belowD)

lemma div_cpo_fun_lub: fixes S::"('s::type \<Rightarrow> 'p::div_cpo) set"
  assumes "D\<in>DIV" and "S\<subseteq>D"  and "longChain S"
  shows "S <<| (\<lambda>a. lub {s a | s. s\<in>S})" and "(\<lambda>a. lub {s a | s. s\<in>S}) \<in> D"
proof -
  obtain DD where dd_def: "D = setify DD" and dd_in: "DD\<in>setify (\<lambda>a. DIV)"
    by (metis DIV_fun_def assms(1) imageE)
  hence "\<And>s a. s\<in>S \<Longrightarrow> s a \<in> DD a"
    by (metis (no_types, lifting) CollectD setify_def assms(2) set_mp)
  hence f1: "\<And>a. {s a | s. s\<in>S} \<subseteq> DD a"
    by (smt CollectD setify_def dd_in subsetI)

  moreover have dd_in_div: "\<And>a. DD a\<in>DIV"
    by (metis (mono_tags, lifting) setify_def dd_in mem_Collect_eq)
  moreover have chain: "\<And>a. longChain {s a | s. s\<in>S}"
    by (simp add: assms(3) div_cpo_fun_chains)
  ultimately have lub_in: "\<And>a. lub {s a | s. s\<in>S} \<in> DD a"
    by (simp add: div_cpo_lub_in)

 show "(\<lambda>a. lub {s a | s. s\<in>S}) \<in> D"
   by (simp add: setify_def dd_def lub_in)

  have s_lub: "\<And>a. {s a | s. s\<in>S} <<| lub {s a | s. s\<in>S}"
      using chain dd_in_div div_cpo_g f1 is_lub_lub by blast
    hence "S <| (\<lambda>a::'s. lub {s a |s::'s \<Rightarrow> 'p. s \<in> S})"
      by (smt below_fun_def is_lub_def is_ub_def mem_Collect_eq)
    moreover have "\<And>u::'s \<Rightarrow> 'p. S <| u \<Longrightarrow> (\<lambda>a::'s. lub {s a |s::'s \<Rightarrow> 'p. s \<in> S}) \<sqsubseteq> u"
    by (smt s_lub fun_belowD fun_belowI is_lub_below_iff is_ubD is_ubI mem_Collect_eq)
  ultimately show "S <<| (\<lambda>a. lub {s a | s. s\<in>S})"
    using is_lubI by blast
qed

instance 
  apply(intro_classes)
  using div_cpo_fun_lub(1) div_cpo_fun_lub(2) by blast
end







section \<open>fun div_pcpo\<close>

instance "fun" :: (type, div_pcpo) div_pcpo
proof(intro_classes)
  fix a ::"('a::type \<Rightarrow> 'b::div_pcpo) set"
  assume "a\<in>DIV"
 from this obtain DD where dd_def: "a = setify DD" and dd_in: "DD\<in>setify (\<lambda>a. DIV)"
   by (metis DIV_fun_def imageE)  
  hence bot_exist: "\<And>s. \<exists>bot\<in>DD s. \<forall>b\<in>DD s. bot\<sqsubseteq>b"
    by (simp add: SetPcpo.setify_def div_pcpo)
  let ?bot = "\<lambda>s. SOME bot. (bot\<in>DD s \<and> (\<forall>b\<in>DD s. bot\<sqsubseteq>b))"
  have "?bot \<in> a"
    by (smt SetPcpo.setify_def bot_exist dd_def mem_Collect_eq someI_ex)
  moreover have "\<forall>b\<in>a. ?bot \<sqsubseteq> b" apply(simp add: below_fun_def, auto)
    by (smt SetPcpo.setify_def bot_exist dd_def mem_Collect_eq someI_ex)
  ultimately show "\<exists>bot\<in>a. \<forall>b\<in>a. bot \<sqsubseteq> b" by blast
qed



instance "fun" :: (type, rev_div_cpo) rev_div_cpo
  apply(intro_classes)
  sorry

instance "fun" :: (type, div_upcpo) div_upcpo
  apply(intro_classes)
  sorry


end