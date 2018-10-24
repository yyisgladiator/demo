theory Instantiation

imports Division GFP

begin

default_sort po


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

  assume "longChain (S)" and c_div: "C\<in>DIV" and s_c: "S\<subseteq>C" and "infinite (S)"
  have rev_below:"\<And>a b:: 'a set . Rev a \<sqsubseteq> Rev b \<longleftrightarrow> b \<subseteq> a"
    by (simp add: SetPcpo.less_set_def)
  hence "(Rev ` S) <<| (Rev (\<Inter> S))" 
    apply(auto simp add: is_lub_def is_ub_def)
    by (metis GFP.rev.exhaust Inf_greatest rev_below)
  moreover have "(\<Inter> S) \<in> C "
    using \<open>infinite (S::'a set set)\<close> c_div s_c set_div_intersection by blast
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





instance "fun" :: (type, div_upcpo) div_upcpo
proof(intro_classes)
  fix a ::"('a::type \<Rightarrow> 'b::div_upcpo) set"
  assume "a\<in>DIV"
 from this obtain DD where dd_def: "a = setify DD" and dd_in: "DD\<in>setify (\<lambda>a. DIV)"
   by (metis DIV_fun_def imageE)  
  hence top_exist: "\<And>s. \<exists>top\<in>DD s. \<forall>b\<in>DD s. b\<sqsubseteq>top"
    by (metis (mono_tags, lifting) CollectD SetPcpo.setify_def div_upcpo)
  let ?top = "\<lambda>s. SOME top. (top\<in>DD s \<and> (\<forall>b\<in>DD s. b\<sqsubseteq>top))"
  have "?top \<in> a"
    by (smt SetPcpo.setify_def dd_def mem_Collect_eq someI_ex top_exist)
  moreover have "\<forall>b\<in>a. b\<sqsubseteq>?top" apply(simp add: below_fun_def, auto)
    by (smt SetPcpo.setify_def dd_def mem_Collect_eq someI_ex top_exist)
  ultimately show "\<exists>top\<in>a. \<forall>b\<in>a.  b \<sqsubseteq> top" by blast
qed




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

instantiation "fun" :: (type, rev_div_cpo) rev_div_cpo
begin

lemma fun_rev_cpo: fixes S :: "('a::type \<Rightarrow> 'b::rev_div_cpo) set"
    assumes "C \<in> DIV" and "infinite (S)" and  "longChain ( S)" and "S \<subseteq> C" 
  shows "Rev ` S <<| Rev (\<lambda>a. (inv Rev) (lub {Rev (s a) | s. s\<in>S}))" and "(\<lambda>a. (inv Rev) (lub {Rev (s a) | s. s\<in>S})) \<in>C"
proof -
  have "longChain S"
    using assms(3) longchain_rev by blast

  obtain DD where dd_def: "C = setify DD" and dd_in: "DD\<in>setify (\<lambda>a. DIV)"
    by (metis DIV_fun_def assms(1) imageE)
  hence "\<And>s a. s\<in>S \<Longrightarrow> s a \<in> DD a"
    by (metis (mono_tags, lifting) SetPcpo.setify_def assms(4) mem_Collect_eq rev_subsetD)
  hence f1: "\<And>a. {s a | s. s\<in>S} \<subseteq> DD a"
    by (smt CollectD setify_def dd_in subsetI)

  have dd_in_div: "\<And>a. DD a\<in>DIV"
    by (metis (mono_tags, lifting) setify_def dd_in mem_Collect_eq)
  have chain: "\<And>a. longChain {s a | s. s\<in>S}"
    by (simp add: assms(3) div_cpo_fun_chains)
  hence "\<And>a. longChain (Rev ` {(s a) | s. s\<in>S})"
    using longchain_rev by blast
  hence h1: "\<And>a. \<exists>x\<in>(DD a). (Rev ` {(s a) | s. s\<in>S}) <<| Rev x" 
    using rev_div_lub_ex dd_in_div f1
    by (simp add: rev_div_lub_ex chain)
  hence h2: "\<And>a. \<exists>!x. x \<in>(DD a) \<and> (Rev ` {(s a) | s. s\<in>S}) <<| Rev x"
    by (smt GFP.rev.inject lub_eqI) 

  let ?Lubs = "\<lambda>a. THE x. (x\<in>(DD a) \<and> (Rev ` {(s a) | s. s\<in>S}) <<| Rev x)"
  have lubs: "\<And>a.  ((?Lubs a)\<in>(DD a) \<and> (Rev ` {(s a) | s. s\<in>S}) <<| Rev (?Lubs a))"
    apply(rule theI')
    by (simp add: h2)
  have h5: "\<And>a. GFP.rev.Rev ` {s a |s. s \<in> S} = {Rev (s a) | s. s\<in>S}"
    by auto
  have "\<And>a. (Rev ` {(s a) | s. s\<in>S}) <<| (lub {Rev (s a) | s. s\<in>S})"
    apply(simp add: h5 )
    using h5 is_lub_lub lubs by fastforce


  hence lub_in: "\<And>a. lub (Rev ` {(s a) | s. s\<in>S}) \<in> (Rev ` (DD a))"
    by (smt h2 imageI lub_eqI)
  have lubs_eq_lulb: "?Lubs = (\<lambda>a. (inv Rev) (lub {Rev (s a) | s. s\<in>S}))"
    by (metis (no_types, lifting) GFP.rev.inject \<open>\<And>a::'a. GFP.rev.Rev ` {s a |s::'a \<Rightarrow> 'b. s \<in> (S::('a \<Rightarrow> 'b) set)} <<| lub {GFP.rev.Rev (s a) |s::'a \<Rightarrow> 'b. s \<in> S}\<close> is_lub_unique lub_def lubs rev_invrev setcompr_eq_image)

  have s_lub: "\<And>a. (Rev ` {s a | s. s\<in>S}) <<| lub (Rev ` {(s a) | s. s\<in>S})"
    using chain dd_in_div div_cpo_g f1 is_lub_lub using h1 by fastforce
  hence "\<And>a y. y\<in>S \<Longrightarrow> (Rev (y a)) \<sqsubseteq> (lub {GFP.rev.Rev (s a) |s. s \<in> S})"
    by (metis (mono_tags, lifting) Collect_cong h5 is_ub_thelub_ex mem_Collect_eq) 
  hence "Rev ` S <| Rev (\<lambda>a. (inv Rev) (lub {Rev (s a) | s. s\<in>S}))" 
    by(auto simp add: is_ub_def below_rev_def below_fun_def)
  have "\<And>x a. (Rev ` S) <| (Rev x) \<Longrightarrow> (lub {Rev (s a) |s. s \<in> S}) \<sqsubseteq> Rev (x a)" 
    apply(auto simp add: is_ub_def)
  proof - (* fuck it, thx sledgi *)
    fix x :: "'a \<Rightarrow> 'b" and a :: 'a
    assume a1: "\<forall>y\<in>S. x \<sqsubseteq> y"
    obtain rr :: "'b GFP.rev \<Rightarrow> 'b GFP.rev set \<Rightarrow> 'b GFP.rev" where
      f2: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notsqsubseteq> x0) = (rr x0 x1 \<in> x1 \<and> rr x0 x1 \<notsqsubseteq> x0)"
by moura
  obtain bb :: "'b GFP.rev \<Rightarrow> 'b GFP.rev \<Rightarrow> 'b" and bba :: "'b GFP.rev \<Rightarrow> 'b GFP.rev \<Rightarrow> 'b" where
    "\<forall>x0 x1. (\<exists>v2 v3. x1 = GFP.rev.Rev v2 \<and> x0 = GFP.rev.Rev v3 \<and> v3 \<notsqsubseteq> v2) = (x1 = GFP.rev.Rev (bb x0 x1) \<and> x0 = GFP.rev.Rev (bba x0 x1) \<and> bba x0 x1 \<notsqsubseteq> bb x0 x1)"
    by moura
  then have f3: "\<forall>r ra. r \<sqsubseteq> ra \<or> r = GFP.rev.Rev (bb ra r) \<and> ra = GFP.rev.Rev (bba ra r) \<and> bba ra r \<notsqsubseteq> bb ra r"
    by (meson GFP.below_rev.elims(3))
obtain bbb :: "'b GFP.rev \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'b" where
  f4: "\<forall>x0 x1. (\<exists>v2. x0 = GFP.rev.Rev (v2 x1) \<and> v2 \<in> S) = (x0 = GFP.rev.Rev (bbb x0 x1 x1) \<and> bbb x0 x1 \<in> S)"
by moura
  { assume "GFP.rev.Rev (bb (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) (rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S})) \<noteq> GFP.rev.Rev (bbb (GFP.rev.Rev (bb (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) (rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S}))) a a) \<or> bbb (GFP.rev.Rev (bb (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) (rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S}))) a \<notin> S"
    moreover
    { assume "\<nexists>f. rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S} = GFP.rev.Rev (f a) \<and> f \<in> S"
      then have "rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S} \<notin> {GFP.rev.Rev (f a) |f. f \<in> S} \<or> rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S} \<sqsubseteq> GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))"
by blast
  then have "{GFP.rev.Rev (f a) |f. f \<in> S} <| GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))"
using f2 by (meson is_ubI) }
  ultimately have "(rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S} \<noteq> GFP.rev.Rev (bb (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) (rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S})) \<or> GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})) \<noteq> GFP.rev.Rev (bba (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) (rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S})) \<or> bba (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) (rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S}) \<sqsubseteq> bb (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) (rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S})) \<or> {GFP.rev.Rev (f a) |f. f \<in> S} <| GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))"
      using f4 by fastforce }
  moreover
  { assume "rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S} \<noteq> GFP.rev.Rev (bb (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) (rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S})) \<or> GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})) \<noteq> GFP.rev.Rev (bba (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) (rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S})) \<or> bba (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) (rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S}) \<sqsubseteq> bb (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) (rr (GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) {GFP.rev.Rev (f a) |f. f \<in> S})"
    then have "{GFP.rev.Rev (f a) |f. f \<in> S} <| GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))"
      using f3 f2 by (meson is_ubI) }
  moreover
  { assume "{GFP.rev.Rev (f a) |f. f \<in> S} <| GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))"
    moreover
    { assume "(GFP.rev.Rev (bb (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})) \<sqsubseteq> GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))) \<noteq> {GFP.rev.Rev (f a) |f. f \<in> S} <| GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))"
      then have "\<not> {GFP.rev.Rev (f a) |f. f \<in> S} <<| GFP.rev.Rev (bb (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}))"
        using is_lub_below_iff by blast
      then have "lub {GFP.rev.Rev (f a) |f. f \<in> S} \<noteq> GFP.rev.Rev (bb (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})) \<or> GFP.rev.Rev (x a) \<noteq> GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})) \<or> bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}) \<sqsubseteq> bb (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})"
        using \<open>\<And>a::'a. GFP.rev.Rev ` {s a |s::'a \<Rightarrow> 'b. s \<in> (S::('a \<Rightarrow> 'b) set)} <<| lub {GFP.rev.Rev (s a) |s::'a \<Rightarrow> 'b. s \<in> S}\<close> h5 by force }
    ultimately have "lub {GFP.rev.Rev (f a) |f. f \<in> S} \<sqsubseteq> GFP.rev.Rev (x a) \<or> lub {GFP.rev.Rev (f a) |f. f \<in> S} \<noteq> GFP.rev.Rev (bb (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})) \<or> GFP.rev.Rev (x a) \<noteq> GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})) \<or> bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}) \<sqsubseteq> bb (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})"
      by auto }
  ultimately have "lub {GFP.rev.Rev (f a) |f. f \<in> S} \<sqsubseteq> GFP.rev.Rev (x a) \<or> lub {GFP.rev.Rev (f a) |f. f \<in> S} \<noteq> GFP.rev.Rev (bb (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})) \<or> GFP.rev.Rev (x a) \<noteq> GFP.rev.Rev (bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})) \<or> bba (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S}) \<sqsubseteq> bb (GFP.rev.Rev (x a)) (lub {GFP.rev.Rev (f a) |f. f \<in> S})"
    using a1 fun_belowD by fastforce
  then show "lub {GFP.rev.Rev (f a) |f. f \<in> S} \<sqsubseteq> GFP.rev.Rev (x a)"
    using f3 by meson
qed
 
  hence "\<And>x a. (Rev ` S) <| (Rev x) \<Longrightarrow> x a \<sqsubseteq> (inv Rev) (lub {Rev (s a) |s. s \<in> S})"
    by (metis (no_types, lifting) Collect_cong below_rev_def inv_rev)
  hence "\<And>u. (Rev ` S) <| u \<Longrightarrow>  Rev (\<lambda>a. (inv Rev) (lub {Rev (s a) | s. s\<in>S})) \<sqsubseteq> u"
    by (simp add: below_rev_def fun_belowI)

  thus "Rev ` S <<| Rev (\<lambda>a. (inv Rev) (lub {Rev (s a) | s. s\<in>S}))"
    using \<open>GFP.rev.Rev ` (S::('a \<Rightarrow> 'b) set) <| GFP.rev.Rev (\<lambda>a::'a. inv GFP.rev.Rev (lub {GFP.rev.Rev (s a) |s::'a \<Rightarrow> 'b. s \<in> S}))\<close> is_lubI by blast
  have "\<And>a. (inv Rev) (lub {Rev (s a) | s. s\<in>S}) \<in> DD a"
    by (metis lubs lubs_eq_lulb)
  thus "(\<lambda>a. (inv Rev) (lub {Rev (s a) | s. s\<in>S})) \<in>C"  by (simp add: setify_def dd_def lub_in)

qed

instance
  apply(intro_classes)
  using fun_rev_cpo(1) fun_rev_cpo(2) by blast
end



instance "fun" :: (type, rev_div_upcpo) rev_div_upcpo
  by(intro_classes)




section \<open>Pair\<close>

instantiation prod :: (division, division) division
begin
definition DIV_prod:: "('a \<times> 'b) set set" where
"DIV_prod = { {(a,b) | a b. a\<in>A \<and> b\<in>B} | A B . A\<in>DIV \<and> B\<in>DIV}"   

lemma prod_div_fst: "C\<in>DIV \<Longrightarrow> (fst ` C)\<in>DIV"
  by(auto simp add: DIV_prod_def div_inner_non_empty)

lemma prod_div_snd: "C\<in>DIV \<Longrightarrow> (snd ` C)\<in>DIV"
  by(auto simp add: DIV_prod_def div_inner_non_empty)

instance 
  apply(intro_classes)
  unfolding DIV_prod_def
  apply auto
  apply (metis div_non_empty ex_in_conv)
  using div_inner_non_empty apply blast
  using div_inner_non_empty by blast
end


instantiation prod :: (div_cpo, div_cpo) div_cpo
begin

lemma prod_fst_chain: "longChain S \<Longrightarrow> longChain (fst ` S)"
  by (simp add: longchain_mono monofun_fst)

lemma prod_snd_chain: "longChain S \<Longrightarrow> longChain (snd ` S)"
  by (simp add: longchain_mono monofun_snd)

lemma prod_fst_lub_in: fixes C :: "('a::div_cpo \<times> 'b) set" 
  shows "C \<in>DIV \<Longrightarrow> longChain S \<Longrightarrow> S \<subseteq> C \<Longrightarrow> (lub (fst ` S))\<in>(fst ` C)"
  by (simp add: div_cpo_lub_in image_mono prod_div_fst prod_fst_chain)

lemma prod_snd_lub_in: fixes C :: "('a \<times> 'b::div_cpo) set" 
  shows "C \<in>DIV \<Longrightarrow> longChain S \<Longrightarrow> S \<subseteq> C \<Longrightarrow> (lub (snd ` S))\<in>(snd ` C)"
  by (simp add: div_cpo_lub_in image_mono prod_div_snd prod_snd_chain)

lemma prod_lub_in: fixes C :: "('a::div_cpo \<times> 'b::div_cpo) set" 
  shows "C \<in> DIV \<Longrightarrow> longChain S \<Longrightarrow> S \<subseteq> C \<Longrightarrow> (lub (fst ` S), lub (snd ` S)) \<in> C"
  apply(auto simp add: DIV_prod_def)
  using div_cpo_lub_in prod_fst_chain apply fastforce
  using div_cpo_lub_in prod_snd_chain apply fastforce
  done

lemma  prod_lub_h: fixes C :: "('a::div_cpo \<times> 'b::div_cpo) set" 
  shows "C \<in> DIV \<Longrightarrow> longChain S \<Longrightarrow> S \<subseteq> C \<Longrightarrow> S <<| (lub (fst ` S), lub (snd ` S))"
  apply(auto simp add: is_lub_def is_ub_def below_prod_def)
  using prod_fst_chain div_cpo_lub_ub prod_div_fst apply (metis (no_types, hide_lams) fst_conv image_iff image_mono)
  using prod_snd_chain div_cpo_lub_ub prod_div_snd apply (metis (no_types, hide_lams) snd_conv image_iff image_mono)
  using prod_fst_chain div_cpo_lub_ub prod_div_fst  div_cpo_lub_least  apply fast
  using prod_snd_chain div_cpo_lub_ub prod_div_snd div_cpo_lub_least  apply fast
  done

lemma prod_lub: fixes C :: "('a::div_cpo \<times> 'b::div_cpo) set" 
  shows "C \<in> DIV \<Longrightarrow> longChain S \<Longrightarrow> S \<subseteq> C \<Longrightarrow> lub S = (lub (fst ` S), lub (snd ` S))"
  by (simp add: lub_eqI prod_lub_h)

instance
  apply(intro_classes)
  using Instantiation.prod_lub_in prod_lub_h by blast


end

instantiation prod :: (div_pcpo, div_pcpo) div_pcpo
begin

lemma prod_div: "(fst ` C)\<in>DIV \<Longrightarrow> (snd ` C)\<in>DIV \<Longrightarrow> C \<in>DIV"
  apply(auto simp add: DIV_prod_def)
  oops

lemma prod_least: "C \<in> DIV \<Longrightarrow> b\<in>C \<Longrightarrow> (div_bot (fst ` C), div_bot (snd ` C)) \<sqsubseteq> b"
  apply(rule prod_belowI, auto)
  using div_bot prod_div_fst apply blast
  by (simp add: div_bot prod_div_snd)

lemma prod_least_in: "C \<in> DIV \<Longrightarrow> (div_bot (fst ` C), div_bot (snd ` C)) \<in> C"
  apply(auto simp add: DIV_prod_def)
  using div_inner_non_empty apply blast
  apply (simp add: div_bot)
  using div_inner_non_empty apply blast
  by (simp add: div_bot)


instance
  apply(intro_classes)
  using prod_least prod_least_in by blast

end

lemma prod_div_bot: "C\<in>DIV \<Longrightarrow> div_bot C = (div_bot (fst ` C), div_bot (snd ` C))"
  using div_bot div_pcpo_bott prod_least prod_least_in by blast


end