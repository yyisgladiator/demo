theory inFlashData

imports bundle.SB
begin

typedef inFlash="{cin1}"
  by auto


instantiation inFlash::"{somechan,finite}"
begin
definition "Rep = Rep_inFlash"
instance
  apply(standard)
  apply(auto simp add: Rep_inFlash_def cEmpty_def)
  apply(auto simp add: ctype_empty_gdw)
  using ctype_empty_gdw
  apply (metis Rep_inFlash cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_inFlash_inject injI) using cMsg.elims Rep_inFlash apply simp
  using type_definition.Abs_image type_definition_inFlash typedef_finite_UNIV by fastforce
end

definition "Flashin \<equiv> Abs_inFlash cin1"

free_constructors inFlash for "Flashin"
  unfolding Flashin_def
  by (metis (full_types)Rep_inFlash Rep_inFlash_inverse empty_iff insert_iff)

lemma Flashin1_rep [simp]: "Rep (Flashin) = cin1"
  by (simp add: Abs_inFlash_inverse Flashin_def Rep_inFlash_def)


fun inFlashChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> inFlash \<Rightarrow> 'a" where
"inFlashChan Cc1 bool Flashin = Cc1 bool"

abbreviation "buildFlashinSBE \<equiv> inFlashChan (Tsyn o (map_option) \<B>)" 

lemma buildflashin_ctype: "buildFlashinSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a;simp)
  by(simp_all add: ctype_def)

lemma buildflashin_inj: "inj buildFlashinSBE"
  apply (auto simp add: inj_def)
  by (metis inFlashChan.simps inj_def inj_B inj_tsyncons)+

lemma buildflashin_range: "range (\<lambda>a. buildFlashinSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

lemma buildflashin_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildFlashinSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildFlashinSBE a c)"
    by (simp add: buildflashin_range)
  hence "\<exists>prod. sbe = buildFlashinSBE prod"
    apply(simp add: fun_eq_iff f_inv_into_f image_iff)
    by (metis (full_types) inFlash.exhaust)
  thus ?thesis
    by auto
qed



abbreviation "buildFlashinSB \<equiv> inFlashChan (Rep_cfun (smap (Tsyn o (map_option) \<B>)))" 

lemma buildflashoutsb_ctype: "sValues\<cdot>(buildFlashinSB a c) \<subseteq> ctype (Rep c)"
 apply(cases c)
  apply auto
   by (metis Flashin1_rep buildflashin_ctype f_inv_into_f inFlashChan.simps smap_sValues)

lemma smap_inj:"inj f \<Longrightarrow> inj (Rep_cfun (smap f))"
  apply(rule injI)
  apply(rule snths_eq,auto)
  apply (metis slen_smap)
  by (metis inj_eq slen_smap smap_snth_lemma)

lemma rep_cfun_smap_bool_inj:"inj (Rep_cfun (smap (Tsyn o (map_option) \<B>)))"
  apply(rule smap_inj)
 
  by simp
lemma buildflashoutsb_inj: "inj buildFlashinSB"
  by (metis (mono_tags, lifting) inFlashChan.simps inj_def rep_cfun_smap_bool_inj)


lemma buildflashoutsb_range: "(\<Union>a. sValues\<cdot>(buildFlashinSB a c)) = ctype (Rep c)"
  apply(cases c)
  apply auto

  apply (metis (no_types, lifting) Flashin1_rep buildflashoutsb_ctype contra_subsetD inFlashChan.simps)

  apply(rule_tac x="\<up>(inv (Tsyn \<circ> map_option \<B>)x)" in exI,auto)
  by (metis Flashin1_rep buildflashin_range comp_apply f_inv_into_f image_cong inFlashChan.simps)


lemma smap_well:"sValues\<cdot>x\<subseteq>range f \<Longrightarrow>  \<exists>s. smap f\<cdot>s = x"
  apply(rule_tac x = "smap (inv f)\<cdot>x" in exI)
  by (simp add: snths_eq smap_snth_lemma f_inv_into_f snth2sValues subset_eq)
  
lemma buildflashoutsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildFlashinSB"
proof -
  have ctypewell:"\<And> c. sValues\<cdot>(sb c) \<subseteq> ctype (Rep c)"
    using assms
    by (simp add: sb_well_def) 
  hence "\<exists>prod. sb = buildFlashinSB prod"
    apply(subst fun_eq_iff,auto,simp add: sValues_def)
 proof -
have f1: "\<forall>i M. sValues\<cdot>(sb i) \<subseteq> M \<or> \<not> ctype (Rep i) \<subseteq> M"
  by (metis ctypewell dual_order.trans)
  have "ctype (Rep Flashin) \<subseteq> range(Tsyn o (map_option) \<B>)"
    by (metis buildflashin_range image_cong inFlashChan.simps set_eq_subset)
then show "\<exists>s. \<forall>i. sb i = buildFlashinSB s i"
using f1 by (smt inFlash.exhaust inFlashChan.simps sValues_def smap_well)
qed 

   
  thus ?thesis
    by auto
qed


end