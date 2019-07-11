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
  using ctype.elims
  apply (metis Rep_inFlash ex_in_conv insertE insert_iff)
  apply (meson Rep_inFlash_inject injI) using ctype.elims Rep_inFlash apply simp
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

abbreviation "buildFlashinSBE \<equiv> inFlashChan \<B>" 

lemma buildflashin_ctype: "buildFlashinSBE a c \<in> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma buildflashin_inj: "inj buildFlashinSBE"
  apply(rule injI)
  apply(case_tac x; case_tac y; simp)
  by (metis M.inject(2) inFlashChan.simps)+

lemma buildflashin_range: "range (\<lambda>a. buildFlashinSBE a c) = ctype (Rep c)"
  apply(cases c)
  by(auto simp add: image_iff)

lemma buildflashin_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildFlashinSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildFlashinSBE a c)"
    using buildflashin_range by auto
  hence "\<exists>prod. sbe = buildFlashinSBE prod"
    apply(subst fun_eq_iff,auto)
    by (metis(full_types) inFlash.exhaust rangeE)
   thus ?thesis
    by auto
qed


abbreviation "buildFlashinSB \<equiv> inFlashChan (Rep_cfun (smap \<B>))" 

lemma buildflashoutsb_ctype: "sdom\<cdot>(buildFlashinSB a c) \<subseteq> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma buildflashoutsb_inj: "inj buildFlashinSB"
  apply(rule injI)
  sorry


lemma buildflashoutsb_range: "(\<Union>a. sdom\<cdot>(buildFlashinSB a c)) = ctype (Rep c)"
  apply(cases c)
  apply auto 
  apply (metis (no_types, lifting) in_mono smap_sdom_range)
  apply(rule_tac x="\<up>xa" in exI)
  by simp

lemma buildflashoutsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildFlashinSB"
proof -
  have ctypewell:"\<And> c. sValues (sb c) \<subseteq> ctype (Rep c)"
    using assms
    by (simp add: sb_well_def) 
  hence "\<exists>prod. sb = buildFlashinSB prod"
    apply(subst fun_eq_iff,auto,simp add: sValues_def)
    sorry
  thus ?thesis
    by auto
qed


end