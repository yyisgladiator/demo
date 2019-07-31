theory outFlashData

imports bundle.SB
begin

typedef outFlash="{cout,cin2}"
  by auto


instantiation outFlash::"{somechan,finite}"
begin
definition "Rep = Rep_outFlash"
instance
  apply(standard)
  apply(auto simp add: Rep_outFlash_def cEmpty_def)
  using ctype.elims 
  apply (metis Rep_outFlash ctype.simps(2) ctype.simps(4) ctype.simps(5) ctype.simps(6) empty_not_UNIV ex_in_conv image_is_empty insertE insert_commute insert_iff)
  apply (meson Rep_outFlash_inject injI)
  using ctype.elims Rep_outFlash 
  apply (metis ctype.simps(2) ctype.simps(4) ctype.simps(5) ctype.simps(6) empty_not_UNIV ex_in_conv image_is_empty insertE insert_commute insert_iff)
  using type_definition.Abs_image type_definition_outFlash typedef_finite_UNIV by fastforce
end

definition "Flashout \<equiv> Abs_outFlash cout"
definition "Flashcin2 \<equiv> Abs_outFlash cin2"

free_constructors outFlash for "Flashout" | Flashcin2
  unfolding Flashout_def Flashcin2_def
  apply (metis Rep_outFlash Rep_outFlash_inverse empty_iff insert_iff)
  by (simp add: Abs_outFlash_inject)

lemma Flashout1_rep [simp]: "Rep (Flashout) = cout"
  by (simp add: Abs_outFlash_inverse Flashout_def Rep_outFlash_def)

lemma Flashcin2_rep [simp]: "Rep (Flashcin2) = cin2"
  by (simp add: Abs_outFlash_inverse Flashcin2_def Rep_outFlash_def)


fun outFlashChan::"('nat::type \<Rightarrow> 'a::type) \<Rightarrow> ('bool::type \<Rightarrow> 'a) \<Rightarrow>('nat\<times>'bool) \<Rightarrow> outFlash \<Rightarrow> 'a" where
"outFlashChan Cc1 Cc2 (port_c1, port_c2) Flashout = Cc1 port_c1" |
"outFlashChan Cc1 Cc2 (port_c1, port_c2) Flashcin2 = Cc2 port_c2"

abbreviation "buildFlashoutSBE \<equiv> outFlashChan \<B> \<B>" 

lemma buildflashout_ctype: "buildFlashoutSBE a c \<in> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma buildflashout_inj: "inj buildFlashoutSBE"
  apply(rule injI)
  apply(case_tac x; case_tac y; simp)
  by (metis M.inject(2) outFlashChan.simps)+

lemma buildflashout_range: "range (\<lambda>a. buildFlashoutSBE a c) = ctype (Rep c)"
  apply(cases c)
  by(auto simp add: image_iff)

lemma buildflashout_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildFlashoutSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildFlashoutSBE a c)"
    using buildflashout_range by auto
  hence "\<exists>prod. sbe = buildFlashoutSBE prod"
    apply(subst fun_eq_iff,auto)
    by (smt Flashcin2_rep Flashout1_rep ctype.simps(5) ctype.simps(6) ctypewell imageE outFlash.exhaust outFlashChan.simps(1) outFlashChan.simps(2))
   thus ?thesis
    by auto
qed

abbreviation "buildFlashoutSB \<equiv> outFlashChan (Rep_cfun (smap \<B>)) (Rep_cfun (smap \<B>))" 

lemma buildflashinsb_ctype: "sValues\<cdot>(buildFlashoutSB a c) \<subseteq> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma buildflashinsb_inj: "inj buildFlashoutSB"
  apply(rule injI)
  sorry


lemma buildflashinsb_range: "(\<Union>a. sValues\<cdot>(buildFlashoutSB a c)) = ctype (Rep c)"
  apply(cases c)
  apply auto 
  apply (metis (no_types, lifting) in_mono smap_sValues_range)
  apply(rule_tac x="\<up>xa" in exI) 
  apply simp
  using smap_sValues_range apply blast
  apply(rule_tac x="\<up>xa" in exI) 
  by simp

lemma buildflashinsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildFlashoutSB"
proof -
  have ctypewell:"\<And> c. sValues\<cdot>(sb c) \<subseteq> ctype (Rep c)"
    using assms
    by (simp add: sb_well_def) 
  hence "\<exists>prod. sb = buildFlashoutSB prod"
    apply(subst fun_eq_iff,auto,simp)
    sorry
  thus ?thesis
    by auto
qed

end
