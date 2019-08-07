theory inEvenData

imports bundle.SB
  begin

typedef inEven="{cin}"
  by auto


instantiation inEven::"{somechan,finite}"
begin
definition "Rep = Rep_inEven"
instance
  apply(standard)
  apply(auto simp add: Rep_inEven_def cEmpty_def)
  apply(auto simp add: ctype_empty_iff)
  using ctype_empty_iff
  apply (metis Rep_inEven cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_inEven_inject injI) using cMsg.elims Rep_inEven apply simp
  using type_definition.Abs_image type_definition_inEven typedef_finite_UNIV by fastforce
end

definition "Evenin \<equiv> Abs_inEven cin"

free_constructors inEven for "Evenin"
  by (metis(full_types) Abs_inEven_cases singletonD)

lemma Andin1_rep [simp]: "Rep (Evenin) = cin"
  using Rep_inEven Rep_inEven_def by auto

fun inEvenChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> inEven \<Rightarrow> 'a" where
"inEvenChan Cc1 bool Evenin = Cc1 bool"

abbreviation "buildEveninSBE \<equiv> inEvenChan (Untimed o \<N>)" 

lemma buildevenin_ctype: "buildEveninSBE a c \<in> ctype (Rep c)"
  sorry

lemma buildevenin_inj: "inj buildEveninSBE"
  sorry

lemma buildevenin_range: "range (\<lambda>a. buildEveninSBE a c) = ctype (Rep c)"
  sorry

lemma buildevenin_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildEveninSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildEveninSBE a c)"
    by (simp add: buildevenin_range)
  hence "\<exists>prod. sbe = buildEveninSBE prod"
    apply(subst fun_eq_iff,auto)
    sorry
  thus ?thesis
    by auto
qed

abbreviation "buildEveninSB \<equiv> inEvenChan (Rep_cfun (smap ((Untimed o \<N>))))" 

end