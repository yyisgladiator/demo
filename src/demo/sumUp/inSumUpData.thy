theory inSumUpData

imports bundle.SB
  begin

typedef inSumUp="{cin}"
  by auto


instantiation inSumUp::"{somechan,finite}"
begin
definition "Rep = Rep_inSumUp"
instance
  apply(standard)
  apply(auto simp add: Rep_inSumUp_def cEmpty_def)
  apply(auto simp add: ctype_empty_iff)
  using ctype_empty_iff
  apply (metis Rep_inSumUp cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_inSumUp_inject injI) using cMsg.elims Rep_inSumUp apply simp
  using type_definition.Abs_image type_definition_inSumUp typedef_finite_UNIV by fastforce
end

definition "SumUpin \<equiv> Abs_inSumUp cin"

free_constructors inSumUp for "SumUpin"
  by (metis(full_types) Abs_inSumUp_cases singletonD)

lemma Andin1_rep [simp]: "Rep (SumUpin) = cin"
  using Rep_inSumUp Rep_inSumUp_def by auto

fun inSumUpChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> inSumUp \<Rightarrow> 'a" where
"inSumUpChan Cc1 bool SumUpin = Cc1 bool"

abbreviation "buildSumUpinSBE \<equiv> inSumUpChan (Untimed o \<N>)" 

lemma buildsumUpin_ctype: "buildSumUpinSBE a c \<in> ctype (Rep c)"
  sorry

lemma buildsumUpin_inj: "inj buildSumUpinSBE"
  sorry

lemma buildsumUpin_range: "range (\<lambda>a. buildSumUpinSBE a c) = ctype (Rep c)"
  sorry

lemma buildsumUpin_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildSumUpinSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildSumUpinSBE a c)"
    by (simp add: buildsumUpin_range)
  hence "\<exists>prod. sbe = buildSumUpinSBE prod"
    apply(subst fun_eq_iff,auto)
    sorry
  thus ?thesis
    by auto
qed

abbreviation "buildSumUpinSB \<equiv> inSumUpChan (Rep_cfun (smap ((Untimed o \<N>))))" 

end