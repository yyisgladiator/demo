theory outSumUpData

imports bundle.SB
  begin

typedef outSumUp = "{cout}"
  by auto

instantiation outSumUp::"{somechan,finite}"
begin
definition "Rep = Rep_outSumUp"
instance
  apply(standard)
  apply(auto simp add: Rep_outSumUp_def cEmpty_def)
  apply(auto simp add: ctype_empty_iff)
  using ctype_empty_iff
  apply (metis Rep_outSumUp cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_outSumUp_inject injI) using cMsg.elims Rep_outSumUp apply simp
  using type_definition.Abs_image type_definition_outSumUp typedef_finite_UNIV by fastforce
end

definition "SumUpout \<equiv> Abs_outSumUp cout"

free_constructors outSumUp for "SumUpout"
  by (metis(full_types) Abs_outSumUp_cases singletonD)

lemma Andin1_rep [simp]: "Rep (SumUpout) = cout"
  by (simp add: Abs_outSumUp_inverse SumUpout_def Rep_outSumUp_def)

fun outSumUpChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outSumUp \<Rightarrow> 'a" where
"outSumUpChan Cc1 bool SumUpout = Cc1 bool"

abbreviation "buildSumUpoutSBE \<equiv> outSumUpChan (Untimed o \<N>)" 

lemma buildsumUpout_ctype: "buildSumUpoutSBE a c \<in> ctype (Rep c)"
  sorry

lemma buildsumUpout_inj: "inj buildSumUpoutSBE"
  sorry

lemma buildsumUpout_range: "range (\<lambda>a. buildSumUpoutSBE a c) = ctype (Rep c)"
  sorry

lemma buildsumUpout_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildSumUpoutSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildSumUpoutSBE a c)"
    by (simp add: buildsumUpout_range)
  hence "\<exists>prod. sbe = buildSumUpoutSBE prod"
    apply(subst fun_eq_iff,auto)
    sorry
  thus ?thesis
    by auto
qed

abbreviation "buildSumUpoutSB \<equiv> outSumUpChan (Rep_cfun (smap (Untimed o \<N>)))" 

end