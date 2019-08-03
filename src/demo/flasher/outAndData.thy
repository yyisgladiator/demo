theory outAndData

imports bundle.SB
  begin

typedef outAnd = "{cout}"
  by auto

definition "Andout \<equiv> Abs_outAnd cout"


instantiation outAnd::"{somechan,finite}"
begin
definition "Rep = Rep_outAnd"
instance
  apply(standard)
  apply(auto simp add: Rep_outAnd_def cEmpty_def)
  apply(auto simp add: ctype_empty_iff)
  using ctype_empty_iff
  apply (metis Rep_outAnd cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_outAnd_inject injI) using cMsg.elims Rep_outAnd apply simp
  using type_definition.Abs_image type_definition_outAnd typedef_finite_UNIV by fastforce
end
free_constructors outAnd for "Andout"
  unfolding Andout_def
  using Abs_outAnd_cases by auto

lemma Andout1_rep [simp]: "Rep (Andout) = cout"
  using Rep_outAnd Rep_outAnd_def by auto

fun outAndChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outAnd \<Rightarrow> 'a" where
"outAndChan Cc1 bool Andout = Cc1 bool"

abbreviation "buildAndoutSBE \<equiv> outAndChan (Tsyn o (map_option) \<B>)" 

lemma buildandout_ctype: "buildAndoutSBE a c \<in> ctype (Rep c)"
  sorry

lemma buildandout_inj: "inj buildAndoutSBE"
  sorry

lemma buildandout_range: "range (\<lambda>a. buildAndoutSBE a c) = ctype (Rep c)"
  sorry

lemma buildandout_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildAndoutSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildAndoutSBE a c)"
    by (simp add: buildandout_range)
  hence "\<exists>prod. sbe = buildAndoutSBE prod"
    apply(subst fun_eq_iff,auto)
    sorry
  thus ?thesis
    by auto
qed

abbreviation "buildAndoutSB \<equiv> outAndChan (Rep_cfun (smap (Tsyn o (map_option) \<B>)))" 

end