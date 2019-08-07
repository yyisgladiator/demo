theory outEvenData

imports bundle.SB
  begin

typedef outEven = "{cout}"
  by auto

instantiation outEven::"{somechan,finite}"
begin
definition "Rep = Rep_outEven"
instance
  apply(standard)
  apply(auto simp add: Rep_outEven_def cEmpty_def)
  apply(auto simp add: ctype_empty_iff)
  using ctype_empty_iff
  apply (metis Rep_outEven cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_outEven_inject injI) using cMsg.elims Rep_outEven apply simp
  using type_definition.Abs_image type_definition_outEven typedef_finite_UNIV by fastforce
end

definition "Evenout \<equiv> Abs_outEven cout"

free_constructors outEven for "Evenout"
  by (metis(full_types) Abs_outEven_cases singletonD)

lemma Andin1_rep [simp]: "Rep (Evenout) = cout"
  by (simp add: Abs_outEven_inverse Evenout_def Rep_outEven_def)

fun outEvenChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outEven \<Rightarrow> 'a" where
"outEvenChan Cc1 bool Evenout = Cc1 bool"

abbreviation "buildEvenoutSBE \<equiv> outEvenChan (Untimed o \<B>)" 

lemma buildevenout_ctype: "buildEvenoutSBE a c \<in> ctype (Rep c)"
  sorry

lemma buildevenout_inj: "inj buildEvenoutSBE"
  sorry

lemma buildevenout_range: "range (\<lambda>a. buildEvenoutSBE a c) = ctype (Rep c)"
  sorry

lemma buildevenout_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildEvenoutSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildEvenoutSBE a c)"
    by (simp add: buildevenout_range)
  hence "\<exists>prod. sbe = buildEvenoutSBE prod"
    apply(subst fun_eq_iff,auto)
    sorry
  thus ?thesis
    by auto
qed

abbreviation "buildEvenoutSB \<equiv> outEvenChan (Rep_cfun (smap (Untimed o \<B>)))" 

end