theory outFM

imports bundle.SB
  begin

typedef outFM = "{cout}"
  by auto

definition "FMout \<equiv> Abs_outFM cout"


instantiation outFM::"{somechan,finite}"
begin
definition "Rep = Rep_outFM"
instance
  apply(standard)
  apply(auto simp add: Rep_outFM_def cEmpty_def)
  apply(auto simp add: ctype_empty_iff)
  using ctype_empty_iff
  apply (metis Rep_outFM cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_outFM_inject injI) using cMsg.elims Rep_outFM apply simp
  using type_definition.Abs_image type_definition_outFM typedef_finite_UNIV by fastforce
end

free_constructors outFM for "FMout"
  unfolding FMout_def
  using Abs_outFM_cases by auto

lemma FMout1_rep [simp]: "Rep (FMout) = cout"
  using Rep_outFM Rep_outFM_def by auto

fun outFMChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outFM \<Rightarrow> 'a" where
"outFMChan Cc1 bool FMout = Cc1 bool"

abbreviation "buildFMoutSBE \<equiv> outFMChan (Tsyn o (map_option) \<B>)" 

lemma buildfmout_ctype: "buildFMoutSBE a c \<in> ctype (Rep c)"
  sorry

lemma buildfmout_inj: "inj buildFMoutSBE"
  sorry

lemma buildfmout_range: "range (\<lambda>a. buildFMoutSBE a c) = ctype (Rep c)"
  sorry

lemma buildfmout_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildFMoutSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildFMoutSBE a c)"
    by (simp add: buildfmout_range)
  hence "\<exists>prod. sbe = buildFMoutSBE prod"
    apply(subst fun_eq_iff,auto)
    sorry
  thus ?thesis
    by auto
qed

abbreviation "buildFMoutSB \<equiv> outFMChan (Rep_cfun (smap (Tsyn o (map_option) \<N>)))" 

end