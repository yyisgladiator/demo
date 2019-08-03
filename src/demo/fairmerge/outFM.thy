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
  apply(auto simp add: Rep_outFM_def)
  apply (metis Rep_outFM singletonD)
   apply (meson Rep_outFM_inject injI)
  sorry
end

free_constructors outFM for "FMout"
  unfolding FMout_def
  using Abs_outFM_cases by auto

lemma FMout1_rep [simp]: "Rep (FMout) = cout"
  using Rep_outFM Rep_outFM_def by auto

fun outFMChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outFM \<Rightarrow> 'a" where
"outFMChan Cc1 bool FMout = Cc1 bool"

abbreviation "buildFMoutSBE \<equiv> outFMChan \<N>" 

lemma buildfmout_ctype: "buildFMoutSBE a c \<in> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma buildfmout_inj: "inj buildFMoutSBE"
  apply(rule injI)
  by (metis M.inject(1) outFMChan.simps)

lemma buildfmout_range: "range (\<lambda>a. buildFMoutSBE a c) = ctype (Rep c)"
  apply(cases c)
  by(auto simp add: image_iff)

lemma buildfmout_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildFMoutSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildFMoutSBE a c)"
    by (simp add: buildfmout_range)
  hence "\<exists>prod. sbe = buildFMoutSBE prod"
    apply(subst fun_eq_iff,auto)
    by (metis (full_types) outFM.exhaust rangeE)
  thus ?thesis
    by auto
qed

abbreviation "buildFMoutSB \<equiv> outFMChan (Rep_cfun (smap \<N>))" 

end