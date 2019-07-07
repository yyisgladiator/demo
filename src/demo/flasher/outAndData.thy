theory outAndData

imports bundle.sbElem
  begin

typedef outAnd = "{cout}"
  by auto

definition "Andout \<equiv> Abs_outAnd cout"


instantiation outAnd::"{somechan,finite}"
begin
definition "Rep = Rep_outAnd"
instance
  apply(standard)
  apply(auto simp add: Rep_outAnd_def)
  apply (metis Rep_outAnd singletonD)
   apply (meson Rep_outAnd_inject injI)
  sorry
end

free_constructors outAnd for "Andout"
  unfolding Andout_def
  using Abs_outAnd_cases by auto

lemma Andout1_rep [simp]: "Rep (Andout) = cout"
  using Rep_outAnd Rep_outAnd_def by auto

fun outAndChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outAnd \<Rightarrow> 'a" where
"outAndChan Cc1 bool Andout = Cc1 bool"

abbreviation "buildAndoutSBE \<equiv> outAndChan \<B>" 

lemma buildandout_ctype: "buildAndoutSBE a c \<in> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma buildandout_inj: "inj buildAndoutSBE"
  apply(rule injI)
  apply(case_tac x; case_tac y; simp)
  by (metis M.inject(2) outAndChan.simps)+

lemma buildandout_range: "range (\<lambda>a. buildAndoutSBE a c) = ctype (Rep c)"
  apply(cases c)
  by(auto simp add: image_iff)

lemma buildandout_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildAndoutSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildAndoutSBE a c)"
    by (simp add: buildandout_range)
  hence "\<exists>prod. sbe = buildAndoutSBE prod"
    apply(subst fun_eq_iff,auto)
    by (metis (full_types) outAnd.exhaust rangeE)
  thus ?thesis
    by auto
qed

end