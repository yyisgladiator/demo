theory outNotData

imports bundle.SB
  begin

typedef outNot = "{cin2}"
  by auto

instantiation outNot::"{somechan,finite}"
begin
definition "Rep = Rep_outNot"
instance
  apply(standard)
  apply(auto simp add: Rep_outNot_def cEmpty_def)
  using ctype.elims
  apply (metis Rep_outNot ctype.simps(4) ctype.simps(5) ctype.simps(6) ex_in_conv insertE insert_iff)
  apply (meson Rep_outNot_inject injI) using ctype.elims Rep_outNot apply simp
  using type_definition.Abs_image type_definition_outNot typedef_finite_UNIV by fastforce
end

definition "Notout \<equiv> Abs_outNot cin2"

free_constructors outNot for "Notout"
  by (metis(full_types) Abs_outNot_cases singletonD)

lemma Andin1_rep [simp]: "Rep (Notout) = cin2"
  by (simp add: Abs_outNot_inverse Notout_def Rep_outNot_def)

fun outNotChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outNot \<Rightarrow> 'a" where
"outNotChan Cc1 bool Notout = Cc1 bool"

abbreviation "buildNotoutSBE \<equiv> outNotChan \<B>" 

lemma buildnotout_ctype: "buildNotoutSBE a c \<in> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma buildnotout_inj: "inj buildNotoutSBE"
  apply(rule injI)
  apply(case_tac x; case_tac y; simp)
  by (metis M.inject(2) outNotChan.simps)+

lemma buildnotout_range: "range (\<lambda>a. buildNotoutSBE a c) = ctype (Rep c)"
  apply(cases c)
  using Rep_outNot Rep_outNot_def by auto

lemma buildnotout_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildNotoutSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildNotoutSBE a c)"
    by (simp add: buildnotout_range)
  hence "\<exists>prod. sbe = buildNotoutSBE prod"
    apply(subst fun_eq_iff,auto)
    by (metis (full_types) outNot.exhaust rangeE)
  thus ?thesis
    by auto
qed

abbreviation "buildNotoutSB \<equiv> outNotChan (Rep_cfun (smap \<B>))" 

end