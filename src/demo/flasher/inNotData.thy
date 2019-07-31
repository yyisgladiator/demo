theory inNotData

imports bundle.SB
  begin

typedef inNot="{cout}"
  by auto


instantiation inNot::"{somechan,finite}"
begin
definition "Rep = Rep_inNot"
instance
  apply(standard)
  apply(auto simp add: Rep_inNot_def cEmpty_def)
  using ctype.elims
  apply (metis Rep_inNot ctype.simps(4) ctype.simps(5) ctype.simps(6) ex_in_conv insertE insert_iff)
  apply (meson Rep_inNot_inject injI) using ctype.elims Rep_inNot apply simp
  using type_definition.Abs_image type_definition_inNot typedef_finite_UNIV by fastforce
end

definition "Notin \<equiv> Abs_inNot cout"

free_constructors inNot for "Notin"
  by (metis(full_types) Abs_inNot_cases singletonD)

lemma Andin1_rep [simp]: "Rep (Notin) = cout"
  using Rep_inNot Rep_inNot_def by auto

fun inNotChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> inNot \<Rightarrow> 'a" where
"inNotChan Cc1 bool Notin = Cc1 bool"

abbreviation "buildNotinSBE \<equiv> inNotChan \<B>" 

lemma buildnotin_ctype: "buildNotinSBE a c \<in> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma buildnotin_inj: "inj buildNotinSBE"
  apply(rule injI)
  apply(case_tac x; case_tac y; simp)
  by (metis M.inject(2) inNotChan.simps)+

lemma buildnotin_range: "range (\<lambda>a. buildNotinSBE a c) = ctype (Rep c)"
  apply(cases c)
  using Rep_inNot Rep_inNot_def by auto

lemma buildnotin_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildNotinSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildNotinSBE a c)"
    by (simp add: buildnotin_range)
  hence "\<exists>prod. sbe = buildNotinSBE prod"
    apply(subst fun_eq_iff,auto)
    by (metis (full_types) inNot.exhaust rangeE)
  thus ?thesis
    by auto
qed

abbreviation "buildNotinSB \<equiv> inNotChan (Rep_cfun (smap \<B>))" 

end