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
  apply(auto simp add: ctype_empty_iff)
  using ctype_empty_iff
  apply (metis Rep_inNot cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_inNot_inject injI) using cMsg.elims Rep_inNot apply simp
  using type_definition.Abs_image type_definition_inNot typedef_finite_UNIV by fastforce
end

definition "Notin \<equiv> Abs_inNot cout"

free_constructors inNot for "Notin"
  by (metis(full_types) Abs_inNot_cases singletonD)

lemma Andin1_rep [simp]: "Rep (Notin) = cout"
  using Rep_inNot Rep_inNot_def by auto

fun inNotChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> inNot \<Rightarrow> 'a" where
"inNotChan Cc1 bool Notin = Cc1 bool"

abbreviation "buildNotinSBE \<equiv> inNotChan (Tsyn o (map_option) \<B>)" 

lemma buildnotin_ctype: "buildNotinSBE a c \<in> ctype (Rep c)"
  sorry

lemma buildnotin_inj: "inj buildNotinSBE"
  sorry

lemma buildnotin_range: "range (\<lambda>a. buildNotinSBE a c) = ctype (Rep c)"
  sorry

lemma buildnotin_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildNotinSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildNotinSBE a c)"
    by (simp add: buildnotin_range)
  hence "\<exists>prod. sbe = buildNotinSBE prod"
    apply(subst fun_eq_iff,auto)
    sorry
  thus ?thesis
    by auto
qed

abbreviation "buildNotinSB \<equiv> inNotChan (Rep_cfun (smap (Tsyn o (map_option) \<B>)))" 

end