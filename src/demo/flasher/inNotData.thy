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

lemma Notin1_rep [simp]: "Rep (Notin) = cout"
  using Rep_inNot Rep_inNot_def by auto

fun inNotChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> inNot \<Rightarrow> 'a" where
"inNotChan Cc1 bool Notin = Cc1 bool"

abbreviation "buildNotinSBE \<equiv> inNotChan (Tsyn o (map_option) \<B>)" 

lemma rangecout[simp]:"range (Tsyn o (map_option) \<B>) = ctype cout"
  apply(auto simp add: ctype_def)
 by (metis option.simps(9) range_eqI)

lemma buildnotin_ctype: "buildNotinSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a;simp)
  by(simp_all add: ctype_def)

lemma buildnotin_inj: "inj buildNotinSBE"
  apply (auto simp add: inj_def)
  by (metis inNotChan.simps inj_def inj_B inj_tsyncons)+

lemma buildnotin_range: "range (\<lambda>a. buildNotinSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

lemma buildnotin_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildNotinSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildNotinSBE a c)"
    by (simp add: buildnotin_range)
  hence "\<exists>prod. sbe = buildNotinSBE prod"
      apply(simp add: fun_eq_iff f_inv_into_f image_iff)
    by (metis (full_types) inNot.exhaust)
  thus ?thesis
    by auto
qed

abbreviation "buildNotinSB \<equiv> inNotChan (Rep_cfun (smap (Tsyn o (map_option) \<B>)))" 

lemma buildnotinsb_ctype: "sValues\<cdot>(buildNotinSB a c) \<subseteq> ctype (Rep c)"
  apply(cases c)
  apply auto
  by (metis image_iff range_eqI rangecout smap_sValues)


lemma rep_cfun_smap_bool_inj:"inj (Rep_cfun (smap (Tsyn o (map_option) \<B>)))"
  apply(rule smap_inj) 
  by simp

lemma buildnotinsb_inj: "inj buildNotinSB"
   by (metis (mono_tags, lifting) inNotChan.simps inj_def rep_cfun_smap_bool_inj)

lemma buildnotinsb_range: "(\<Union>a. sValues\<cdot>(buildNotinSB a c)) = ctype (Rep c)"
  apply(auto;cases c)
  using buildnotinsb_ctype apply blast
  apply(rule_tac x="\<up>(inv (Tsyn \<circ> map_option \<B>)x)" in exI,auto)
  by (metis comp_apply f_inv_into_f rangecout)
 
lemma buildnotinsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildNotinSB"
proof -
  have ctypewell:"\<And> c. sValues\<cdot>(sb c) \<subseteq> ctype (Rep c)"
    using assms
    by (simp add: sb_well_def) 
  hence "\<exists>prod. sb = buildNotinSB prod"
    apply(subst fun_eq_iff,auto,simp add: sValues_def)
  proof -
    have f1: "\<forall>i M. sValues\<cdot>(sb i) \<subseteq> M \<or> \<not> ctype (Rep i) \<subseteq> M"
      by (metis ctypewell dual_order.trans)
    have "ctype (Rep Notin) \<subseteq> range(Tsyn o (map_option) \<B>)"
      by (metis buildnotin_range image_cong inNotChan.simps set_eq_subset)
    then show "\<exists>s. \<forall>i. sb i = buildNotinSB s i"
      using f1 by (smt inNot.exhaust inNotChan.simps sValues_def smap_well)
  qed 
  thus ?thesis
    by auto
qed


end