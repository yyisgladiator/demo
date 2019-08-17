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
  apply(auto simp add: ctype_empty_iff)
  using ctype_empty_iff
  apply (metis Rep_outNot cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_outNot_inject injI) using cMsg.elims Rep_outNot apply simp
  using type_definition.Abs_image type_definition_outNot typedef_finite_UNIV by fastforce
end

definition "Notout \<equiv> Abs_outNot cin2"

free_constructors outNot for "Notout"
  by (metis(full_types) Abs_outNot_cases singletonD)

lemma Notout1_rep [simp]: "Rep (Notout) = cin2"
  by (simp add: Abs_outNot_inverse Notout_def Rep_outNot_def)

fun outNotChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outNot \<Rightarrow> 'a" where
"outNotChan Cc1 bool Notout = Cc1 bool"

abbreviation "buildNotoutSBE \<equiv> outNotChan (Tsyn o (map_option) \<B>)" 

lemma rangecin2[simp]:"range (Tsyn o (map_option) \<B>) = ctype cin2"
  apply(auto simp add: ctype_def)
  by (metis option.simps(9) range_eqI)

lemma buildnotout_ctype: "buildNotoutSBE a c \<in> ctype (Rep c)"
  apply(cases c; cases a;simp)
  by(simp_all add: ctype_def)

lemma buildnotout_inj: "inj buildNotoutSBE"
  apply (auto simp add: inj_def)
  by (metis outNotChan.simps inj_def inj_B inj_tsyncons)+

lemma buildnotout_range: "range (\<lambda>a. buildNotoutSBE a c) = ctype (Rep c)"
  apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+

lemma buildnotout_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildNotoutSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildNotoutSBE a c)"
    by (simp add: buildnotout_range)
  hence "\<exists>prod. sbe = buildNotoutSBE prod"
      apply(simp add: fun_eq_iff f_inv_into_f image_iff)
    by (metis (full_types) outNot.exhaust)
  thus ?thesis
    by auto
qed

abbreviation "buildNotoutSB \<equiv> outNotChan (Rep_cfun (smap (Tsyn o (map_option) \<B>)))" 

lemma buildnotoutsb_ctype: "sValues\<cdot>(buildNotoutSB a c) \<subseteq> ctype (Rep c)"
 apply(cases c)
 apply auto
 by (metis image_iff range_eqI rangecin2 smap_sValues)

lemma rep_cfun_smap_bool_inj:"inj (Rep_cfun (smap (Tsyn o (map_option) \<B>)))"
  apply(rule smap_inj)
  by simp

lemma buildnotoutsb_inj: "inj buildNotoutSB"
   by (metis (mono_tags, lifting) outNotChan.simps inj_def rep_cfun_smap_bool_inj)

lemma buildnotoutsb_range: "(\<Union>a. sValues\<cdot>(buildNotoutSB a c)) = ctype (Rep c)"
  apply(auto;cases c)
  using buildnotoutsb_ctype apply blast
  apply(rule_tac x="\<up>(inv (Tsyn \<circ> map_option \<B>)x)" in exI,auto)
  by (metis comp_apply f_inv_into_f rangecin2)
  
lemma buildnotoutsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildNotoutSB"
proof -
  have ctypewell:"\<And> c. sValues\<cdot>(sb c) \<subseteq> ctype (Rep c)"
    using assms
    by (simp add: sb_well_def) 
  hence "\<exists>prod. sb = buildNotoutSB prod"
    apply(subst fun_eq_iff,auto,simp add: sValues_def)
  proof -
    have f1: "\<forall>i M. sValues\<cdot>(sb i) \<subseteq> M \<or> \<not> ctype (Rep i) \<subseteq> M"
      by (metis ctypewell dual_order.trans)
    have "ctype (Rep Notout) \<subseteq> range(Tsyn o (map_option) \<B>)"
      by (metis buildnotout_range image_cong outNotChan.simps set_eq_subset)
    then show "\<exists>s. \<forall>i. sb i = buildNotoutSB s i"
      using f1 by (smt outNot.exhaust outNotChan.simps sValues_def smap_well)
  qed 
  thus ?thesis
    by auto
qed

end