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
    apply(cases c; cases a;simp)
  by(simp_all add: ctype_def)
lemma buildandout_inj: "inj buildAndoutSBE"
   apply (auto simp add: inj_def)
  by (metis outAndChan.simps inj_def inj_B inj_tsyncons)+

lemma buildandout_range: "range (\<lambda>a. buildAndoutSBE a c) = ctype (Rep c)"
 apply(cases c)
  apply(auto simp add: image_iff ctype_def)
  by (metis option.simps(9))+
lemma buildandout_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildAndoutSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildAndoutSBE a c)"
    by (simp add: buildandout_range)
  hence "\<exists>prod. sbe = buildAndoutSBE prod"
      apply(simp add: fun_eq_iff f_inv_into_f image_iff)
    by (metis (full_types) outAnd.exhaust)
  thus ?thesis
    by auto
qed

abbreviation "buildAndoutSB \<equiv> outAndChan (Rep_cfun (smap (Tsyn o (map_option) \<B>)))" 



lemma buildandoutsb_ctype: "sValues\<cdot>(buildAndoutSB a c) \<subseteq> ctype (Rep c)"

 apply(cases c)
  apply auto
   by (metis Andout1_rep buildandout_ctype f_inv_into_f outAndChan.simps smap_sValues)

lemma rep_cfun_smap_bool_inj:"inj (Rep_cfun (smap (Tsyn o (map_option) \<B>)))"
  apply(rule smap_inj)
  by simp


lemma buildandoutsb_inj: "inj buildAndoutSB"
  apply(rule injI)
 
  by (metis outAndChan.simps inj_eq old.prod.exhaust rep_cfun_smap_bool_inj)




lemma buildandoutsb_range: "(\<Union>a. sValues\<cdot>(buildAndoutSB a c)) = ctype (Rep c)"
  apply(cases c)
  apply auto
  apply (metis (no_types, lifting) Andout1_rep buildandoutsb_ctype contra_subsetD outAndChan.simps)
  apply(rule_tac x="\<up>(inv (Tsyn \<circ> map_option \<B>)x)" in exI,auto)
  apply (smt Andout1_rep buildandout_range comp_apply f_inv_into_f outAndChan.elims rangeI)
  done



  
lemma buildandoutsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildAndoutSB"
proof -
  have ctypewell:"\<And> c. sValues\<cdot>(sb c) \<subseteq> ctype (Rep c)"
    using assms
    by (simp add: sb_well_def) 
  hence "\<exists>prod. sb = buildAndoutSB prod"
    apply(subst fun_eq_iff,auto,simp add: sValues_def)
  proof -
    have f1: "\<forall>i M. sValues\<cdot>(sb i) \<subseteq> M \<or> \<not> ctype (Rep i) \<subseteq> M"
      by (metis ctypewell dual_order.trans)
    have  "ctype (Rep Andout) \<subseteq> range(Tsyn o (map_option) \<B>)"
          by (metis buildandout_range image_cong outAndChan.simps set_eq_subset)
  
    then show "\<exists>a . \<forall>i. sb i = buildAndoutSB a i"
      using f1  by (smt outAnd.exhaust outAndChan.simps sValues_def smap_well)
  qed 
  thus ?thesis
    by auto
qed


end