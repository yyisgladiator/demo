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
  apply(auto simp add: Rep_inNot_def)
  apply (metis Rep_inNot singletonD)
  apply (meson Rep_inNot_inject injI)
  apply(simp add: cEmpty_def)
  sorry
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
lemma buildflashoutsb_ctype: "sdom\<cdot>(buildNotinSB a c) \<subseteq> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma smap_inj:"inj f \<Longrightarrow> inj (Rep_cfun (smap f))"
  apply(rule injI)
  apply(rule snths_eq,auto)
  apply (metis slen_smap)
  by (metis inj_eq slen_smap smap_snth_lemma)

lemma rep_cfun_smap_bool_inj:"inj (Rep_cfun (smap \<B>))"
  apply(rule smap_inj)
  by(simp add: inj_def)+

lemma buildNotoutsb_inj: "inj buildNotinSB"
  by (metis (mono_tags, hide_lams) inNotChan.simps inj_def rep_cfun_smap_bool_inj)

lemma buildflashoutsb_range: "(\<Union>a. sdom\<cdot>(buildNotinSB a c)) = ctype (Rep c)"
  apply(cases c)
  apply auto 
  apply (metis (no_types, lifting) in_mono smap_sdom_range)
  apply(rule_tac x="\<up>xa" in exI)
  by simp


lemma smap_well:"range f = S \<Longrightarrow> sdom\<cdot>x\<subseteq>S \<Longrightarrow>  \<exists>s. smap f\<cdot>s = x"

 
  sorry

lemma buildflashoutsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildNotinSB"
proof -
  have ctypewell:"\<And> c. sValues (sb c) \<subseteq> ctype (Rep c)"
    using assms
    by (simp add: sb_well_def) 
  hence "\<exists>prod. sb = buildNotinSB prod"
    apply(subst fun_eq_iff,auto,simp add: sValues_def)
 
  proof -
have f1: "\<forall>i M. sValues (sb i) \<subseteq> M \<or> \<not> ctype (Rep i) \<subseteq> M"
  by (metis ctypewell dual_order.trans)
  have "ctype (Rep Notin) \<subseteq> range \<B>"
    by force
then show "\<exists>s. \<forall>i. sb i = buildNotinSB s i"
using f1 by (metis (full_types) inNotChan.elims sValues_def smap_well)
qed  thus ?thesis
    by auto
qed

end