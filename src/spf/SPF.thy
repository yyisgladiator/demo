theory SPF

imports bundle.SB SPFcomp

begin

section \<open> Causal SPFs\<close>

subsection \<open>Weak SPF\<close>

subsubsection \<open>Weak SPF definition \<close>

definition weak_well::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<Rightarrow> bool" where
"weak_well spf = (\<forall>sb. sbLen sb \<le> sbLen (spf\<cdot>sb))"

definition sometimesspfw::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)"where
"sometimesspfw = (\<Lambda> sb. Abs_sb(\<lambda>c. sinftimes (\<up>(SOME a. a \<in> ctype (Rep c)))))"

lemma sblen_leadm:"adm (\<lambda>sb. k \<le> sbLen sb)"
  oops

lemma sblen_ladm:"adm (\<lambda>sb. k <\<^sup>l sbLen sb)"
  oops

cpodef ('I::chan,'O::chan)spfw = "{f::('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) . weak_well f}"
  apply(simp add: weak_well_def)
  apply(cases "chIsEmpty TYPE('O)")
  apply(subgoal_tac "\<forall>sb::'O\<^sup>\<Omega>. sbLen sb = \<infinity>",auto)
(*  defer(*lemma for sbLen*)
  apply(rule_tac x="sometimesspfw" in exI)
  defer (*lemma sbLen (sometimesspfw\<cdot>sb) = \<infinity> with assumption*)
  apply(simp add: weak_well_def)
  apply(rule adm_all)(*lemma sblen_leadm*)
  apply(rule admI)*)
  sorry

lemma [simp, cont2cont]:"cont Rep_spfw"
  using cont_Rep_spfw cont_id by blast

lift_definition Rep_spfw_fun::"('I::chan,'O::chan)spfw \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow>'O\<^sup>\<Omega>)"is
"\<lambda> spfs. Rep_spfw( spfs)"
  by(intro cont2cont)

subsubsection \<open>Weak SPF functions \<close>

definition spfcomp_w::"('I::chan,'O::chan)spfw \<rightarrow>  ('I2::chan,'O2::chan)spfw \<rightarrow> ('I3::chan,'O3::chan)spfw"where
"spfcomp_w \<equiv> (\<Lambda> spf1 spf2. Abs_spfw(genComp\<cdot>(Rep_spfw spf1)\<cdot>(Rep_spfw spf2)))"

subsubsection \<open>Weak SPF lemmas\<close>

subsection \<open>Strong SPF \<close>

subsubsection \<open>Strong SPF definition\<close>
(*If 'O is empty (then there is no weak function*)
definition strong_well::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<Rightarrow> bool" where
"strong_well spf = (\<forall>sb. lnsuc\<cdot>(sbLen sb) \<le> sbLen (spf\<cdot>sb))"

cpodef ('I::chan,'O::chan)spfs = "{f::('I,'O)spfw . strong_well (Rep_spfw f)}"
  apply(simp add: strong_well_def)
  apply(cases "chIsEmpty TYPE('O)")
  apply(subgoal_tac "\<forall>sb::'O\<^sup>\<Omega>. sbLen sb = \<infinity>",auto)
(*  defer(*lemma for sbLen*)
  apply(rule_tac x="Abs_spfw(sometimesspfw)" in exI)
  defer (*lemma spfw_well sometimesspfw with assumption*)
  apply(simp add: strong_well_def)
  apply(rule adm_all)(*lemma sblen_ladm*)
  apply(rule admI)*)
  sorry

lemma [simp, cont2cont]:"cont Rep_spfs"
  using cont_Rep_spfs cont_id by blast

subsubsection \<open>Strong SPF functions\<close>

lift_definition Rep_spfs_fun::"('I::chan,'O::chan)spfs \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow>'O\<^sup>\<Omega>)"is
"\<lambda> spfs. Rep_spfw_fun\<cdot>(Rep_spfs spfs)"
  by(intro cont2cont)

definition spfcomp_s::"('I::chan,'O::chan)spfs \<rightarrow>  ('I2::chan,'O2::chan)spfs \<rightarrow> ('I3::chan,'O3::chan)spfs"where
"spfcomp_s \<equiv> (\<Lambda> spf1 spf2. Abs_spfs(spfcomp_w\<cdot>(Rep_spfs spf1)\<cdot>(Rep_spfs spf2)))"


subsubsection \<open>Strong SPF lemmas\<close>

end
