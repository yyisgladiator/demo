(*<*)(*:maxLineLen=68:*)
theory SPF
(*>*)
imports bundle.SB

begin

section \<open> Causal SPFs\<close>

subsection \<open>Weak SPF\<close>

subsubsection \<open>Weak SPF definition \<close>

definition weak_well::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<Rightarrow> bool" where
"weak_well spf = (\<forall>sb. sbLen sb \<le> sbLen (spf\<cdot>sb))"

definition sometimesspfw::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)"where
"sometimesspfw = (\<Lambda> sb. Abs_sb(\<lambda>c. sinftimes (\<up>(SOME a. a \<in> ctype (Rep c)))))"

lemma sometimesspfw_well:"\<not>chIsEmpty TYPE('cs) 
                          \<Longrightarrow> sb_well (\<lambda>c::'cs. sinftimes (\<up>(SOME a. a \<in> ctype (Rep c))))"
  apply(auto simp add: sb_well_def)
  using cEmpty_def cnotempty_rule some_in_eq by auto

lemma sometimesspfw_len:"\<not>chIsEmpty TYPE('cs) \<Longrightarrow> sbLen ((sometimesspfw\<cdot>sb)::'cs\<^sup>\<Omega>) = \<infinity>"
  apply(rule sblen_rule,simp_all add: sometimesspfw_def sbgetch_insert2)
  by(simp add: Abs_sb_inverse sometimesspfw_well)+

lemma weak_well_adm:"adm weak_well"
  unfolding weak_well_def
  apply (rule admI)   
  apply auto
  by (meson is_ub_thelub  cfun_below_iff sblen_mono lnle_def monofun_def  less_lnsuc order_trans)

lemma strong_spf_exist:" \<exists>x::('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) . (\<forall>sb. lnsuc\<cdot>(sbLen sb) \<le> sbLen (x\<cdot>sb))"
  apply(cases "chIsEmpty TYPE('O)")
  apply simp
  apply(rule_tac x=sometimesspfw in exI)
  by(simp add:  sometimesspfw_len)

cpodef ('I::chan,'O::chan)spfw = "{f::('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) . weak_well f}"
  apply(simp add: weak_well_def)
  apply (metis (full_types) eq_iff strong_spf_exist fold_inf inf_ub le2lnle leI le_cases 
        less_irrefl trans_lnle)
  by (simp add: weak_well_adm)

lemma [simp, cont2cont]:"cont Rep_spfw"
  using cont_Rep_spfw cont_id by blast

lift_definition Rep_spfw_fun::"('I::chan,'O::chan)spfw \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow>'O\<^sup>\<Omega>)"is
"\<lambda> spfs. Rep_spfw( spfs)"
  by(intro cont2cont)

subsubsection \<open>Weak SPF functions \<close>

subsubsection \<open>Weak SPF lemmas\<close>

subsection \<open>Strong SPF \<close>

subsubsection \<open>Strong SPF definition\<close>

definition strong_well::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<Rightarrow> bool" where
"strong_well spf = (\<forall>sb. lnsuc\<cdot>(sbLen sb) \<le> sbLen (spf\<cdot>sb))"

lemma strong2weak:" \<And> f. strong_well f \<Longrightarrow> weak_well f"
  using less_lnsuc strong_well_def trans_lnle weak_well_def by blast

lemma strong_well_adm:"adm (\<lambda>x::('I, 'O) spfw. strong_well (Rep_spfw x))"
  unfolding strong_well_def
  apply (rule admI)
  apply auto
  by (meson is_ub_thelub below_spfw_def cfun_below_iff sblen_mono 
      lnle_def monofun_def less_lnsuc order_trans)

cpodef ('I::chan,'O::chan)spfs = "{f::('I,'O)spfw . strong_well (Rep_spfw f)}"
   apply (metis Rep_spfw_cases mem_Collect_eq strong2weak strong_spf_exist strong_well_def)
  by(simp add: strong_well_adm)

lemma [simp, cont2cont]:"cont Rep_spfs"
  using cont_Rep_spfs cont_id by blast

subsubsection \<open>Strong SPF functions\<close>

lift_definition Rep_spfs_fun::"('I::chan,'O::chan)spfs \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow>'O\<^sup>\<Omega>)"is
"\<lambda> spfs. Rep_spfw_fun\<cdot>(Rep_spfs spfs)"
  by(intro cont2cont)


subsubsection \<open>Strong SPF lemmas\<close>
(*<*)
end
(*>*)