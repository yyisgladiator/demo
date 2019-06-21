theory SPF

imports bundle.SB

begin

section \<open> Causal SPFs\<close>


definition strong_weak_ex::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"strong_weak_ex = (\<Lambda> sb. Abs_sb(\<lambda>c. sinftimes(\<up>eps)))" (*doesnt work, because of ctype*)

subsection \<open>Weak SPF\<close>

subsubsection \<open>Weak SPF definition \<close>

definition weak_well::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<Rightarrow> bool" where
"weak_well spf = (\<forall>sb. sbLen sb \<le> sbLen (spf\<cdot>sb))"

typedef ('I::chan,'O::chan)spfw = "{f::('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) . weak_well f}"
  apply(simp add: weak_well_def)
  sorry

subsubsection \<open>Weak SPF lemmas\<close>

subsection \<open>Strong SPF \<close>

subsubsection \<open>Strong SPF definition\<close>


definition strong_well::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<Rightarrow> bool" where
"strong_well spf = (\<forall>c. sbLen c \<le> lnsuc\<cdot>(sbLen (spf\<cdot>c)))"

typedef ('I::chan,'O::chan)spfs = "{f::('I,'O)spfw . strong_well (Rep_spfw f)}"
  apply(simp add: strong_well_def)
  sorry

subsubsection \<open>Strong SPF lemmas\<close>

end
