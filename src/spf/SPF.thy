(*<*)(*:maxLineLen=68:*)
theory SPF

imports bundle.SB

begin
(*>*)
section \<open>Stream Processing Functions \label{sec:spf}\<close>

text\<open>A deterministic component can be  modeled by a \Gls{spf}.
Since we there is no restriction for be \gls{spf}, beside being
continuous, we do not introduce an extra type for \Gls{spf}, because
it is only a type synonym.\<close>

type_synonym ('I,'O) SPF = "('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)"

text\<open>However, we will introduce a function to convert the domain of 
a component. Similar to @{const sbConvert}\ref{subsub.sbconvert}
this makes it possible to evaluate the equality of two components
with the same domains but different types. It also allows us to
restrict input or output domains, hence it can be used for hiding 
channels.\<close>

definition spfConvert::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<rightarrow> ('Ie\<^sup>\<Omega> \<rightarrow> 'Oe\<^sup>\<Omega>)" where
"spfConvert \<equiv> \<Lambda> f sb. (f\<cdot>(sb\<star>)\<star>)"

lemma spfconvert_eq [simp]: "spfConvert\<cdot>f = f"
  apply(rule cfun_eqI)
  by(simp add: spfConvert_def)

subsection \<open>Causal SPFs \label{sub:cspf}\<close>

text\<open>However, we will introduce types for causal \Gls{spf}. Beside
the continuity of the components also its causality is important for
its realizeability. This section introduces two predicates to 
distinguish between strong, weak, and non-causal \Gls{spf}. The 
causal \gls{spf} types are a direct consequence from the predicates.
Strong causal components are a subset of weak causal. A weak causal
component is realizable, but we also introduce a type for strong 
causal components for their compositional properties. In general,
both causal types do not contain a \<open>\<bottom>\<close> element, because this would
be inconsistent with our time model.\<close>

subsubsection \<open>Weak SPF\<close>

text\<open>Weak causal \Gls{spf} can not look into the future. Their
output must depend completely on their previous input. Since we
interpret a stream bundle element as a time slice, @{const sbLen}
\ref{subsub:sblen} is enough to restrict the behaviour to a causal
one. If the output of a \gls{spf} is longer or equally long to the
input, it consists of as least as many time slices as the input.
Hence, we can define as weak, if the output is in all cases at least
as long as the input.\<close>

definition weak_well::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<Rightarrow> bool" where
"weak_well spf = (\<forall>sb. sbLen sb \<le> sbLen (spf\<cdot>sb))"

text\<open>Now we can immediately construct a type for weal causal 
\Gls{spf} with the @{const weak_well} Predicate.\<close>
(*<*)
definition sometimesspfw::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)"where
"sometimesspfw = (\<Lambda> sb. Abs_sb(\<lambda>c. sinftimes 
                  (\<up>(SOME a. a \<in> ctype (Rep c)))))"

lemma sometimesspfw_well:
"\<not>chDomEmpty TYPE('cs) \<Longrightarrow> 
 sb_well (\<lambda>c::'cs. sinftimes (\<up>(SOME a. a \<in> ctype (Rep c))))"
  apply(auto simp add: sb_well_def)
  using cEmpty_def cnotempty_rule some_in_eq by auto

lemma sometimesspfw_len:
"\<not>chDomEmpty TYPE('cs) \<Longrightarrow> sbLen ((sometimesspfw\<cdot>sb)::'cs\<^sup>\<Omega>) = \<infinity>"
  apply(rule sblen_rule,simp_all add: sometimesspfw_def 
        sbgetch_insert2)
  by(simp add: Abs_sb_inverse sometimesspfw_well)+

lemma weak_well_adm:"adm weak_well"
  unfolding weak_well_def
  apply (rule admI)   
  apply auto
  by (meson is_ub_thelub  cfun_below_iff sblen_mono lnle_def 
      monofun_def less_lnsuc order_trans)

lemma strong_spf_exist:" \<exists>x::('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) . 
  (\<forall>sb. lnsuc\<cdot>(sbLen sb) \<le> sbLen (x\<cdot>sb))"
  apply(cases "chDomEmpty TYPE('O)")
  apply simp
  apply(rule_tac x=sometimesspfw in exI)
  by(simp add:  sometimesspfw_len)
(*>*)

cpodef ('I,'O)spfw = "{f::('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) . weak_well f}"
  apply(simp add: weak_well_def)
  apply (metis (full_types) eq_iff strong_spf_exist fold_inf inf_ub
        le2lnle leI le_cases less_irrefl trans_lnle)
  by (simp add: weak_well_adm)


lemma [simp, cont2cont]:"cont Rep_spfw"
  using cont_Rep_spfw cont_id by blast

lift_definition %invisible Rep_spfw_fun::
"('I,'O)spfw \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow>'O\<^sup>\<Omega>)"is "\<lambda> spfs. Rep_spfw( spfs)"
  by(intro cont2cont)


lemma spf_weakI:
  fixes spf :: "'I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>"
  assumes "\<And>sb. (sbLen sb) \<le> sbLen (spf\<cdot>sb)"
  shows "weak_well spf"
  by(simp add: weak_well_def assms)

lemma spf_weakI2:
  fixes spf :: "'I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>"
  assumes "\<not>chDomEmpty TYPE('I)"
    and "\<And>sb s. sbLen sb < \<infinity> \<Longrightarrow> sbLen sb \<le> sbLen (spf\<cdot>sb)"
  shows "weak_well spf"
proof-
  have "\<And>sb. sbLen sb = \<infinity> \<Longrightarrow> sbLen sb \<le> sbLen (spf\<cdot>sb)"
  proof (rule ccontr)
    fix sb::"'I\<^sup>\<Omega>"
    assume sb_len: "sbLen sb = \<infinity>"
      and not_weak: "\<not> sbLen sb \<le> sbLen (spf\<cdot>sb)"
    then obtain k where out_len: "sbLen (spf\<cdot>sb) = Fin k"
      by (metis le_less_linear lnat_well_h2)
    have sbtake_sb_len: "sbLen (sbTake (Suc k)\<cdot>sb) = Fin (Suc k)"
      by (simp add: assms sbtake_len sb_len)
    have "sbLen (spf\<cdot>(sbTake (Suc k)\<cdot>sb)) \<le> sbLen (spf\<cdot>sb)"
      using monofun_cfun_arg sblen_monosimp sbtake_below by blast
    thus False
      by (metis Fin_Suc Fin_leq_Suc_leq SBv3.lnat.inject assms(2) 
          le_less_linear less2eq less_lnsuc n_not_Suc_n 
          notinfI3 out_len sbtake_sb_len)
  qed
  thus ?thesis
    by (metis assms(2) inf_ub order.not_eq_order_implies_strict 
        weak_well_def)
qed

subsubsection \<open>Strong SPF \<close>

text\<open>Strong causal \Gls{spf} model weak components, whose output 
never depends on the current input. Thus, its output only depends on
earlier input. This property is again definable with @{const sbLen}.
Here we have to mind that an input can be infinitely long, hence,
the output will not always be longer than the input. Therefore, we 
use a increment instead of the smaller relation.\<close>

definition strong_well::"('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>) \<Rightarrow> bool" where
"strong_well spf = (\<forall>sb. lnsuc\<cdot>(sbLen sb) \<le> sbLen (spf\<cdot>sb))"

text\<open>Now it is easy to show, that every strong component is also a
weak component.\<close>

theorem strong2weak:"\<And>f. strong_well f \<Longrightarrow> weak_well f"
  using less_lnsuc strong_well_def trans_lnle weak_well_def by blast

lemma strong_well_adm:
"adm (\<lambda>x::('I, 'O) spfw. strong_well (Rep_spfw x))"
  unfolding strong_well_def
  apply (rule admI)
  apply auto
  by (meson is_ub_thelub below_spfw_def cfun_below_iff sblen_mono 
      lnle_def monofun_def less_lnsuc order_trans)

text\<open>Following this property, we define the strong \gls{spf} type as
a subset of the weak type.\<close>

cpodef ('I,'O)spfs = "{f::('I,'O)spfw . strong_well (Rep_spfw f)}"
  apply (metis Rep_spfw_cases mem_Collect_eq strong2weak 
         strong_spf_exist strong_well_def)
  by(simp add: strong_well_adm)

lemma [simp, cont2cont]:"cont Rep_spfs"
  using cont_Rep_spfs cont_id by blast

lift_definition %invisible Rep_spfs_fun::
"('I,'O)spfs \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow>'O\<^sup>\<Omega>)"is "\<lambda> spfs. Rep_spfw_fun\<cdot>(Rep_spfs spfs)"
  by(intro cont2cont)

lemma spf_strongI:
  fixes spf :: "'I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>"
  assumes "\<And>sb. lnsuc\<cdot>(sbLen sb) \<le> sbLen (spf\<cdot>sb)"
  shows "strong_well spf"
  by(simp add: strong_well_def assms)

subsection \<open>SPS \label{sec:sps}\<close>

text\<open>The behaviour of under-specified or nondeterministic components
can often not be modeled by a single \gls{spf} but by a set of 
\Gls{spf}. Similar to the \gls{spf} type, we define \gls{sps} type 
as a type synonym.\<close> 

type_synonym ('I,'O)SPS = "('I,'O)SPF set"

(*<*)
end
(*>*)