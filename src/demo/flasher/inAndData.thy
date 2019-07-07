theory inAndData

imports bundle.sbElem
begin

typedef inAnd="{cin1,cin2}"
  by auto

instantiation inAnd::"{somechan,finite}"
begin
definition "Rep = Rep_inAnd"
instance
  apply(standard)
  apply(auto simp add: Rep_inAnd_def cEmpty_def)
  using ctype.elims
  apply (metis Rep_inAnd ctype.simps(4) ctype.simps(5) ctype.simps(6) ex_in_conv insertE insert_iff insert_not_empty sup_eq_bot_iff)
  apply (meson Rep_inAnd_inject injI)
  sorry
end

definition "Andin1 \<equiv> Abs_inAnd cin1"
definition "Andin2 \<equiv> Abs_inAnd cin2"

free_constructors inAnd for "Andin1"  | "Andin2"
   apply auto
  unfolding Andin1_def Andin2_def
  apply (metis Rep_inAnd Rep_inAnd_inverse empty_iff insert_iff)
  by (simp add: Abs_inAnd_inject)

lemma Andin1_rep [simp]: "Rep (Andin1) = cin1"
  by (simp add: Abs_inAnd_inverse Andin1_def Rep_inAnd_def)

lemma Andin2_rep [simp]: "Rep (Andin2) = cin2"
  unfolding Rep_inAnd_def Andin2_def
  by (simp add: Abs_inAnd_inverse)

fun inAndChan::"('nat::type \<Rightarrow> 'a::type) \<Rightarrow> ('bool::type \<Rightarrow> 'a) \<Rightarrow>('nat\<times>'bool) \<Rightarrow> inAnd \<Rightarrow> 'a" where
"inAndChan Cc1 Cc2 (port_c1, port_c2) Andin1 = Cc1 port_c1" |
"inAndChan Cc1 Cc2 (port_c1, port_c2) Andin2 = Cc2 port_c2"

abbreviation "buildAndinSBE \<equiv> inAndChan \<B> \<B>" 

lemma buildandin_ctype: "buildAndinSBE a c \<in> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma buildandin_inj: "inj buildAndinSBE"
  apply(rule injI)
  apply(case_tac x; case_tac y; simp)
  by (metis M.inject(2) inAndChan.simps)+

lemma buildandin_range: "range (\<lambda>a. buildAndinSBE a c) = ctype (Rep c)"
  apply(cases c)
  by(auto simp add: image_iff)

lemma buildandin_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildAndinSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildAndinSBE a c)"
    by (simp add: buildandin_range)
  hence "\<exists>prod. sbe = buildAndinSBE prod"
    apply(subst fun_eq_iff,auto)
    by (smt Andin1_rep Andin2_rep ctype.simps(4) ctype.simps(5) ctypewell imageE inAnd.exhaust inAndChan.simps(1) inAndChan.simps(2)) (*TODO: no smt*)
  thus ?thesis
    by auto
qed

end