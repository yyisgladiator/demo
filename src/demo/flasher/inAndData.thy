theory inAndData

imports bundle.SB
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
  apply (metis Rep_inAnd ctype.simps(4) ctype.simps(5) ctype.simps(6) ex_in_conv insertE insert_iff)
  apply (meson Rep_inAnd_inject injI) using ctype.elims Rep_inAnd apply simp
  apply (metis ctype.simps(2) ctype.simps(4) ctype.simps(5) emptyE image_iff iso_tuple_UNIV_I)
  using type_definition.Abs_image type_definition_inAnd typedef_finite_UNIV by fastforce
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

abbreviation "buildAndinSB \<equiv> inAndChan (Rep_cfun (smap \<B>)) (Rep_cfun (smap \<B>))" 
lemma buildandoutsb_ctype: "sdom\<cdot>(buildAndinSB a c) \<subseteq> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma smap_inj:"inj f \<Longrightarrow> inj (Rep_cfun (smap f))"
  apply(rule injI)
  apply(rule snths_eq,auto)
  apply (metis slen_smap)
  by (metis inj_eq slen_smap smap_snth_lemma)

lemma rep_cfun_smap_bool_inj:"inj (Rep_cfun (smap \<B>))"
  apply(rule smap_inj)
  by(simp add: inj_def)+

lemma buildNotoutsb_inj: "inj buildAndinSB"
  apply(rule injI)
 
  by (metis inAndChan.simps(1) inAndChan.simps(2) inj_eq old.prod.exhaust rep_cfun_smap_bool_inj)

lemma buildflashoutsb_range: "(\<Union>a. sdom\<cdot>(buildAndinSB a c)) = ctype (Rep c)"
  apply(cases c)
  apply auto 
  apply (metis (no_types, lifting) in_mono smap_sdom_range)
  apply(rule_tac x="\<up>xa" in exI)
  apply simp
  using smap_sdom_range apply blast
  apply(rule_tac x="\<up>xa" in exI)
  by simp
lemma smap_well:"range f = S \<Longrightarrow> sdom\<cdot>x\<subseteq>S \<Longrightarrow>  \<exists>s. smap f\<cdot>s = x"

 
  sorry

lemma buildflashoutsb_surj: assumes "sb_well sb"
  shows "sb \<in> range buildAndinSB"
proof -
  have ctypewell:"\<And> c. sValues (sb c) \<subseteq> ctype (Rep c)"
    using assms
    by (simp add: sb_well_def) 
  hence "\<exists>prod. sb = buildAndinSB prod"
    apply(subst fun_eq_iff,auto,simp add: sValues_def)
      proof -
have f1: "\<forall>i M. sValues (sb i) \<subseteq> M \<or> \<not> ctype (Rep i) \<subseteq> M"
  by (metis ctypewell dual_order.trans)
  have f2:"ctype (Rep Andin1) \<subseteq> range \<B>"
    by force
  have f3:"ctype (Rep Andin2) \<subseteq> range \<B>"
    by force
  then show "\<exists>a b. \<forall>i. sb i = buildAndinSB (a ,b)  i"
    using  f2 f1
    sorry
  qed
    thus ?thesis
    by auto
qed

end