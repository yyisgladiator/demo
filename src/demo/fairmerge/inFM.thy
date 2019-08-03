theory inFM

imports bundle.SB
begin

typedef inFM="{cin1,cin2}"
  by auto


instantiation inFM::"{somechan,finite}"
begin
definition "Rep = Rep_inFM"
instance
  apply(standard)
  apply(auto simp add: Rep_inFM_def cEmpty_def)
  using ctype.elims
  apply (metis Rep_inFM ctype.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_inFM_inject injI) using ctype.elims Rep_inFM apply simp
  apply (metis ctype.simps emptyE image_iff iso_tuple_UNIV_I)
  using type_definition.Abs_image type_definition_inFM typedef_finite_UNIV by fastforce
end

definition "FMin1 \<equiv> Abs_inFM cin1"
definition "FMin2 \<equiv> Abs_inFM cin2"

free_constructors inFM for "FMin1"  | "FMin2"
  apply auto
  unfolding FMin1_def FMin2_def
  apply (metis Rep_inFM Rep_inFM_inverse empty_iff insert_iff)
  by (simp add: Abs_inFM_inject)

lemma FMin1_rep [simp]: "Rep (FMin1) = cin1"
  by (simp add: Abs_inFM_inverse FMin1_def Rep_inFM_def)

lemma FMin2_rep [simp]: "Rep (FMin2) = cin2"
  unfolding Rep_inFM_def FMin2_def
  by (simp add: Abs_inFM_inverse)

fun inFMChan::"('nat::type \<Rightarrow> 'a::type) \<Rightarrow> ('bool::type \<Rightarrow> 'a) \<Rightarrow>('nat\<times>'bool) \<Rightarrow> inFM \<Rightarrow> 'a" where
"inFMChan Cc1 Cc2 (port_c1, port_c2) FMin1 = Cc1 port_c1" |
"inFMChan Cc1 Cc2 (port_c1, port_c2) FMin2 = Cc2 port_c2"

abbreviation "buildFMinSBE \<equiv> inFMChan \<N> \<N>" 

lemma buildfmin_ctype: "buildFMinSBE a c \<in> ctype (Rep c)"
  by(cases c; cases a;simp)

lemma buildfmin_inj: "inj buildFMinSBE"
  apply(rule injI)
  apply(case_tac x; case_tac y; simp)
  by (metis M.inject(1) inFMChan.simps)

lemma buildfmin_range: "range (\<lambda>a. buildFMinSBE a c) = ctype (Rep c)"
  apply(cases c)
  by(auto simp add: image_iff)

lemma buildfmin_surj: assumes "sbElem_well (Some sbe)"
  shows "sbe \<in> range buildFMinSBE"
proof -
  have ctypewell:"\<And> c. sbe c\<in> ctype (Rep c)"
    using assms by auto
  hence "\<And>c. sbe c \<in> range (\<lambda>a. buildFMinSBE a c)"
    by (simp add: buildfmin_range)
  hence "\<exists>prod. sbe = buildFMinSBE prod"
    apply(subst fun_eq_iff,auto)
    by (smt FMin1_rep FMin2_rep ctype.simps ctypewell imageE inFM.exhaust inFMChan.simps(1) inFMChan.simps(2)) (*TODO: no smt*)
  thus ?thesis
    by auto
qed

abbreviation "buildFMinSB \<equiv> inFMChan (Rep_cfun (smap \<N>)) (Rep_cfun (smap \<N>))" 

end