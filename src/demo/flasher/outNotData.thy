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
  apply(auto simp add: ctype_empty_gdw)
  using ctype_empty_gdw
  apply (metis Rep_outNot cMsg.simps ex_in_conv insertE insert_iff)
  apply (meson Rep_outNot_inject injI) using cMsg.elims Rep_outNot apply simp
  using type_definition.Abs_image type_definition_outNot typedef_finite_UNIV by fastforce
end

definition "Notout \<equiv> Abs_outNot cin2"

free_constructors outNot for "Notout"
  by (metis(full_types) Abs_outNot_cases singletonD)

lemma Andin1_rep [simp]: "Rep (Notout) = cin2"
  by (simp add: Abs_outNot_inverse Notout_def Rep_outNot_def)

fun outNotChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outNot \<Rightarrow> 'a" where
"outNotChan Cc1 bool Notout = Cc1 bool"

abbreviation "buildNotoutSBE \<equiv> outNotChan (Tsyn o (map_option) \<B>)" 

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

end