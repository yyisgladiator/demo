theory SBElem

imports SB tsynBundle

begin
default_sort message

definition sbHdElemWell::"'m::message SB \<Rightarrow> bool" where
"sbHdElemWell  \<equiv> \<lambda> sb. (\<forall>c \<in> ubDom\<cdot>(sb). sb. c \<noteq> \<epsilon>)"  


lemma sbHdElem_below:"sbHdElemWell sb1  \<Longrightarrow> sb1\<sqsubseteq>sb2 \<Longrightarrow>  sbHdElemWell sb2"
  by (metis bottomI sbHdElemWell_def ubdom_below ubgetch_below)

lemma sbelemwell_empty: "sbElemWell Map.empty"
  by(simp add: sbElemWell_def)

typedef 'm sbElem = "{x :: (channel\<rightharpoonup>'m::message) . sbElemWell x}"
  using sbelemwell_empty by blast

setup_lifting type_definition_sbElem



definition sbeDom :: "'a sbElem \<Rightarrow> channel set" where
"sbeDom sbe = dom (Rep_sbElem sbe)"

lift_definition sbeNull :: "channel set \<Rightarrow> 'a::message tsyn sbElem" is
"\<lambda>cs. (\<lambda>c. (c\<in>cs) \<leadsto> ~)"
 unfolding sbElemWell_def
  unfolding usclOkay_stream_def
  unfolding ctype_tsyn_def
  by simp

lift_definition sbe2SB::"'a::message sbElem \<Rightarrow> 'a SB" is
"\<lambda> elem. (\<lambda>c. (c\<in>sbeDom elem) \<leadsto> \<up>(Rep_sbElem elem)\<rightharpoonup>c)"
  unfolding ubWell_def
  unfolding usclOkay_stream_def sbeDom_def
  apply simp
  using Rep_sbElem sbElemWell_def by auto

lift_definition sbeUnion ::"'a sbElem \<Rightarrow> 'a sbElem \<Rightarrow> 'a sbElem" (infixl "\<plusminus>" 100) is
"\<lambda> l r. ((Rep_sbElem l) ++ (Rep_sbElem r))"
 unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def
  by (metis Rep_sbElem domIff map_add_dom_app_simps(1) map_add_dom_app_simps(3) mem_Collect_eq sbElemWellI)


definition SBELEM :: "channel set \<Rightarrow> 'a::message sbElem set" where 
"SBELEM \<equiv> \<lambda> In. {sbe::'a sbElem. sbeDom sbe = In}"

lemma sbeunivI: "\<And> sbe. sbeDom sbe = In \<Longrightarrow> sbe \<in> SBELEM In"
  by (simp add: SBELEM_def)


section \<open>Lemma\<close>

lemma sbe_eq: assumes "sbeDom sbe1 = sbeDom sbe2"
  and "\<And>c. c\<in>sbeDom sbe1 \<Longrightarrow> (Rep_sbElem sbe1)\<rightharpoonup>c =  (Rep_sbElem sbe2)\<rightharpoonup>c"
  shows "sbe1 = sbe2"
  by (metis Rep_sbElem_inject assms(1) assms(2) part_eq sbeDom_def)

lemma Rep_abs_sbElem[simp]:"sbElemWell sbE \<Longrightarrow> Rep_sbElem (Abs_sbElem sbE) = sbE"
  by(simp add: Abs_sbElem_inverse)

lemma sbElem_Elem_well: assumes "E \<in> ctype c" shows "sbElemWell [c \<mapsto> E]"
  unfolding sbElemWell_def usclOkay_stream_def ctype_tsyn_def 
  by(simp add: assms)

lemma sbElem_Elem_well_alt:assumes "c \<in> sbeDom sbE" shows "sbElemWell [c \<mapsto> Rep_sbElem sbE\<rightharpoonup>c]"
  using Rep_sbElem assms sbElem_Elem_well sbElemWellI sbeDom_def by fastforce

lemma Rep_abs_channel_eq[simp]:assumes "c\<in> sbeDom sbE" shows "Rep_sbElem (Abs_sbElem [c \<mapsto> Rep_sbElem sbE\<rightharpoonup>c])\<rightharpoonup>c = Rep_sbElem sbE\<rightharpoonup>c"
  apply(subst Rep_abs_sbElem, auto)
  apply(rule sbElem_Elem_well)
  by(metis Rep_sbElem assms mem_Collect_eq sbElemWell_def sbeDom_def)

subsection \<open>sbe2SB\<close>

lemma sbe2sb_dom [simp]: "ubDom\<cdot>(sbe2SB sbe) = sbeDom sbe"
  by(simp add: sbeDom_def ubdom_insert sbe2SB.rep_eq)

lemma sbe2sb_nbot: "\<And>c. c\<in>sbeDom sbe \<Longrightarrow> (sbe2SB sbe) . c \<noteq> \<epsilon>"
  by(simp add: ubgetch_insert sbe2SB.rep_eq sbeDom_def)

lemma sbe2sb_getch[simp]: "c\<in>sbeDom sbe \<Longrightarrow> ((sbe2SB sbe)  .  c) = \<up>((Rep_sbElem sbe) \<rightharpoonup> c)"
  unfolding ubgetch_insert sbe2SB.rep_eq
  apply auto
  done

lemma sbe2sb_hdelem: "(sbHdElem\<cdot>(sbe2SB sbe)) = convDiscrUp (Rep_sbElem sbe)"
  apply(simp add: sbhdelem_insert)
  apply(rule ext, rename_tac a)
  apply(case_tac "a\<in>sbeDom sbe")
  apply (auto simp add: convDiscrUp_def sbe2sb_getch sup'_def up_def)
  apply (simp add: domD sbeDom_def)
  by (simp add: domI sbeDom_def)

lemma sbe2sb_ubhd: assumes "sbHdElemWell ub"
  shows "sbe2SB (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>ub))) = ubHd\<cdot>ub"
proof -
  let ?In = "ubDom\<cdot>ub"
  have h3: "sbElemWell (inv convDiscrUp (sbHdElem\<cdot>ub))"
    by (meson assms sbHdElemWell_def sbHdElem_sbElemWell)
  have h5: "\<And>c. c \<in> ?In \<Longrightarrow> (\<lambda>c. (c \<in> ?In)\<leadsto>lshd\<cdot>(ub  .  c))\<rightharpoonup>c =
          lshd\<cdot>(ub  .  c)"
    by simp
  have h7: "\<And> c. c \<in> ?In \<Longrightarrow> ub  .  c \<noteq> \<epsilon>"
    by (meson assms sbHdElemWell_def)
  have h8: "\<And>c::channel. c \<in> ?In \<Longrightarrow>
          updis (inv Discr (inv Iup (lshd\<cdot>(ub  .  c)))) && \<epsilon> = stake (Suc (0::nat))\<cdot>(ub  .  c)"
  proof -
    fix c:: channel
    assume a30: "c \<in> ?In"
    obtain daEle rtSt where da_conc: "ub . c = \<up>daEle \<bullet> rtSt"
      using a30 h7 scases by blast
    show "updis (inv Discr (inv Iup (lshd\<cdot>(ub  .  c)))) && \<epsilon> = stake (Suc (0::nat))\<cdot>(ub  .  c)"
      apply (simp add: da_conc)
      by (metis (no_types, hide_lams) Abs_cfun_inverse2 cont_discrete_cpo discr.exhaust iup_inv_iup sup'_def surj_def surj_f_inv_f up_def)
  qed
  have h9: "sbeDom (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>ub)))  = ?In"
    by (simp add: Abs_sbElem_inverse h7 sbHdElem_channel sbHdElem_sbElemWell sbeDom_def)
  show ?thesis
    apply (rule ub_eq)
    apply (simp_all add: h9)
    apply (simp add: h3 Abs_sbElem_inverse)
    apply (simp add: ubHd_def ubTake_def)
    apply (subst ubMapStream_ubGetCh)
      apply (simp add: usclTake_well)
    apply simp
    apply (subst convDiscrUp_inv_subst)
      apply (simp_all add: h7 sbHdElem_channel)
    apply (simp add: sbhdelem_insert)
    apply (simp add: sup'_def usclTake_stream_def)
    by (simp add: h8)
qed

lemma sbe2sb_hdelem_conc: "ubDom\<cdot>sb = sbeDom sbe \<Longrightarrow> (sbHdElem\<cdot>(ubConcEq(sbe2SB sbe)\<cdot>sb)) = sbHdElem\<cdot>(sbe2SB sbe)"
  apply(simp add: sbhdelem_insert ubconceq_insert)
  apply(rule ext, rename_tac a)
  apply(case_tac "a\<in>sbeDom sbe")
  apply (auto simp add: convDiscrUp_def sbe2sb_getch sup'_def up_def)
  by (metis Abs_cfun_inverse2 cont_Iup sconc_scons' stream.sel_rews(4) up_def usclConc_stream_def)

lemma sbe2sb_hdelem2: "(inv convDiscrUp) (sbHdElem\<cdot>(sbe2SB sbe)) = (Rep_sbElem sbe)"
  by (simp add: convDiscrUp_inj sbe2sb_hdelem)

lemma sbe2sb_hdelem3[simp]: "Abs_sbElem ((inv convDiscrUp) (sbHdElem\<cdot>(sbe2SB sbe))) = sbe"
  by (simp add: Rep_sbElem_inverse sbe2sb_hdelem2)

lemma sbe2sb_hdelem4[simp]: "ubDom\<cdot>sb = sbeDom sbe \<Longrightarrow> Abs_sbElem ((inv convDiscrUp) (sbHdElem\<cdot>(ubConcEq(sbe2SB sbe)\<cdot>sb))) = sbe"
  using sbe2sb_hdelem_conc by fastforce

lemma sbe2sb_rt[simp]:"ubDom\<cdot>sb = sbeDom sbe \<Longrightarrow> sbRt\<cdot>(ubConcEq(sbe2SB sbe)\<cdot>sb) = sb"
  apply(rule ub_eq)
   apply simp
  apply (simp add: sbe2sb_getch)
  by (simp add: usclConc_stream_def ubconceq_insert)


lemma sbedom_null[simp]: "sbeDom (sbeNull cs) = cs"
  by(simp add: sbeDom_def sbeNull.rep_eq)

lemma sbe_ch_len: "\<And>c. c\<in> ubDom\<cdot>(sbe2SB sbe) \<Longrightarrow> # ((sbe2SB sbe) . c) = 1"
  by (simp add: one_lnat_def sbe2SB.rep_eq ubgetch_insert)

lemma sbe2sb_len[simp]: "sbeDom sbe \<noteq> {} \<Longrightarrow> ubLen (sbe2SB sbe) = 1"
  apply(simp add: ubLen_def)
  apply(rule Least_equality)
  apply (metis all_not_in_conv sbe2sb_dom sbe_ch_len usclLen_stream_def)
  by (metis order_refl sbe2sb_dom sbe_ch_len usclLen_stream_def)

lemma sbe2sb_maxlen[simp]: "sbeDom sbe \<noteq> {} \<Longrightarrow> ubMaxLen 1 (sbe2SB sbe)"
  apply(auto simp add: ubMaxLen_def)
  apply (simp add: sbe_ch_len usclLen_stream_def)
  by (simp add: one_lnat_def)

lemma sbe_obtain: assumes "ubLen ub = 1" and "ubMaxLen 1 ub"
  obtains sbe where "sbe2SB sbe = ub" and "sbeDom sbe = ubDom\<cdot>ub"
proof -
  have "ubDom\<cdot>ub \<noteq> {}"
    by (metis assms(1) notinfI3 one_lnat_def order_refl ubLen_def)
  have len: "\<And>c. c\<in>ubDom\<cdot>ub \<Longrightarrow> (# (ub. c)) = 1"
    by (metis assms(1) assms(2) ubmax_len_len usclLen_stream_def)
  have "\<And>s. #s = 1 \<Longrightarrow> \<exists>m. (\<up>m = s \<and> m\<in>sdom\<cdot>s)"
    using len_one_stream one_lnat_def by fastforce
  hence f_exists: "\<And>c.  (c\<in>ubDom\<cdot>ub) \<Longrightarrow> \<exists>m. ( ub . c = \<up>m \<and> m \<in> ctype c)" 
      using len usclOkay_stream_def by (smt subsetCE ubdom_channel_usokay ubgetch_insert)
  let ?f = "\<lambda>c. (c\<in>ubDom\<cdot>ub) \<leadsto> SOME m. (ub . c = \<up>m \<and> m \<in> ctype c)"
  have "dom ?f = ubDom\<cdot>ub" by(simp add: domIff2)

  have f_well: "sbElemWell ?f"
    apply(auto simp add: sbElemWell_def)
    by (metis (mono_tags, lifting) f_exists someI_ex)
  have "sbe2SB (Abs_sbElem ?f) = ub"
    apply(rule ub_eq)
    apply (simp add: sbeDom_def Abs_sbElem_inverse f_well)
    apply (simp add: domIff2 sbeDom_def Abs_sbElem_inverse f_well)
    apply(simp add: ubGetCh_def sbe2SB.rep_eq domIff2 sbeDom_def Abs_sbElem_inverse f_well)
    by (metis (mono_tags, lifting) f_exists someI_ex ubgetch_insert)
  thus ?thesis
    by (metis (no_types, lifting) sbe2sb_dom that) 
qed

lemma sbe_eq_bundle: assumes "sbe2SB sbe1 = sbe2SB sbe2"
  shows "sbe1 = sbe2"
  apply(rule sbe_eq)
  apply (metis assms sbe2sb_dom)
  by (metis assms sbe2sb_hdelem2)

subsection \<open>sbeUnion\<close>

lemma sbeunion_dom [simp]: "sbeDom (sbe1 \<plusminus> sbe2) = sbeDom sbe1 \<union> sbeDom sbe2"
  unfolding sbeDom_def sbeUnion.rep_eq
  by (simp add: Un_commute)

lemma sbeunion_2sb: "sbe2SB (sbe1 \<plusminus> sbe2) = (ubUnion\<cdot>(sbe2SB sbe1)\<cdot>(sbe2SB sbe2))"
  apply(rule ub_eq)
  apply simp_all
  by (smt Un_iff domD map_add_dom_app_simps(3) map_add_find_right sbe2sb_dom sbe2sb_getch sbeDom_def sbeUnion.rep_eq sbeunion_dom ubunion_getchL ubunion_getchR)

lemma sbeunion_null[simp]: "(sbeNull cs1) \<plusminus> (sbeNull cs2) = sbeNull (cs1 \<union> cs2)"
  apply(rule sbe_eq)
   apply simp_all
  unfolding sbeUnion.rep_eq sbeNull.rep_eq
  apply auto
  by (simp add: map_add_def)

lemma sbeunion_second[simp]: "c\<in>sbeDom sbe2 \<Longrightarrow> (Rep_sbElem (sbe1 \<plusminus> sbe2) ) \<rightharpoonup> c = Rep_sbElem sbe2 \<rightharpoonup> c"
  by(simp add: sbeUnion.rep_eq sbeDom_def map_add_dom_app_simps)

lemma sbeunion_first[simp]: "c\<notin>sbeDom sbe2 \<Longrightarrow> (Rep_sbElem (sbe1 \<plusminus> sbe2) ) \<rightharpoonup> c = Rep_sbElem sbe1 \<rightharpoonup> c"  
  by(simp add: sbeUnion.rep_eq sbeDom_def map_add_dom_app_simps)


section \<open>SBElem Induction for SB\<close>


lemma finind_sbe:
  "\<lbrakk>ubLen x = Fin n; 
    \<And>ub. (ubDom\<cdot>ub = ubDom\<cdot>x \<and> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)) \<Longrightarrow> P ub;
    \<And>sbe ub. P ub \<Longrightarrow> sbeDom sbe = (ubDom\<cdot>x) \<Longrightarrow> ubDom\<cdot>ub = (ubDom\<cdot>x) \<Longrightarrow> P (ubConcEq (sbe2SB sbe)\<cdot>ub)\<rbrakk>
    \<Longrightarrow> P x"
  apply(subst ubtake_ind_alt2, auto)
  by (smt Fin_neq_inf One_nat_def conceq_conc_1 leI one_lnat_def order_refl sbe_obtain ubHdLen_one 
          ubLen_def ubclDom_ubundle_def ubconc_sbhdrt ubconc_ubleast ubhd_ubdom ublen_min_on_channel 
          ubmaxlen_least_only ubmaxlen_sbrt_sbhd ubrt_ubdom usclLen_zero)

lemma ind_sbe:
  assumes "adm P" 
  and     "ubDom\<cdot>x \<noteq> {}"
  and     "\<And>ub. (ubDom\<cdot>ub = ubDom\<cdot>x \<Longrightarrow> (\<exists>c\<in>ubDom\<cdot>x. ub . c = \<bottom>)) \<Longrightarrow> P ub"
  and     "\<And>sbe ub. P ub \<Longrightarrow> sbeDom sbe = ubDom\<cdot>x \<Longrightarrow> ubDom\<cdot>ub = ubDom\<cdot>x \<Longrightarrow> P (ubConcEq (sbe2SB sbe)\<cdot>ub)"
shows     "P x"
  apply(rule ind_ub_alt)
  apply (simp add: assms)
  apply (simp add: assms)
  apply (simp add: assms)
  by (metis (no_types, lifting) assms  ublen_not_0 usclLen_bottom one_lnat_def sbe_obtain ubLen_def 
      ublen_min_on_channel ubundle_ubgetch_uscllen_one)  

end