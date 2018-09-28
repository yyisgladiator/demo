theory SBElem

imports SB tsynBundle

begin
default_sort message


lemma sbelemwell_empty: "sbElemWell Map.empty"
  by(simp add: sbElemWell_def)

typedef 'm sbElem = "{x :: (channel\<rightharpoonup>'m::message) . sbElemWell x}"
  using sbelemwell_empty by blast

setup_lifting type_definition_sbElem



definition sbeDom :: "'a sbElem \<Rightarrow> channel set" where
"sbeDom sbe = dom (Rep_sbElem sbe)"

lift_definition sbeNull :: "channel set \<Rightarrow> 'a::message tsyn sbElem" is
"\<lambda>cs. (\<lambda>c. (c\<in>cs) \<leadsto> -)"
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
 

section \<open>Lemma\<close>

lemma sbe_eq: assumes "sbeDom sbe1 = sbeDom sbe2"
  and "\<And>c. c\<in>sbeDom sbe1 \<Longrightarrow> (Rep_sbElem sbe1)\<rightharpoonup>c =  (Rep_sbElem sbe2)\<rightharpoonup>c"
  shows "sbe1 = sbe2"
  by (metis Rep_sbElem_inject assms(1) assms(2) part_eq sbeDom_def)

subsection \<open>sbe2SB\<close>

lemma sbe2sb_dom [simp]: "ubDom\<cdot>(sbe2SB sbe) = sbeDom sbe"
  by(simp add: sbeDom_def ubdom_insert sbe2SB.rep_eq)

lemma sbe2sb_nbot: "\<And>c. c\<in>sbeDom sbe \<Longrightarrow> (sbe2SB sbe) . c \<noteq> \<epsilon>"
  by(simp add: ubgetch_insert sbe2SB.rep_eq sbeDom_def)

lemma sbe2sb_getch: "c\<in>sbeDom sbe \<Longrightarrow> ((sbe2SB sbe)  .  c) = \<up>((Rep_sbElem sbe) \<rightharpoonup> c)"
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

lemma sbe2sb_hdelem_conc: "ubDom\<cdot>sb = sbeDom sbe \<Longrightarrow> (sbHdElem\<cdot>(ubConcEq(sbe2SB sbe)\<cdot>sb)) = sbHdElem\<cdot>(sbe2SB sbe)"
  apply(simp add: sbhdelem_insert)
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
  by (simp add: usclConc_stream_def)


lemma sbedom_null[simp]: "sbeDom (sbeNull cs) = cs"
  by(simp add: sbeDom_def sbeNull.rep_eq)

lemma sbe_ch_len: "\<And>c. c\<in> ubDom\<cdot>(sbe2SB sbe) \<Longrightarrow> # ((sbe2SB sbe) . c) = 1"
  by (simp add: one_lnat_def sbe2SB.rep_eq ubgetch_insert)

lemma sbe2sb_len[simp]: "sbeDom sbe \<noteq> {} \<Longrightarrow> ubLen (sbe2SB sbe) = 1"
  apply(simp add: ubLen_def)
  apply(rule Least_equality)
  apply (metis all_not_in_conv sbe2sb_dom sbe_ch_len usclLen_stream_def)
  by (metis order_refl sbe2sb_dom sbe_ch_len usclLen_stream_def)

lemma sbe_obtain: assumes "ubLen ub = 1" and "ubMaxLen 1 ub" 
  obtains sbe where "sbe2SB sbe = ub" and "sbeDom sbe = ubDom\<cdot>ub"
proof -
  have "ubDom\<cdot>ub \<noteq> {}"
    by (metis assms(1) notinfI3 one_lnat_def order_refl ubLen_def)
  have "\<And>c. c\<in>ubDom\<cdot>ub \<Longrightarrow> (# (ub. c)) = 1" oops


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


end