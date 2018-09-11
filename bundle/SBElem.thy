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



section \<open>Lemma\<close>

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


end