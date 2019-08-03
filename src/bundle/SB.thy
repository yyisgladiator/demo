(*<*)
theory SB
  imports stream.Stream sbElem
begin
(*>*)

declare %invisible[[show_types]]
declare %invisible[[show_consts]]


(* TODO: Sections richtig benennen 
  * English (duh)
  * So wie in einem Techreport. Nicht Name der Definition
*)


default_sort chan

section \<open>Type Definition \<close>

definition sb_well :: "('c::chan \<Rightarrow> M stream) \<Rightarrow> bool" where
"sb_well f \<equiv> \<forall>c. sValues\<cdot> (f c) \<subseteq> ctype (Rep c)"

lemma sbwellI:
  assumes"\<And>c. sValues\<cdot>(f c) \<subseteq> ctype (Rep c)"
  shows"sb_well f"
  by (simp add: assms sb_well_def)

lemma sbwell_ex:"sb_well (\<lambda>c. \<epsilon>)"
  by(simp add: sb_well_def)

lemma sbwell_adm: "adm sb_well"
  unfolding sb_well_def
  apply(rule adm_all, rule admI)
  by (simp add: ch2ch_fun l44 lub_fun)

pcpodef 'c::chan sb("(_\<^sup>\<Omega>)" [1000] 999) = "{f :: ('c::chan \<Rightarrow> M stream). sb_well f}"
  by (auto simp add: sbwell_ex sbwell_adm lambda_strict[symmetric])

(* TODO: Remove Warning
  https://fa.isabelle.narkive.com/wKVBUrdK/isabelle-setup-lifting-no-relator-for-the-type-warning
  HOL/Library/Quotient_Set.thy 
  *)
setup_lifting %invisible type_definition_sb


subsection \<open> sb pcpo lemmata \<close>

lemma bot_sb:"\<bottom> = Abs_sb(\<lambda>c. \<epsilon>)"
  by (simp add: Abs_sb_strict lambda_strict)

lemma rep_sb_well[simp]:"sb_well(Rep_sb sb)"
  using Rep_sb by auto

lemma sbrep_cont[simp, cont2cont]: "cont Rep_sb"
  using cont_Rep_sb cont_id by blast

text\<open>This is a continuity property for SBs.\<close>
lemma sb_abs_cont2cont [cont2cont]: assumes "cont h" and "\<And>x. sb_well (h x)"
  shows "cont (\<lambda>x. Abs_sb (h x))"
  by (simp add: assms(1) assms(2) cont_Abs_sb)

lemma sb_rep_eqI:assumes"\<And>c. (Rep_sb sb1) c = (Rep_sb sb2) c"
  shows "sb1 = sb2"
  by(simp add: po_eq_conv below_sb_def fun_belowI assms)

lemma sbtypeepmpty_sbbot[simp]:"chIsEmpty TYPE ('cs::chan) \<Longrightarrow> (sb::'cs\<^sup>\<Omega>) = \<bottom>"
  unfolding chDom_def cEmpty_def bot_sb
  apply(rule sb_rep_eqI)
  apply(subst Abs_sb_inverse)
  apply (simp add: sbwell_ex,auto)
  apply(insert sb_well_def[of "Rep_sb sb"],auto)
  using strict_sValues_rev by fastforce

lemma sbwell2fwell[simp]:"Rep_sb sb = f \<Longrightarrow> sb_well (f)"
  using Rep_sb by auto

section \<open>Definitions \<close>

subsection \<open>Converter from sbElem to SB\<close>

lift_definition sbe2sb::" 'c\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<Omega>" is
"\<lambda> sbe. case (Rep_sbElem sbe) of Some f \<Rightarrow> (\<lambda>c. \<up>(f c))
                                | None  \<Rightarrow> \<bottom> "
  apply(rule sbwellI, auto)
  apply(case_tac "Rep_sbElem sbElem = None")
  apply auto
  apply(subgoal_tac "sbElem_well (Some y)",simp)
  by(simp only: sbelemwell2fwell)

subsection \<open>Extract a single stream\<close>

lift_definition sbGetCh :: "'e \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow> M stream" is
"(\<lambda>c sb . if Rep c\<in>(chDom TYPE('c)) then  (Rep_sb sb) (Abs(Rep c)) else \<epsilon>)"
  apply(intro cont2cont)
  by(simp add: cont2cont_fun)

lemmas sbgetch_insert = sbGetCh.rep_eq

abbreviation sbgetch_magic_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'e \<Rightarrow> M stream" (infix " \<^enum>\<^sub>\<star> " 65) where 
"sb \<^enum>\<^sub>\<star> c \<equiv> sbGetCh c\<cdot>sb"

abbreviation sbgetch_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'c \<Rightarrow> M stream" (infix " \<^enum> " 65) where 
"sb \<^enum> c \<equiv> sbGetCh c\<cdot>sb"

definition sbHdElemWell::"'c\<^sup>\<Omega>  \<Rightarrow> bool" where
"sbHdElemWell  \<equiv> \<lambda> sb. (\<forall>c. sb  \<^enum>  c \<noteq> \<epsilon>)"  

lemma sbgetch_insert2:"sb \<^enum> c = (Rep_sb sb) c"
  apply(simp add: sbgetch_insert)
  by (metis (full_types)Rep_sb_strict app_strict cnotempty_cdom sbtypeepmpty_sbbot)

lemma sbhdelemchain[simp]:"sbHdElemWell x \<Longrightarrow>  x \<sqsubseteq> y \<Longrightarrow> sbHdElemWell y"
  apply(simp add: sbHdElemWell_def sbgetch_insert2)
  by (metis below_antisym below_sb_def fun_belowD minimal)

lemma sbgetch_ctypewell[simp]:"sValues\<cdot>(sb \<^enum>\<^sub>\<star> c) \<subseteq> ctype (Rep c)"
  apply(simp add: sbgetch_insert chDom_def,auto)
  by (meson in_mono sb_well_def sbwell2fwell)

lemma sbmap_well:assumes"\<And>s. sValues\<cdot>(f s) \<subseteq> sValues\<cdot>s" shows"sb_well (\<lambda>c. f (b \<^enum>\<^sub>\<star> c))"
  apply(rule sbwellI)
  using assms sbgetch_ctypewell by fastforce

lemma sbgetch_ctype_notempty:"sb  \<^enum>  c \<noteq> \<epsilon> \<Longrightarrow> ctype (Rep c) \<noteq> {}"
proof-
  assume a1: "sb  \<^enum>\<^sub>\<star>  c \<noteq> \<epsilon>"
  then have "\<exists>e. e\<in> sValues\<cdot>(sb  \<^enum>\<^sub>\<star>  c)"
    by (simp add: sValues_notempty strict_sValues_rev neq_emptyD)
  then show "ctype (Rep c) \<noteq> {}"
    using sbgetch_ctypewell by blast
qed

lemma sbgetch_below_slen[simp]:"sb1 \<sqsubseteq> sb2 \<Longrightarrow> #(sb1 \<^enum>\<^sub>\<star> c) \<le> #(sb2 \<^enum>\<^sub>\<star> c)"
  by (simp add: mono_slen monofun_cfun_arg)

lemma sbgetch_bot[simp]:"\<bottom> \<^enum>\<^sub>\<star> c = \<epsilon>"
  apply(simp add: sbGetCh.rep_eq bot_sb)
  by (metis Rep_sb_strict app_strict bot_sb)

lemma sb_belowI:   fixes sb1 sb2::"'cs\<^sup>\<Omega>"
  assumes "\<And>c. Rep c\<in>chDom TYPE('cs) \<Longrightarrow>  sb1 \<^enum> c \<sqsubseteq> sb2 \<^enum> c"
  shows "sb1 \<sqsubseteq> sb2"
  apply(subst below_sb_def)
  apply(rule fun_belowI)
  by (metis (full_types) assms  po_eq_conv sbGetCh.rep_eq sbgetch_insert2)

lemma sb_eqI:
  fixes sb1 sb2::"'cs\<^sup>\<Omega>"
    assumes "\<And>c. Rep c\<in>chDom TYPE('cs) \<Longrightarrow> sb1 \<^enum> c = sb2 \<^enum> c"
    shows "sb1 = sb2"
  apply(cases "chDom TYPE('cs) \<noteq> {}")
  apply (metis Diff_eq_empty_iff Diff_triv assms chDom_def chan_botsingle rangeI sb_rep_eqI sbgetch_insert2)
  by (metis (full_types) sbtypeepmpty_sbbot)

lemma slen_empty_eq:  assumes"chIsEmpty(TYPE('c))"
  shows " #(sb \<^enum> (c::'c)) =0"
  using assms chDom_def cEmpty_def sbgetch_ctype_notempty by fastforce

lemma sbgetch_sbe2sb_nempty: assumes "\<not>chIsEmpty(TYPE('a))"
  shows "\<forall>c::'a. sbe2sb sbe  \<^enum>  c \<noteq> \<epsilon>"
  apply (simp add: sbe2sb_def)
  apply (simp split: option.split) 
  apply (rule conjI)
  apply (rule impI)
  using assms chDom_def sbElem_well.simps(1) sbelemwell2fwell apply blast
  apply (rule allI, rule impI, rule allI)
  by (metis (no_types) option.simps(5) sbe2sb.abs_eq sbe2sb.rep_eq sbgetch_insert2 sconc_snd_empty 
      srcdups_step srcdupsimposs strict_sdropwhile)


subsection \<open>Concatination\<close>

lemma sbconc_well[simp]:"sb_well (\<lambda>c. (sb1 \<^enum> c) \<bullet> (sb2 \<^enum> c))"
  apply(rule sbwellI)
  by (metis (no_types, hide_lams) Un_subset_iff dual_order.trans sbgetch_ctypewell sconc_sValues)

lift_definition sbConc:: "'c\<^sup>\<Omega>  \<Rightarrow>  'c\<^sup>\<Omega> \<rightarrow>  'c\<^sup>\<Omega>" is
"\<lambda> sb1 sb2. Abs_sb(\<lambda>c. (sb1 \<^enum> c )\<bullet>(sb2 \<^enum> c))"
  by(intro cont2cont, simp)

lemmas sbconc_insert = sbConc.rep_eq

abbreviation sbConc_abbr :: "'c\<^sup>\<Omega>  \<Rightarrow>  'c\<^sup>\<Omega> \<Rightarrow>  'c\<^sup>\<Omega>" (infixr "\<bullet>\<^sup>\<Omega>" 70) where
"sb1 \<bullet>\<^sup>\<Omega> sb2 \<equiv> sbConc sb1\<cdot>sb2"

lemma sbconc_getch [simp]: "sb1 \<bullet>\<^sup>\<Omega> sb2  \<^enum> c = (sb1 \<^enum> c) \<bullet> (sb2 \<^enum> c)"
  unfolding sbgetch_insert2 sbconc_insert
  apply(subst Abs_sb_inverse)
   apply simp
  apply(rule sbwellI)
   apply (metis (no_types, hide_lams) Un_subset_iff dual_order.trans sbgetch_ctypewell sbgetch_insert2 sconc_sValues)
  ..

lemma sbconc_bot_r[simp]:"sb \<bullet>\<^sup>\<Omega> \<bottom> = sb"
  by(rule sb_eqI, simp)

lemma sbconc_bot_l[simp]:"\<bottom> \<bullet>\<^sup>\<Omega> sb = sb"
  by(rule sb_eqI, simp)

subsection \<open>sbLen\<close>

subsubsection \<open>sbLen definition \<close>

definition sbLen::"'c\<^sup>\<Omega> \<Rightarrow> lnat"where
"sbLen sb = (if (chIsEmpty TYPE('c)) then \<infinity> else (LEAST n . n\<in>({#(sb \<^enum> c) | c. True})))"

subsubsection \<open> sbLen lemmas \<close>

lemma sblen_min_len_empty[simp]:
  assumes"chIsEmpty(TYPE('c))"
  shows " sbLen (sb::'c\<^sup>\<Omega>) = \<infinity>"
  by(simp add: sbLen_def assms slen_empty_eq)
lemma sblen_min_len [simp]:
  assumes"\<not>chIsEmpty(TYPE('c))"
  shows"sbLen (sb :: 'c\<^sup>\<Omega>) \<le> #(sb \<^enum> c)"
  apply(simp add: sbLen_def assms)
  by (metis (mono_tags, lifting) Least_le)


lemma sblenleq: assumes "\<not> chIsEmpty TYPE('a)" and
 "\<exists>c::'a. #(sb\<^enum>c) \<le> k"
  shows "sbLen sb \<le> k" 
  apply(simp add: sbLen_def assms)
  apply(subgoal_tac "\<And>c::'a. Rep c \<notin> cEmpty") 
  apply auto
  apply (metis (mono_tags, lifting) Least_le assms(2) dual_order.trans)
  using assms(1) by(simp add: chDom_def)

lemma sblengeq: assumes "\<And>c::'c. k\<le> #(sb\<^enum>c)"
  shows "k \<le> sbLen sb" 
  apply(cases  "chIsEmpty(TYPE('c))",simp add: assms)
  apply(simp add: sbLen_def)
  using LeastI2_wellorder_ex inf_ub insert_iff mem_Collect_eq sbLen_def assms by smt

lemma sblen_sbconc: "((sbLen sb1) + (sbLen sb2)) \<le> (sbLen (sb1 \<bullet>\<^sup>\<Omega> sb2))"
  apply(cases  "chIsEmpty(TYPE('a))",simp)
  apply(rule sblengeq)
  by (metis lessequal_addition sbconc_getch sblen_min_len sconc_slen2)

lemma sblen_mono:"monofun sbLen"
  apply(rule monofunI,simp)
  apply(cases "chIsEmpty TYPE('a)",simp)
  apply(rule sblengeq)
  apply(rule sblenleq)
  using sbgetch_below_slen by auto

lemma sblen_rule:assumes "\<not>chIsEmpty(TYPE('a))" and "\<And>c. k \<le> #(sb \<^enum> (c :: 'a ))" and "\<exists>c. #(sb \<^enum> (c :: 'a )) = k"
  shows" sbLen sb = k"
  by (metis assms(1) assms(2) assms(3) dual_order.antisym sblen_min_len sblengeq)
 
lemma sblen_sbeqI:"x \<sqsubseteq> y \<Longrightarrow> sbLen x = \<infinity> \<Longrightarrow> x = y"
  apply(cases "chIsEmpty TYPE('a)")
  apply (metis (full_types)sbtypeepmpty_sbbot)
proof(simp add: sbLen_def)
  assume a1: "x \<sqsubseteq> y"
  assume a2: "(LEAST n::lnat. \<exists>c::'a. n = #(x  \<^enum>  c)) = \<infinity>"
  assume a3: "chDom TYPE('a) \<noteq> {}"
  then have "\<And>c. #(x \<^enum> c) = \<infinity>"
    by (metis (mono_tags, lifting) Least_le a2 inf_less_eq)
  moreover have "\<And>c. #(y \<^enum> c) = \<infinity>"
    using a1 calculation cont_pref_eq1I mono_fst_infD by blast
  then show ?thesis 
    apply(subst sb_eqI[of x y],auto)
    by (simp add: a1 calculation cont_pref_eq1I eq_less_and_fst_inf)
qed

lemma sblen2slen:
  assumes"\<not>chIsEmpty(TYPE('c))"
  shows"\<exists>c. sbLen (sb :: 'c\<^sup>\<Omega>) = #(sb \<^enum> c)"
  sorry

lemma sbconc_chan_len:"#(sb1 \<bullet>\<^sup>\<Omega> sb2  \<^enum>  c) = #(sb1 \<^enum> c)+ #(sb2  \<^enum>  c)"
  by (simp add: sconc_slen2)

lemma sblen_sbconc_eq: assumes "\<And>c.#(sb1 \<^enum> c) = k" shows "(sbLen (sb1 \<bullet>\<^sup>\<Omega> sb2)) = (sbLen sb2) + k"
  apply(cases  "chIsEmpty(TYPE('a))",simp)
  apply (simp add: plus_lnatInf_r)
  apply(subgoal_tac "sbLen sb1 = k")
  apply(rule sblen_rule,simp)
  apply (metis add.commute dual_order.trans sblen_min_len sblen_sbconc)
  apply (metis assms lnat_plus_commu sbconc_chan_len sblen2slen)  
  by(rule sblen_rule,simp_all add: assms)

lemma sbelen_one[simp]:
  assumes"\<not>chIsEmpty(TYPE('a))"
  shows " sbLen (sbe2sb (sbe::'a\<^sup>\<surd>)) = 1"
proof-
  have "\<And>c. #(sbe2sb (sbe::'a\<^sup>\<surd>) \<^enum> (c :: 'a )) = 1"
    apply(simp add: sbe2sb_def)
    apply(subgoal_tac "Rep_sbElem sbe \<noteq> None")
    apply auto
    apply(simp add: sbgetch_insert2)
    apply(subst Abs_sb_inverse,auto)
    apply (metis (full_types) option.simps(5) sbe2sb.rep_eq sbwell2fwell)
     apply (simp add: one_lnat_def)
    by(simp add: assms)
  then show ?thesis
    apply(subst sblen_rule)
    by(simp_all add: assms)
qed


lemma sbe2slen_1:  assumes"\<not>chIsEmpty(TYPE('a))"
  shows  "\<And>c::'a. #(sbe2sb sbe  \<^enum>  c) = (1::lnat)"
    apply(simp add: sbe2sb_def)
    apply(subgoal_tac "Rep_sbElem sbe \<noteq> None")
    apply auto
    apply(simp add: sbgetch_insert2)
    apply(subst Abs_sb_inverse,auto)
    apply (metis (full_types) option.simps(5) sbe2sb.rep_eq sbwell2fwell)
   apply (simp add: one_lnat_def)
    by(simp add: assms)
 
subsection\<open>sbIsLeast Predicate\<close>
(* TODO: nach oben verschieben *)
definition sbIsLeast::"'cs\<^sup>\<Omega> \<Rightarrow> bool" where
"sbIsLeast sb \<equiv> sbLen sb=0  \<or>  chIsEmpty TYPE('cs)"

subsubsection \<open>sbIsLeast lemmas\<close>

lemma "sbIsLeast \<bottom>"
  apply(simp add: sbIsLeast_def sbLen_def chDom_def)
  apply(case_tac "(\<exists>c::'a. Rep c \<notin> cEmpty)",simp_all)
  apply (metis (mono_tags, lifting) LeastI_ex)
  by (simp add: image_subset_iff) 

subsection \<open>sbDrop\<close>

subsubsection \<open>sbDrop definition\<close>

lemma sbdrop_well[simp]:"sb_well (\<lambda>c. sdrop n\<cdot>(b \<^enum>\<^sub>\<star> c))"
  apply(rule sbwellI)
  by (meson dual_order.trans sbgetch_ctypewell sdrop_sValues)

lift_definition sbDrop::"nat \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"is
"\<lambda> n sb. Abs_sb (\<lambda>c. sdrop n\<cdot>(sb \<^enum> c))"
  apply(intro cont2cont)
  by(simp add: sValues_def)

lemmas sbdrop_insert = sbDrop.rep_eq

subsubsection \<open>sbRt abbreviation\<close>

abbreviation sbRt :: "'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"  where 
"sbRt \<equiv> sbDrop 1"

subsubsection \<open>sbDrop lemmas\<close>


lemma sbdrop_bot[simp]:"sbDrop n\<cdot>\<bottom> = \<bottom>"
  apply(simp add: sbdrop_insert)
  by (simp add: bot_sb)

subsection \<open>sbTake\<close>

subsubsection \<open>sbTake definition\<close>

lemma sbtake_well[simp]:"sb_well (\<lambda>c. stake n\<cdot>(sb  \<^enum>\<^sub>\<star>  c))"
  by(simp add: sbmap_well)

lift_definition sbTake::"nat \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow>  'c\<^sup>\<Omega>"is
"\<lambda> n sb. Abs_sb (\<lambda>c. stake n\<cdot>(sb \<^enum> c))"
  by(intro cont2cont, simp)

lemmas sbtake_insert = sbTake.rep_eq

subsubsection \<open>sbHd abbreviation\<close>

abbreviation sbHd :: "'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"  where 
"sbHd \<equiv> sbTake 1"

subsubsection \<open>sbTake lemmas\<close>


lemma sbtake_getch[simp]:"sbTake n\<cdot>sb \<^enum> c = stake n\<cdot>(sb \<^enum> c)"
  apply(simp add: sbgetch_insert sbTake.rep_eq)
  apply(subst Abs_sb_inverse,auto simp add: sb_well_def)
  by (metis sValues_sconc sbgetch_ctypewell sbgetch_insert2 split_streaml1 subsetD)

lemma sbmap_stake_eq:"(Abs_sb (\<lambda>c::'a. stake n\<cdot>((sb::'a\<^sup>\<Omega>)  \<^enum>  c))  \<^enum>  (c::'a)) = stake n\<cdot>(sb  \<^enum>  c)"
  apply(simp add: sbgetch_insert2)
  apply(subst Abs_sb_inverse)
  apply simp
  apply(rule sbwellI)
  apply (metis sbgetch_insert2 sbgetch_ctypewell dual_order.trans sValues_sconc split_streaml1)
  by simp

lemma sbtake_max_len [simp]: "#(sbTake n\<cdot>(sb::'a\<^sup>\<Omega>) \<^enum> (c::'a)) \<le> Fin n"
  apply(simp add: sbTake.rep_eq)
  by(simp add: sbmap_stake_eq)


subsection\<open>sbHdElem\<close>

subsubsection \<open>sbHdElem definition\<close>

lemma sbhdelem_mono:"monofun
     (\<lambda>sb::'c\<^sup>\<Omega>.
         if range (Rep::'c \<Rightarrow> channel) \<subseteq> cEmpty then Iup (Abs_sbElem None)
         else if \<exists>c::'c. sb  \<^enum>\<^sub>\<star>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (sb  \<^enum>\<^sub>\<star>  c)))))"
  apply(rule monofunI)
  apply(cases "range (Rep::'c \<Rightarrow> channel) \<subseteq> cEmpty")
  apply simp
  apply auto
  apply (metis below_bottom_iff monofun_cfun_arg)
  by (meson below_shd monofun_cfun_arg)

definition sbHdElem_h::"'c\<^sup>\<Omega> \<Rightarrow> ('c\<^sup>\<surd>) u"where
"sbHdElem_h = (\<lambda> sb. if (range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty) then Iup(Abs_sbElem None) else
        if (\<exists>c. sb \<^enum> c = \<epsilon>) then \<bottom> else Iup(Abs_sbElem (Some (\<lambda>c. shd((sb) \<^enum> c)))))"

definition sbHdElem::"'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<surd>"where
"sbHdElem = (\<lambda> sb. case (sbHdElem_h sb) of Iup sbElem \<Rightarrow> sbElem | _ \<Rightarrow> undefined)"

subsubsection \<open>sbHdElem abbreviation \<close> (*TODO: better abbreviation lfloor*)

abbreviation sbHdElem_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<surd>" ( "\<lfloor>_" 70) where
"\<lfloor>sb \<equiv> sbHdElem sb"

subsubsection \<open>sbHdElem lemmas\<close>

lemma sbhdelem_none[simp]:"(range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty) \<Longrightarrow> sbHdElem((x::('c)\<^sup>\<Omega>)) = Abs_sbElem(None)"
  by(simp add: sbHdElem_def sbHdElem_h_def)

lemma sbhdelem_some:"sbHdElemWell x \<Longrightarrow> sbHdElem((x::('c)\<^sup>\<Omega>)) = Abs_sbElem(Some(\<lambda>c. shd((x) \<^enum>\<^sub>\<star> c)))"
  apply(simp add: sbHdElem_def sbHdElem_h_def sbHdElemWell_def,auto)
  using cEmpty_def sbgetch_ctype_notempty by fastforce

lemma sbhdelem_mono_empty[simp]:"((range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty)) \<Longrightarrow> (x::('c)\<^sup>\<Omega>) \<sqsubseteq> y \<Longrightarrow> sbHdElem x = sbHdElem y"
  by(simp)

lemma sbhdelem_mono_eq[simp]:"sbHdElemWell x \<Longrightarrow>  x \<sqsubseteq> y \<Longrightarrow> sbHdElem x = sbHdElem y"
  apply(cases "chIsEmpty(TYPE('a))")
  apply(simp add: sbHdElemWell_def chDom_def)
  apply(subgoal_tac "\<And>c::'a. shd (x  \<^enum>  c) = shd (y  \<^enum>  c)")
  apply(simp_all add: sbhdelem_some)
  apply(rule below_shd)
  by(simp add: sbgetch_insert2 below_sb_def sbHdElemWell_def below_fun_def)

subsection\<open>sbECons\<close>
(* TODO: nach oben verschieben *)
definition sbECons::"'c\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>" where
"sbECons sbe = sbConc (sbe2sb sbe)"

abbreviation sbECons_abbr :: "'c\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega>" (infixr "\<bullet>\<^sup>\<surd>" 100) where
"sbe \<bullet>\<^sup>\<surd> sb \<equiv> sbECons sbe\<cdot>sb"


lemma sbtypeempty_sbecons_bot[simp]:"chIsEmpty TYPE ('cs) \<Longrightarrow> (sbe::'cs\<^sup>\<surd>) \<bullet>\<^sup>\<surd> sb = \<bottom>"
  by simp

lemma [simp]:"chIsEmpty TYPE ('cs) \<Longrightarrow> P(sb) \<Longrightarrow> P( (sbe::'cs\<^sup>\<surd>) \<bullet>\<^sup>\<surd> sb)"
  by (metis (full_types) sbtypeepmpty_sbbot)

lemma sbrt_sbecons: "sbRt\<cdot>(sbe \<bullet>\<^sup>\<surd> sb) = sb"
  apply (cases "chIsEmpty(TYPE('a))", simp)
  apply (simp add: sbDrop.rep_eq)
  apply (simp add: sbECons_def)
  apply (subst sdropl6)
  apply (subgoal_tac "\<And>c. \<exists>m. sbe2sb sbe  \<^enum>  c = \<up>m")
  apply (metis Fin_0 Fin_Suc lnzero_def lscons_conv slen_scons strict_slen sup'_def)
  apply (simp add: sbgetch_insert2 sbe2sb.rep_eq chDom_def)
  apply (metis Diff_eq_empty_iff chDom_def option.simps(5) sbtypenotempty_fex)
  by (simp add: sb_rep_eqI sbgetch_insert2 Rep_sb_inverse)

lemma sbhdelem_h_sbe:" sbHdElem_h (sbe \<bullet>\<^sup>\<surd> sb) = up\<cdot>sbe"
  apply (cases "chIsEmpty(TYPE('a))",simp)
  apply (simp_all add: sbHdElem_def sbHdElem_h_def)+
  apply (rule conjI, rule impI)+
  apply (simp_all add: chDom_def up_def)
  apply (metis Diff_eq_empty_iff chDom_def sbtypeepmpty_sbenone)
  apply (subgoal_tac "\<forall>c::'a. sbe2sb sbe  \<^enum>  c \<noteq> \<epsilon>")
  apply (simp add: sbgetch_sbe2sb_nempty chDom_def)+
  apply (simp add: sbECons_def)
  apply (simp add: sbe2sb_def)
  apply (simp split: option.split)
  apply (rule conjI)
  apply (rule impI)+
  using sbElem_well.simps(1) sbelemwell2fwell chDom_def apply blast
  apply (rule allI)
  apply (rule impI)+
  apply (subgoal_tac "\<forall>c::'a. Abs_sb (\<lambda>c::'a. \<up>(x2 c))  \<^enum>  c = \<up>(x2 c)")
  apply (simp add: Abs_sbElem_inverse)
  apply (metis Rep_sbElem_inverse)
  apply (metis option.simps(5) sbe2sb.abs_eq sbe2sb.rep_eq sbgetch_insert2)
  by (simp add: chDom_def sbgetch_sbe2sb_nempty)

lemma sbhdelem_sbecons: "sbHdElem (sbe  \<bullet>\<^sup>\<surd> sb) = sbe"
  by(simp add: sbHdElem_def sbhdelem_h_sbe up_def)

lemma sbecons_len:
  shows "sbLen (sbe \<bullet>\<^sup>\<surd> sb) = lnsuc\<cdot>(sbLen sb)"
  apply(cases "chIsEmpty(TYPE('a))")
  apply(simp)
  apply(rule sblen_rule,simp)
  apply(simp add: sbECons_def sbgetch_insert2 sbconc_insert)
  apply(subst Abs_sb_inverse)
  apply simp
  apply(insert sbconc_well[of "sbe2sb sbe" sb],simp add: sbgetch_insert2)
   apply(subst sconc_slen2)
  apply(subgoal_tac "#(Rep_sb (sbe2sb sbe) c) = 1",auto)
  apply (metis equals0D lessequal_addition lnat_plus_commu lnat_plus_suc sbelen_one sbgetch_insert2 sblen_min_len)
  apply (metis emptyE sbe2slen_1 sbgetch_insert2) 
  apply(simp add: chDom_def)
  by (metis (no_types, hide_lams) add.left_neutral cempty_rule f_inv_into_f lnat_plus_commu one_def 
  only_empty_has_length_0 sbECons_def sbconc_chan_len sbe2slen_1 sblen2slen sconc_slen2 slen_scons)


(*sb_case*)

lemma sbcons:"sbLen (sb::'cs\<^sup>\<Omega>) \<noteq> (0::lnat) \<Longrightarrow>sbConc (sbHd\<cdot>sb)\<cdot>(sbRt\<cdot>sb) = sb"
  sorry

lemma sbHdElem:"sbLen (sb::'cs\<^sup>\<Omega>) \<noteq> (0::lnat) \<Longrightarrow>sbe2sb (sbHdElem sb) = sbHd\<cdot>sb"
  sorry

(*sb_ind*)

lemma sbtake_chain:"chain (\<lambda>i::nat. sbTake i\<cdot>x)"
  apply (rule chainI)
  apply(simp add: below_sb_def)
  apply(rule fun_belowI)
  apply(simp add: sbtake_insert)
  by (metis (no_types) Suc_leD le_refl sbgetch_insert2 sbmap_stake_eq stake_mono)

lemma sblen_sbtake:" \<not>chIsEmpty TYPE ('c) \<Longrightarrow> sbLen (sbTake n\<cdot>(x :: 'c\<^sup>\<Omega>)) \<le> Fin (n)"
proof- 
assume a0:"\<not>chIsEmpty TYPE ('c)"
  have h0:"\<And>c. sbLen (sbTake n\<cdot>x) \<le> #((sbTake n\<cdot>x) \<^enum> (c::'c))"
    by(rule sblen_min_len, simp add: a0)
  have h1:"\<And>c. #((sbTake n\<cdot>x) \<^enum> (c::'c)) \<le> Fin (n)"
   by simp 
  then show ?thesis
    using dual_order.trans h0 by blast
qed

lemma sbtake_lub:"(\<Squnion>i::nat. sbTake i\<cdot>x) = x"
  apply(rule sb_eqI)
  apply(subst contlub_cfun_arg)
  apply(simp add: sbtake_chain)
  by(simp add: sbtake_insert sbmap_stake_eq reach_stream)

lemma sbECons_sbLen:"sbLen (sb::'cs\<^sup>\<Omega>) \<noteq> (0::lnat) \<Longrightarrow> \<not> chIsEmpty TYPE('cs) \<Longrightarrow> \<exists> sbe sb'. sb = sbe \<bullet>\<^sup>\<surd> sb'"
  by (metis sbECons_def sbHdElem sbcons)

lemma sb_cases [case_names least sbeCons, cases type: sb]: 
  "(sbIsLeast (sb'::'cs\<^sup>\<Omega>) \<Longrightarrow> P) 
  \<Longrightarrow> (\<And>sbe sb. sb' = sbECons sbe\<cdot>sb \<Longrightarrow> \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> P) 
  \<Longrightarrow> P"
  by (meson sbECons_sbLen sbIsLeast_def)

lemma sb_finind1:
    fixes x::"'cs\<^sup>\<Omega>"
    shows "sbLen x = Fin k\<Longrightarrow> (\<And>sb. sbIsLeast sb \<Longrightarrow> P sb) \<Longrightarrow> (\<And>sbe sb. P sb 
          \<Longrightarrow> \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb))
    \<Longrightarrow>P x"
  apply(induction k  arbitrary:x)
  apply (simp add: sbIsLeast_def)
  by (metis Fin_Suc inject_lnsuc sb_cases sbecons_len)

lemma sb_finind:
    fixes x::"'cs\<^sup>\<Omega>"
  assumes "sbLen x < \<infinity>"
      and "\<And>sb. sbIsLeast sb \<Longrightarrow> P sb"
      and "\<And>sbe sb. P sb \<Longrightarrow> \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb)"
    shows "P x"
  by (metis assms(1) assms(2) assms(3) lnat_well_h2 sb_finind1)

lemma sbtakeind1: 
  fixes x::"'cs\<^sup>\<Omega>"
  shows "\<forall>x. (( \<forall>(sb::'cs\<^sup>\<Omega>) . sbIsLeast sb \<longrightarrow> P sb) \<and> 
        (\<forall> (sbe::'cs\<^sup>\<surd>) sb::'cs\<^sup>\<Omega>. P sb  \<longrightarrow> \<not>chIsEmpty TYPE ('cs) \<longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb))) \<and> 
        ( \<not>chIsEmpty TYPE ('cs) \<longrightarrow> sbLen x \<le> Fin n) \<longrightarrow> P (x)"
  by (metis (no_types, lifting) inf_ub less2eq order.not_eq_order_implies_strict sb_cases sb_finind sb_finind1)

lemma sbtakeind: 
  fixes x::"'cs\<^sup>\<Omega>"
  shows "\<forall>x. (( \<forall>(sb::'cs\<^sup>\<Omega>) . sbIsLeast sb \<longrightarrow> P sb) \<and> 
         (\<forall> (sbe::'cs\<^sup>\<surd>) sb::'cs\<^sup>\<Omega>. P sb  \<longrightarrow> \<not>chIsEmpty TYPE ('cs) \<longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb))) 
          \<longrightarrow> P (sbTake  n\<cdot>x)"
  apply rule+
  apply(subst sbtakeind1, simp_all) 
  using sblen_sbtake sbtakeind1 by auto

lemma sb_ind[case_names adm least sbeCons, induct type: sb]:
    fixes x::"'cs\<^sup>\<Omega>"
  assumes "adm P" 
      and "\<And>sb. sbIsLeast sb \<Longrightarrow> P sb"
      and "\<And>sbe sb. P sb  \<Longrightarrow> \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb)"   
    shows  "P x"
  using assms(1) assms(2) assms(3) 
  apply(unfold adm_def)
  apply(erule_tac x="\<lambda>i. sbTake i\<cdot>x" in allE,auto)
  apply(simp add: sbtake_chain)
  apply(simp add: sbtakeind)
  by(simp add: sbtake_lub)

lemma sbecons_eq:assumes "sbLen sb \<noteq> 0" shows "(sbHdElem sb) \<bullet>\<^sup>\<surd> (sbRt\<cdot>sb) = sb"
  apply(cases sb,simp_all add: sbIsLeast_def assms)
  by (metis One_nat_def sbhdelem_sbecons sbrt_sbecons)
  
subsection \<open>sbUnion\<close>

subsubsection\<open>sbUnion definition\<close>

definition sbUnion::"'c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega> \<rightarrow> 'e\<^sup>\<Omega>" where
"sbUnion = (\<Lambda> sb1 sb2. Abs_sb (\<lambda> c. if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) then 
                  sb1 \<^enum>\<^sub>\<star> c else  sb2\<^enum>\<^sub>\<star> c))"

lemma sbunion_sbwell[simp]: "sb_well ((\<lambda> (c::'e). if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) then 
                  (sb1::'c\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c else  (sb2::'d\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c))"
  apply(rule sbwellI)
  by simp

lemma sbunion_insert:"sbUnion\<cdot>(sb1::'c\<^sup>\<Omega>)\<cdot>sb2 = Abs_sb (\<lambda> c. if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) then 
                  sb1 \<^enum>\<^sub>\<star> c else  sb2 \<^enum>\<^sub>\<star> c)"
  unfolding sbUnion_def
  apply(subst beta_cfun, intro cont2cont, simp)+
  ..
(* TODO: sbunion_rep_eq 
  Namin_convention: "insert" = Abs_cfun weg
                      rep_eq = Abs_XXX weg *)

lemma sbunion_rep_eq:"Rep_sb (sbUnion\<cdot>(sb1::'c\<^sup>\<Omega>)\<cdot>sb2) = (\<lambda> c. if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) then 
                  sb1 \<^enum>\<^sub>\<star> c else  sb2 \<^enum>\<^sub>\<star> c)"
  apply(subst sbunion_insert)
  apply(subst Abs_sb_inverse)
  by auto

subsubsection\<open>sbUnion abbreviation\<close>

abbreviation sbUnion_magic_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega> \<Rightarrow> 'e\<^sup>\<Omega>" (infixr "\<uplus>\<^sub>\<star>" 100) where
"sb1 \<uplus>\<^sub>\<star> sb2 \<equiv> sbUnion\<cdot>sb1\<cdot>sb2"

abbreviation sbUnion_minus_abbr :: "('c - ('d))\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega>" (infixr "\<uplus>\<^sub>-" 100) where
"sb1 \<uplus>\<^sub>- sb2 \<equiv> sbUnion\<cdot>sb1\<cdot>sb2"

abbreviation sbUnion_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega> \<Rightarrow> ('c\<union>'d)\<^sup>\<Omega>" (infixr "\<uplus>" 100) where
" sb1 \<uplus> sb2 \<equiv> sb1 \<uplus>\<^sub>\<star> sb2"


subsubsection \<open>sbUnion lemmas\<close>

lemma sbunion_getch[simp]:fixes c::"'a"
      assumes"Rep c \<in> range(Rep::'c \<Rightarrow> channel)"
      shows  "(sbUnion::'a\<^sup>\<Omega>\<rightarrow> 'b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>)\<cdot>cb\<cdot>db \<^enum>\<^sub>\<star> c = cb \<^enum> c"
  by(simp add: Abs_sb_inverse sbGetCh.rep_eq sbunion_insert assms chDom_def)

lemma sbunion_eq [simp]: "sb1 \<uplus>\<^sub>\<star> sb2 = sb1"
  apply(rule sb_eqI)
  by simp


subsection \<open>sbConvert\<close>

subsubsection \<open>sbConvert definition\<close>

lemma sbconvert_well[simp]:"sb_well (\<lambda>c. sb \<^enum>\<^sub>\<star> c)"
  by(rule sbwellI, simp)

lift_definition sbConvert::"'c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>"is
"(\<lambda> sb. Abs_sb (\<lambda>c.  sb \<^enum>\<^sub>\<star> c ))"
  by(intro cont2cont, simp)
  
lemmas sbconvert_insert = sbConvert.rep_eq

subsubsection \<open>sbConvert abbreviation\<close>

abbreviation sbConvert_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega>" ( "_\<star>" 200) where 
"sb\<star> \<equiv> sbConvert\<cdot>sb"

abbreviation sbConvert_abbr_fst :: "('c \<union> 'd)\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega>" ( "_\<star>\<^sub>1" 200) where 
"sb\<star>\<^sub>1 \<equiv> sbConvert\<cdot>sb"

abbreviation sbConvert_abbr_snd :: "('c\<union>'d)\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega>" ( "_\<star>\<^sub>2" 200) where 
"sb\<star>\<^sub>2 \<equiv> sbConvert\<cdot>sb"

subsubsection \<open>sbConvert lemmas\<close>

lemma sbconvert_rep[simp]: "Rep_sb(sb\<star>) = (\<lambda>c. sb \<^enum>\<^sub>\<star> c)"
  by (simp add: Abs_sb_inverse sbconvert_insert)

lemma fixes sb ::"'a\<^sup>\<Omega>"
  shows "sb\<star> \<^enum>\<^sub>\<star> c = sb \<^enum>\<^sub>\<star> c"
  apply(cases "Rep c\<in>(range(Rep::'a\<Rightarrow>channel))")
   apply(auto simp add: sbgetch_insert)
  oops (* gilt nicht, wenn 'b kleiner ist als 'a *)

lemma sbconv_eq[simp]:"sbConvert\<cdot>sb = sb"
  apply(rule sb_eqI)
  by (metis (no_types) Abs_sb_inverse mem_Collect_eq sbconvert_insert sbconvert_well sbgetch_insert2)

lemma sbunion_sbconvert_eq[simp]:"cb \<uplus>\<^sub>\<star> cb = (cb\<star>)"
  by(simp add: sbunion_insert sbconvert_insert)

(*  Die Section ist so kurz, das verwirrt mehr als es hilft 
subsection\<open>sbMapStream\<close>

subsubsection \<open>sbMapStream definition\<close>

definition sbMapStream:: "(M stream \<Rightarrow> M stream) \<Rightarrow> 'c\<^sup>\<Omega> \<Rightarrow>  'c\<^sup>\<Omega>" where
"sbMapStream f b = Abs_sb (\<lambda>c. f (b \<^enum>\<^sub>\<star> c))"  (* Nicht unbedingt wellformed... also nicht verwenden *)

subsubsection \<open>sbMapStream lemmas\<close>

lemma sbmapstream_well:assumes"\<And>s. sValues (f s) \<subseteq> sValues s" shows"sb_well (\<lambda>c. f (b \<^enum>\<^sub>\<star> c))"
  apply(rule sbwellI)
  using assms sValues_def sbgetch_ctypewell by fastforce

lemma sbmapstream_cont[cont2cont]:
  assumes "\<And>s. sValues (f s) \<subseteq> sValues s" 
      and "cont f"
    shows "cont (sbMapStream f)"
  unfolding sbMapStream_def
  apply(intro cont2cont)
  by (simp_all add: assms cont_compose sbmapstream_well)
*)





(*
lemma sblen_mono[simp]:"monofun sbLen"
  apply(rule monofunI)
proof(simp add: sbLen_def)
  fix x::"'a\<^sup>\<Omega>" and y::"'a\<^sup>\<Omega>"
  assume a1:"x \<sqsubseteq> y"
  then have h1:"\<forall>c::'a . #(x  \<^enum>\<^sub>\<star>  c) \<sqsubseteq> #(y  \<^enum>\<^sub>\<star>  c)"
    by simp
  then have "\<exists>c::'a. #(x  \<^enum>\<^sub>\<star>  c) \<sqsubseteq> #(y  \<^enum>\<^sub>\<star>  c)"
    by simp
  then show "(LEAST n::lnat. n = \<infinity> \<or> (\<exists>c::'a. n = #(x  \<^enum>\<^sub>\<star>  c) \<and> Rep c \<notin> cEmpty)) \<le> (LEAST n::lnat. n = \<infinity> \<or> (\<exists>c::'a. n = #(y  \<^enum>\<^sub>\<star>  c) \<and> Rep c \<notin> cEmpty))"
  proof(cases "range(Rep::'a \<Rightarrow> channel)\<subseteq> cEmpty")
    case True
    then have "\<forall>c::'a. (Rep c)\<in>cEmpty"
      by auto
    then show ?thesis
      by auto
  next
    case False
    then have "\<forall>c::'a. (Rep c)\<notin>cEmpty"
      using chan_botsingle by blast
    have "\<exists>(c::'a).  \<forall>c2::'a.  #(x  \<^enum>\<^sub>\<star>  c) \<sqsubseteq> #((x \<^enum>\<^sub>\<star> c2))"(*? ? ?*)
    proof(cases "\<exists>(c::'a).  \<forall>c2::'a.  #(x  \<^enum>\<^sub>\<star>  c) \<sqsubseteq> #((x \<^enum>\<^sub>\<star> c2))" )
      case True
      then show ?thesis
         by simp
    next
      case False
      then have "\<forall>c2::'a. \<exists>c::'a. #(x  \<^enum>\<^sub>\<star>  c2) \<sqsubseteq> #(x  \<^enum>\<^sub>\<star>  c)"
        by auto
      then have "\<exists>(c::'a).  \<forall>c2::'a.  #(x  \<^enum>\<^sub>\<star>  c) \<sqsubseteq> #((x \<^enum>\<^sub>\<star> c2))"
        sorry
      then show ?thesis
        by auto
    qed
    then show ?thesis
      apply auto
      sorry
  qed

lemma sblen_notbot:"\<exists>c::'c. (Rep::'c\<Rightarrow> channel) c \<noteq> cbot \<Longrightarrow> sbLen (sb::'c\<^sup>\<Omega>) = (LEAST n. n\<in>{#(sb \<^enum>\<^sub>\<star> c) | c::'c. True})"
  apply(simp add: sbLen_def)
  apply(cases "\<exists>c::'c. #(sb  \<^enum>\<^sub>\<star>  c) = \<infinity>")
  sorry

lemma sblen_cont[simp]:"cont (sbLen::('c::{chan,finite}\<^sup>\<Omega> \<Rightarrow> lnat))"
  apply(rule Cont.contI2,simp_all)
  apply(cases "\<exists>c::'c. (Rep::'c\<Rightarrow>channel) c \<noteq> cbot")
  apply(subst sblen_notbot)
  apply simp
  apply(subst sblen_notbot)
  apply simp
  apply(simp_all add: sbLen_def)
proof-
  fix Y::"nat \<Rightarrow> 'c\<^sup>\<Omega>"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. LEAST n::lnat. n = \<infinity> \<or> (\<exists>c::'c. n = #(Y i  \<^enum>\<^sub>\<star>  c) \<and> Rep c \<noteq> cbot))"
  assume a3:"\<exists>c::'c. Rep c \<noteq> cbot"
  then show "(LEAST n::lnat. \<exists>c::'c. n = #(Lub Y  \<^enum>\<^sub>\<star>  c)) \<le> (\<Squnion>i::nat. LEAST n::lnat. \<exists>c::'c. n = #(Y i  \<^enum>\<^sub>\<star>  c))"
    apply(subst contlub_cfun_arg, simp add: a1)
    apply(subst contlub_cfun_arg)
    sorry
qed
*)

(*<*)
end
(*>*)
