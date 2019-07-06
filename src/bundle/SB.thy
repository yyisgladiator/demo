(*<*)
theory SB
  imports stream.Stream sbElem
begin
(*>*)

declare[[show_types]]
declare[[show_consts]]

text \<open>TODO: sDom  umbenenne zu sValues\<close>
definition sValues :: "M stream \<Rightarrow> M set" where "sValues = (Rep_cfun sdom)" (*collect*)

(* TODO: Sections richtig benennen 
  * English (duh)
  * So wie in einem Techreport. Nicht Name der Definition
*)


default_sort chan

section \<open>Type Definition \<close>

definition sb_well :: "('c::chan \<Rightarrow> M stream) \<Rightarrow> bool" where
"sb_well f \<equiv> \<forall>c. sValues (f c) \<subseteq> ctype (Rep c)"

lemma sbwellI:
  assumes"\<And>c. sdom\<cdot>(f c) \<subseteq> ctype (Rep c)"
  shows"sb_well f"
  by (simp add: assms sValues_def sb_well_def)

lemma sbwell_ex:"sb_well (\<lambda>c. \<epsilon>)"
  by(simp add: sb_well_def sValues_def)

lemma sbwell_adm: "adm sb_well"
  unfolding sb_well_def sValues_def
  apply(rule adm_all, rule admI)
  by (simp add: ch2ch_fun l44 lub_fun)

pcpodef 'c::chan sb("(_\<^sup>\<Omega>)" [1000] 999) = "{f :: ('c::chan \<Rightarrow> M stream). sb_well f}"
  by (auto simp add: sbwell_ex sbwell_adm lambda_strict[symmetric])

(* TODO: Remove Warning
  https://fa.isabelle.narkive.com/wKVBUrdK/isabelle-setup-lifting-no-relator-for-the-type-warning
  HOL/Library/Quotient_Set.thy 
  *)
setup_lifting type_definition_sb


subsection \<open> sb pcpo lemmata \<close>

lemma bot_sb:"\<bottom> = Abs_sb(\<lambda>c. \<epsilon>)"
  by (simp add: Abs_sb_strict lambda_strict)

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
  unfolding chIsEmpty_def cEmpty_def bot_sb
  apply(rule sb_rep_eqI)
  apply(subst Abs_sb_inverse)
  apply (simp add: sbwell_ex)
  by(metis (mono_tags) Rep_sb bot.extremum cEmpty_def f_inv_into_f image_subset_iff iso_tuple_UNIV_I 
      mem_Collect_eq rangeI range_eqI sValues_def sb_well_def strict_sdom_rev subset_antisym)

lemma sbwell2fwell[simp]:"Rep_sb sb = f \<Longrightarrow> sb_well (f)"
  using Rep_sb by auto

section \<open>Definitions \<close>

subsection \<open>Domain of the SB\<close>

definition sbDom :: "'c\<^sup>\<Omega> \<Rightarrow> channel set" where
"sbDom = (\<lambda> c. (range (Rep::'c \<Rightarrow> channel)) - cEmpty)"



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
"(\<lambda>c sb . if Rep c\<in>(range(Rep::'c\<Rightarrow>channel)) then  (Rep_sb sb) (Abs(Rep c)) else \<epsilon>)"
  apply(intro cont2cont)
  by(simp add: cont2cont_fun)

lemmas sbgetch_insert = sbGetCh.rep_eq

abbreviation sbgetch_magic_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'e \<Rightarrow> M stream" (infix " \<^enum>\<^sub>\<star> " 65) where 
"sb \<^enum>\<^sub>\<star> c \<equiv> sbGetCh c\<cdot>sb"

abbreviation sbgetch_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'c \<Rightarrow> M stream" (infix " \<^enum> " 65) where 
"sb \<^enum> c \<equiv> sbGetCh c\<cdot>sb"


lemma sbgetch_insert2:"sb \<^enum>\<^sub>\<star> c = (Rep_sb sb) c"
  by(simp add: sbgetch_insert)

lemma sbgetch_ctypewell[simp]:"sdom\<cdot>(sb \<^enum>\<^sub>\<star> c) \<subseteq> ctype (Rep c)"
  apply(simp add: sbgetch_insert)
proof
  assume a1:"Rep c \<in> range (Rep::'a \<Rightarrow> channel)"
  obtain f where f_def:"Rep_sb sb =f "
    by simp
  then have "sb_well f"
    using Rep_sb by auto
  have "Rep((Abs::channel \<Rightarrow> 'a) (Rep c)) \<in> range (Rep::'a \<Rightarrow> channel)"
    by simp
  then show "sdom\<cdot>(Rep_sb sb (Abs (Rep c))) \<subseteq> ctype (Rep c)"
    using \<open>sb_well (f::'a \<Rightarrow> M stream)\<close> a1 f_def sValues_def sb_well_def by fastforce
qed

lemma sbmap_well:assumes"\<And>s. sValues (f s) \<subseteq> sValues s" shows"sb_well (\<lambda>c. f (b \<^enum>\<^sub>\<star> c))"
  apply(rule sbwellI)
  using assms sValues_def sbgetch_ctypewell by fastforce

(* TODO: Move to stream *)
lemma sdom_notempty:"s\<noteq>\<epsilon> \<Longrightarrow> sdom\<cdot>s\<noteq>{}"
  using strict_sdom_rev by auto

lemma sbgetch_ctype_notempty:"sb  \<^enum>\<^sub>\<star>  c \<noteq> \<epsilon> \<Longrightarrow> ctype (Rep c) \<noteq> {}"
proof-
  assume a1: "sb  \<^enum>\<^sub>\<star>  c \<noteq> \<epsilon>"
  then have "\<exists>e. e\<in> sdom\<cdot>(sb  \<^enum>\<^sub>\<star>  c)"
    by (simp add: sdom_notempty strict_sdom_rev neq_emptyD)
  then show "ctype (Rep c) \<noteq> {}"
    using sbgetch_ctypewell by blast
qed

lemma sbgetch_below_slen[simp]:"sb1 \<sqsubseteq> sb2 \<Longrightarrow> #(sb1 \<^enum>\<^sub>\<star> c) \<le> #(sb2 \<^enum>\<^sub>\<star> c)"
  by (simp add: mono_slen monofun_cfun_arg)

lemma sbgetch_bot[simp]:"\<bottom> \<^enum>\<^sub>\<star> c = \<epsilon>"
  apply(simp add: sbGetCh.rep_eq bot_sb)
  by (metis Rep_sb_strict app_strict bot_sb)

lemma sb_eqI:
    assumes "\<And>c. sb1 \<^enum> c = sb2 \<^enum> c"
    shows "sb1 = sb2"
  using Rep_sb_inject by (metis assms ext sbgetch_insert2)



subsection \<open>Concatination\<close>

lemma sbconc_well[simp]:"sb_well (\<lambda>c. (sb1 \<^enum> c) \<bullet> (sb2 \<^enum> c))"
  apply(rule sbwellI)
  by (metis (no_types, hide_lams) Un_subset_iff dual_order.trans sbgetch_ctypewell sconc_sdom)

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
   apply (metis (no_types, hide_lams) Un_subset_iff dual_order.trans sbgetch_ctypewell sbgetch_insert2 sconc_sdom)
  ..

lemma sbconc_bot_r[simp]:"sb \<bullet>\<^sup>\<Omega> \<bottom> = sb"
  by(rule sb_eqI, simp)

lemma sbconc_bot_l[simp]:"\<bottom> \<bullet>\<^sup>\<Omega> sb = sb"
  by(rule sb_eqI, simp)

subsection \<open>sbLen\<close>

subsubsection \<open>sbLen definition \<close>

definition sbLen::"'c\<^sup>\<Omega> \<Rightarrow> lnat"where
"sbLen sb = (LEAST n . n\<in>(insert (\<infinity>) {#(sb \<^enum>\<^sub>\<star> (c::'c)) | c. ((Rep::'c \<Rightarrow> channel) c)\<notin>cEmpty}))"

lemma sblen_mono:"monofun sbLen"
  oops

subsubsection \<open> sbLen lemmas \<close>

lemma sblen_min_len [simp]: "\<not>chIsEmpty(TYPE('cs)) \<Longrightarrow>sbLen (sb::'cs\<^sup>\<Omega>) \<le> #(sb \<^enum> c)" (* TODO: vermutlich typ von "c" fixieren *)
  oops  (* Sonderfall: "cEmpty" *)

lemma sblen_sbeqI:"x \<sqsubseteq> y \<Longrightarrow> sbLen x = \<infinity> \<Longrightarrow> x = y"
  oops

subsection\<open>sbIsLeast Predicate\<close>
(* TODO: nach oben verschieben *)
definition sbIsLeast::"'cs\<^sup>\<Omega> \<Rightarrow> bool" where
"sbIsLeast sb \<equiv> sbLen sb=0  \<or>  chIsEmpty TYPE('cs)"

subsubsection \<open>sbIsLeast lemmas\<close>

lemma "sbIsLeast \<bottom>"
  apply(simp add: sbIsLeast_def sbLen_def chIsEmpty_def)
  apply(case_tac "(\<exists>c::'a. Rep c \<notin> cEmpty)",simp_all)
  apply (metis (mono_tags, lifting) Inf'_neq_0_rev LeastI_ex Least_le inf_less_eq)
  by (simp add: image_subset_iff) 

subsection\<open>sbECons\<close>
(* TODO: nach oben verschieben *)
definition sbECons::"'c\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>" where
"sbECons sbe = sbConc (sbe2sb sbe)"

abbreviation sbECons_abbr :: "'c\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega>" (infixr "\<bullet>\<^sup>\<surd>" 100) where
"sbe \<bullet>\<^sup>\<surd> sb \<equiv> sbECons sbe\<cdot>sb"

lemma sbecons_len:"sbLen (sbe \<bullet>\<^sup>\<surd> sb) = lnsuc\<cdot>(sbLen sb)"
  oops

lemma sbtypeempty_sbecons_bot[simp]:"chIsEmpty TYPE ('cs) \<Longrightarrow> (sbe::'cs\<^sup>\<surd>) \<bullet>\<^sup>\<surd> sb = \<bottom>"
  by simp

lemma [simp]:"chIsEmpty TYPE ('cs) \<Longrightarrow> P(sb) \<Longrightarrow> P( (sbe::'cs\<^sup>\<surd>) \<bullet>\<^sup>\<surd> sb)"
  by (metis (full_types) sbtypeepmpty_sbbot)

(* TODO: nach oben verschieben *)
lemma sb_cases [case_names least sbeCons, cases type: sb]:
  "(sbIsLeast (sb'::'cs\<^sup>\<Omega>) \<Longrightarrow> P)
  \<Longrightarrow> (\<And>sbe sb. sb' = sbECons sbe\<cdot>sb \<Longrightarrow> \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> P)
  \<Longrightarrow> P"
  oops
(* TODO: nach oben verschieben *)
lemma sb_finind:
    fixes x::"'cs\<^sup>\<Omega>"
  assumes "sbLen x < \<infinity>"
      and "\<And>sb. sbIsLeast sb \<Longrightarrow> P sb"
      and "\<And>sbe sb. P sb \<Longrightarrow> \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb)"
    shows "P x"
  oops
(* TODO: nach oben verschieben *)
lemma sb_ind[case_names adm least sbeCons, induct type: sb]:
    fixes x::"'cs\<^sup>\<Omega>"
  assumes "adm P"
      and "\<And>sb. sbIsLeast sb \<Longrightarrow> P sb"
      and "\<And>sbe sb. P sb  \<Longrightarrow> \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb)"
  shows  "P x"
  sorry

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

lemma sbhdelem_some:"((\<forall>c::'c. x \<^enum>\<^sub>\<star> c \<noteq> \<epsilon>) \<and> x\<noteq>\<bottom>) \<Longrightarrow> sbHdElem((x::('c)\<^sup>\<Omega>)) = Abs_sbElem(Some(\<lambda>c. shd((x) \<^enum>\<^sub>\<star> c)))"
  apply(simp add: sbHdElem_def sbHdElem_h_def,auto)
  using cEmpty_def sbgetch_ctype_notempty by fastforce

lemma sbhdelem_mono_empty[simp]:"((range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty)) \<Longrightarrow> (x::('c)\<^sup>\<Omega>) \<sqsubseteq> y \<Longrightarrow> sbHdElem x = sbHdElem y"
  by(simp)

lemma sbhdelem_mono_eq[simp]:"(\<And>c::'a. (x::'a\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c \<noteq> \<epsilon>) \<Longrightarrow>  x \<sqsubseteq> y \<Longrightarrow> sbHdElem x = sbHdElem y"
proof-
  assume a1:"(\<And>c::'a. x  \<^enum>\<^sub>\<star>  c \<noteq> \<epsilon>)"
  assume a2:"x \<sqsubseteq> y"
  then have "\<And>c::'a. ctype (Rep c) \<noteq> {}"
    using a1 sbgetch_ctype_notempty by auto
  then have not_none:"\<not>(range(Rep::'a\<Rightarrow> channel)\<subseteq>cEmpty)"
    by(simp add: cEmpty_def,auto)
  then have a3:"(\<And>c::'a. y  \<^enum>\<^sub>\<star>  c \<noteq> \<epsilon>)"
    by (metis a1 a2 below_bottom_iff monofun_cfun_arg)
  then have not_bot:"x\<noteq>\<bottom> \<and> y \<noteq> \<bottom>"
    using a1 sbgetch_bot by auto
  then have h1:"\<And>c::'a. shd (x  \<^enum>\<^sub>\<star>  c) = shd (y  \<^enum>\<^sub>\<star>  c)"
    by (simp add: a1 a2 below_shd monofun_cfun_arg)
  then show ?thesis
    apply(subst sbhdelem_some)
    using not_bot a1  not_none apply auto[1]
    apply(subst sbhdelem_some)
    using not_bot a3 not_none apply auto[1]
    by(simp add: h1)
qed

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

subsubsection\<open>sbUnion abbreviation\<close>

abbreviation sbUnion_magic_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega> \<Rightarrow> 'e\<^sup>\<Omega>" (infixr "\<uplus>\<^sub>\<star>" 100) where
"sb1 \<uplus>\<^sub>\<star> sb2 \<equiv> sbUnion\<cdot>sb1\<cdot>sb2"

(*
abbreviation sbUnion_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega> \<Rightarrow> ('c\<union>'d)\<^sup>\<Omega>" (infixr "\<uplus>" 100) where
" sb1 \<uplus> sb2 \<equiv> sb1 \<uplus>\<star> sb2"
*)

subsubsection \<open>sbUnion lemmas\<close>

lemma sbunion_getch[simp]:fixes c::"'a"
      assumes"Rep c \<in> range(Rep::'c \<Rightarrow> channel)"
      shows  "(sbUnion::'a\<^sup>\<Omega>\<rightarrow> 'b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>)\<cdot>cb\<cdot>db \<^enum>\<^sub>\<star> c = cb \<^enum>\<^sub>\<star> c"
  by(simp add: Abs_sb_inverse sbGetCh.rep_eq sbunion_insert assms)

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

lemma sbunion_sbconvert_eq[simp]:"cb \<uplus>\<^sub>\<star> cb = cb\<star>"    (* TODO: keine warning mehr *)
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

subsection \<open>sbDrop\<close>

subsubsection \<open>sbDrop definition\<close>

lemma sbdrop_well[simp]:"sb_well (\<lambda>c. sdrop n\<cdot>(b \<^enum>\<^sub>\<star> c))"
  apply(rule sbwellI)
  by (meson dual_order.trans sbgetch_ctypewell sdrop_sdom)

lift_definition sbDrop::"nat \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"is
"\<lambda> n sb. Abs_sb (\<lambda>c. sdrop n\<cdot>(sb \<^enum> c))"
  apply(intro cont2cont)
  by(simp add: sValues_def)

lemmas sbdrop_insert = sbDrop.rep_eq

subsubsection \<open>sbRt abbreviation\<close>

abbreviation sbRt :: "'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"  where 
"sbRt \<equiv> sbDrop 1"

subsubsection \<open>sbDrop lemmas\<close>

lemma sbecons_eq:assumes "sbLen sb \<noteq> 0" shows "(sbHdElem sb) \<bullet>\<^sup>\<surd> (sbRt\<cdot>sb) = sb"
  oops

subsection \<open>sbTake\<close>

subsubsection \<open>sbTake definition\<close>

lemma sbtake_well[simp]:"sb_well (\<lambda>c. stake n\<cdot>(sb  \<^enum>\<^sub>\<star>  c))"
  apply(rule sbmap_well)
  by(simp add: sValues_def)

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
  apply(subst Abs_sb_inverse)
  by(auto simp add: sbgetch_insert2[symmetric])

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
