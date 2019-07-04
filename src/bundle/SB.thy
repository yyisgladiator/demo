theory SB

imports stream.Stream sbElem
begin
declare[[show_types]]
section\<open>ctype (generated)\<close>

text \<open>TODO: sDom umbenenne zu sValues\<close>
definition sValues :: "M stream \<Rightarrow> M set" where "sValues = (Rep_cfun sdom)" (*collect*)


section \<open>sb pcpo definition \<close>

definition sb_well :: "('c::chan \<Rightarrow> M stream) \<Rightarrow> bool" where
"sb_well f = (\<forall>c. sValues (f c) \<subseteq> ctype ((Rep::'c \<Rightarrow> channel) c))"

lemma sbwellI:
  assumes"\<And>(c::'c::chan). sdom\<cdot>(f c) \<subseteq> ctype ((Rep::'c\<Rightarrow> channel) c)"
  shows"sb_well f"
  by (simp add: assms sValues_def sb_well_def)

lemma sb_ex:"sb_well (\<lambda>c. \<epsilon>)"
  by(simp add: sb_well_def sValues_def)

pcpodef 'c::chan sb("(_\<^sup>\<Omega>)" [1000] 999) = "{f :: ('c::chan \<Rightarrow> M stream). sb_well f}"
  apply auto
  apply (metis lambda_strict sb_ex)
  apply (simp add: sb_well_def sValues_def)
  apply(rule adm_all)
  apply(rule admI)
  by (simp add: ch2ch_fun l44 lub_fun)

subsection \<open>sb Predicate definitions\<close>

definition spfIsStrict::"('c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>) \<Rightarrow> bool" where
"spfIsStrict f \<equiv> f\<cdot>\<bottom>=\<bottom>"

subsection \<open> sb pcpo lemmata \<close>
lemma bot_sb:"\<bottom> = Abs_sb(\<lambda>c. \<epsilon>)"
  by (simp add: Abs_sb_strict lambda_strict)

lemma [simp, cont2cont]:"cont Rep_sb"
  using cont_Rep_sb cont_id by blast

section \<open>sb functions \<close>
default_sort chan

subsection \<open>sbDom\<close>

subsubsection\<open>sbDom definition \<close>
definition sbDom :: "'c\<^sup>\<Omega>\<Rightarrow> channel set" where
"sbDom = (\<lambda> c. (range (Rep::'c \<Rightarrow> channel)) - cEmpty)"


subsection \<open>sbGetCh\<close>

subsubsection\<open>sbGetCh definition\<close>

lift_definition sbGetCh :: "'e \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow> M stream" is
"(\<lambda>c sb . if Rep c\<in>(range(Rep::'c\<Rightarrow>channel)) then  (Rep_sb sb) (Abs(Rep c)) else \<epsilon>)"
  apply(simp add: cfun_def)
  apply(rule Cont.contI2)
  apply(rule monofunI)
  apply (simp add: below_sb_def fun_belowD)
  apply(subst cont2contlubE[of Rep_sb],simp,simp)
  apply auto
  by (simp add: below_sb_def lub_fun po_class.chain_def)

lemmas sbgetch_insert = sbGetCh.rep_eq

subsubsection \<open>sbGetCh abbreviation\<close>

abbreviation sbgetch_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'e \<Rightarrow> M stream" (infix " \<^enum> " 65) where 
"sb \<^enum> c \<equiv> sbGetCh c\<cdot>sb"

subsubsection \<open>sbGetCh Lemmata\<close>

lemma sbgetch_insert2:"(sb::'c\<^sup>\<Omega>) \<^enum> (c::'c) = (Rep_sb sb) c"
  apply(simp add: sbgetch_insert)
  by (simp add: chan_inj)

lemma sbgetch_ctypewell[simp]:"sdom\<cdot>(sb \<^enum> c) \<subseteq> ctype (Rep c)"
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

lemma sdom_notempty:"s\<noteq>\<epsilon> \<Longrightarrow> sdom\<cdot>s\<noteq>{}"
  using strict_sdom_rev by auto

lemma sbgetch_ctype_notempty:"sb  \<^enum>  c \<noteq> \<epsilon> \<Longrightarrow> ctype (Rep c) \<noteq> {}"
proof-
  assume a1: "sb  \<^enum>  c \<noteq> \<epsilon>"
  then have "\<exists>e. e\<in> sdom\<cdot>(sb  \<^enum>  c)"
    by (simp add: sdom_notempty strict_sdom_rev neq_emptyD)
  then show "ctype (Rep c) \<noteq> {}"
    using sbgetch_ctypewell by blast
qed

lemma sbgetch_below_slen[simp]:"sb1 \<sqsubseteq> sb2 \<Longrightarrow> #(sb1 \<^enum> c) \<le> #(sb2 \<^enum> c)"
  by (simp add: mono_slen monofun_cfun_arg)

lemma sbgetch_bot:"\<bottom> \<^enum> c = \<epsilon>"
  apply(simp add: sbGetCh.rep_eq bot_sb)
  by (metis Rep_sb_strict app_strict bot_sb)

lemma sb_eqI:
  fixes sb1 sb2::"'a\<^sup>\<Omega>"
    assumes "\<And>c::'a. sb1 \<^enum> c = sb2 \<^enum> c"
    shows "sb1 = sb2"
  using Rep_sb_inject by (metis assms ext sbgetch_insert2)
  
subsection \<open>sbUnion\<close>

subsubsection\<open>sbUnion definition\<close>

definition sbUnion::"'c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega> \<rightarrow> 'e\<^sup>\<Omega>" where
"sbUnion = (\<Lambda> sb1 sb2. Abs_sb (\<lambda> c. if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) then 
                  sb1 \<^enum> c else  sb2\<^enum> c))"

lemma sbunion_sbwell[simp]: "sb_well ((\<lambda> (c::'e). if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) then 
                  (sb1::'c\<^sup>\<Omega>) \<^enum> c else  (sb2::'d\<^sup>\<Omega>) \<^enum> c))"
  apply(rule sbwellI)
  by simp

lemma sbunionlub_well[simp]:"chain Y \<Longrightarrow> sb_well(\<Squnion>i::nat. (\<lambda>c::'a. if Rep c \<in> range (Rep::'c \<Rightarrow> channel) then ((Y i)::'c\<^sup>\<Omega> )  \<^enum>  c else (x::'d\<^sup>\<Omega>)  \<^enum>  c))"
  apply(rule sbwellI)
  by (smt below_refl contlub_lambda l44 monofun_cfun_arg po_class.chain_def sbgetch_ctypewell)

lemma sbunion_cont_h[simp]:"cont(\<lambda>sb2::'d\<^sup>\<Omega>. Abs_sb (\<lambda> c. if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) then 
                  (sb1::'c\<^sup>\<Omega>) \<^enum> c else  sb2 \<^enum> c))"
  apply(rule Cont.contI2)
  apply(rule monofunI)
  apply (simp add: Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI)
  apply(simp add: Abs_sb_inverse below_sb_def)
  apply(rule fun_belowI)
  apply(simp add: cont2contlubE)
  apply(simp add: Abs_sb_inverse below_sb_def)
  by (smt cont_pref_eq1I contlub_lambda is_ub_thelub lub_eq po_class.chain_def po_eq_conv)

lemma sbunion_cont[simp]:"cont(\<lambda>sb1::'c\<^sup>\<Omega> . \<Lambda> (sb2::'d\<^sup>\<Omega>). Abs_sb (\<lambda> c. if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) then
                  (sb1::'c\<^sup>\<Omega>) \<^enum> c else  sb2 \<^enum> c))"  (*verkürzen*)
  apply(rule Cont.contI2)
   apply(rule monofunI)
  apply(rule cfun_belowI)
   apply (simp add: Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI)
  apply(rule cfun_belowI)
  apply(simp add: Abs_sb_inverse below_sb_def)
  apply(rule fun_belowI)
proof(simp add: cont2contlubE,auto)
  fix Y::"nat \<Rightarrow> 'c\<^sup>\<Omega>" and x::"'d\<^sup>\<Omega>" and xa::'a and xb::'c
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. \<Lambda> (sb2::'d\<^sup>\<Omega>). Abs_sb (\<lambda>c::'a. if Rep c \<in> range Rep then Y i  \<^enum>  c else sb2  \<^enum>  c))"
  assume a3:"Rep xa = Rep xb"
  have c1:"chain (\<lambda>i sb2::'d\<^sup>\<Omega>. Abs_sb (\<lambda>c::'a. if Rep c \<in> range (Rep::'c\<Rightarrow> channel) then Y i  \<^enum>  c else sb2  \<^enum>  c))"
    apply(rule ch2ch_monofun)
    apply(rule monofunI)
    apply (simp add: Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI)
    by(simp add: a1)
  have c2:"chain (\<lambda>i::nat. Abs_sb (\<lambda>c::'a. if Rep c \<in> range (Rep::'c\<Rightarrow> channel) then Y i  \<^enum>  c else x  \<^enum>  c))"
    apply(rule chainI)
    apply (simp add: Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI)
    by (simp add: a1 cont_pref_eq1I fun_belowI po_class.chainE)
  show "(\<Squnion>i::nat. Y i  \<^enum>  xa) \<sqsubseteq> Rep_sb ((\<Squnion>i::nat. (\<lambda>sb2::'d\<^sup>\<Omega>. Abs_sb (\<lambda>c::'a. if Rep c \<in> range (Rep::'c \<Rightarrow> channel) then Y i  \<^enum>  c else sb2  \<^enum>  c))) x) xa"
    apply(subst lub_fun)
    apply(simp add: c1)
    apply(subst lub_sb)
    apply(simp add: c2)
    apply (simp add: Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI a1)
    by (smt a1 a3 contlub_lambda lub_mono monofun_cfun_arg po_class.chain_def po_eq_conv range_eqI)
next
  fix Y::"nat \<Rightarrow> 'c\<^sup>\<Omega>" and x::"'d\<^sup>\<Omega>" and xa::'a
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. \<Lambda> (sb2::'d\<^sup>\<Omega>). Abs_sb (\<lambda>c::'a. if Rep c \<in> range Rep then Y i  \<^enum>  c else sb2  \<^enum>  c))"
  assume a3:" Rep xa \<notin> range (Rep::'c\<Rightarrow> channel)"
  have c1:"chain (\<lambda>i sb2::'d\<^sup>\<Omega>. Abs_sb (\<lambda>c::'a. if Rep c \<in> range (Rep::'c\<Rightarrow> channel) then Y i  \<^enum>  c else sb2  \<^enum>  c))"
    apply(rule ch2ch_monofun)
    apply(rule monofunI)
    apply (simp add: Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI)
    by(simp add: a1)
  have c2:"chain (\<lambda>i::nat. Abs_sb (\<lambda>c::'a. if Rep c \<in> range (Rep::'c\<Rightarrow> channel) then Y i  \<^enum>  c else x  \<^enum>  c))"
    apply(rule chainI)
    apply (simp add: Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI)
    by (simp add: a1 cont_pref_eq1I fun_belowI po_class.chainE)
  have c3:"chain (\<lambda>(i::nat) c::'a. if Rep c \<in> range (Rep::'c\<Rightarrow> channel) then Y i  \<^enum>  c else x  \<^enum>  c)"
    apply(rule chainI)
    by (simp add: a1 cont_pref_eq1I fun_belowI po_class.chainE)
  show "x  \<^enum>  xa \<sqsubseteq> Rep_sb ((\<Squnion>i::nat. (\<lambda>sb2::'d\<^sup>\<Omega>. Abs_sb (\<lambda>c::'a. if Rep c \<in> range (Rep::'c\<Rightarrow> channel) then Y i  \<^enum>  c else sb2  \<^enum>  c))) x) xa"
    apply(simp add: lub_sb c2 lub_fun c1 Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI a1 )
    by(simp add: lub_fun c3 a3)
qed


lemma sbunion_insert:"sbUnion \<cdot>(sb1::'c\<^sup>\<Omega>)\<cdot>sb2 = Abs_sb (\<lambda> c. if (Rep c \<in> (range (Rep ::'c \<Rightarrow> channel))) then 
                  sb1 \<^enum> c else  sb2 \<^enum> c)"
  by(simp add: sbUnion_def)

subsubsection\<open>sbUnion abbreviation\<close>

abbreviation sbUnion_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega> \<Rightarrow> 'e\<^sup>\<Omega>" (infixr "\<uplus>" 100) where
"sb1 \<uplus> sb2 \<equiv> sbUnion\<cdot>sb1\<cdot>sb2"

subsubsection \<open>sbUnion lemmas\<close>

lemma sbunion_getch[simp]:fixes c::"'a"
      assumes"Rep c \<in> range(Rep::'c \<Rightarrow> channel)"
      shows  "(sbUnion::'a\<^sup>\<Omega>\<rightarrow> 'b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>)\<cdot>cb\<cdot>db \<^enum> c = cb \<^enum> c"
  by(simp add: Abs_sb_inverse sbGetCh.rep_eq sbunion_insert assms)

subsection \<open>sbConvert\<close>

subsubsection \<open>sbConvert definition\<close>

lemma sbconvert_well[simp]:"sb_well (\<lambda>c. sb \<^enum> c)"
  apply(rule sbwellI)
  by auto

lift_definition sbConvert::"'c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>"is
"(\<lambda> sb. Abs_sb (\<lambda>c.  sb \<^enum> c ))"
  apply(simp add: cfun_def)
  apply(rule Cont.contI2)
  apply(rule monofunI)
  apply (simp add: Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI)
  apply(simp add: Abs_sb_inverse below_sb_def)
  apply(rule fun_belowI)
  apply(simp add: cont2contlubE)
  apply(simp add: Abs_sb_inverse below_sb_def)
  by (smt cont_pref_eq1I contlub_lambda is_ub_thelub lub_eq po_class.chain_def po_eq_conv)

lemmas sbconvert_insert = sbConvert.rep_eq

subsubsection \<open>sbConvert abbreviation\<close>

abbreviation sbConvert_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega>" ( "_\<star>" 70) where 
"sb\<star> \<equiv> sbConvert\<cdot>sb"

subsubsection \<open>sbConvert lemmas\<close>

lemma sbconvert_rep[simp]: "Rep_sb(sb\<star>) = (\<lambda>c. sb \<^enum> c)"
  by (simp add: Abs_sb_inverse sbconvert_insert)

lemma fixes sb ::"'a\<^sup>\<Omega>"
  shows "sb\<star> \<^enum> c = sb \<^enum> c"
  apply(cases "Rep c\<in>(range(Rep::'a\<Rightarrow>channel))")
   apply(auto simp add: sbgetch_insert)
  oops (* gilt nicht, wenn 'b kleiner ist als 'a *)

lemma sbconv_eq[simp]:"(sbConvert::'a\<^sup>\<Omega> \<rightarrow> 'a\<^sup>\<Omega>)\<cdot>sb = sb"
  apply(rule sb_eqI)
  by (metis (no_types) Abs_sb_inverse mem_Collect_eq sbconvert_insert sbconvert_well sbgetch_insert2)

lemma sbunion_sbconvert_eq[simp]:"cb \<uplus> cb = (cb\<star>)"
  by(simp add: sbunion_insert sbconvert_insert)

subsection\<open>sbMapStream\<close>

subsubsection \<open>sbMapStream definition\<close>

definition sbMapStream:: "(M stream \<Rightarrow> M stream) \<Rightarrow> 'c\<^sup>\<Omega> \<Rightarrow>  'c\<^sup>\<Omega>" where
"sbMapStream f b = Abs_sb (\<lambda>c. f (b \<^enum> c))"  (* Nicht unbedingt wellformed... also nicht verwenden *)

subsubsection \<open>sbMapStream lemmas\<close>

lemma sbmapstream_well:assumes"\<And>s. sValues (f s) \<subseteq> sValues s" shows"sb_well (\<lambda>c. f (b \<^enum> c))"
  apply(rule sbwellI)
  using assms sValues_def sbgetch_ctypewell by fastforce

lemma sbmapstream_mono:assumes"\<And>s. sValues (f s) \<subseteq> sValues s" and "monofun f "shows"monofun (sbMapStream f)"
  apply(rule monofunI)
  apply(simp add: sbMapStream_def)
  apply(simp add: below_sb_def)
  apply(simp add: sbmapstream_well assms Abs_sb_inverse)
  by (simp add: assms(2) below_fun_def monofunE sbgetch_insert2)


subsection \<open>sbDrop\<close>

subsubsection \<open>sbDrop definition\<close>

lemma sbdrop_well[simp]:"sb_well (\<lambda>c. (Rep_cfun(sdrop n)) (b \<^enum> c))"
  apply(rule sbmapstream_well)
  by(simp add: sValues_def)

lift_definition sbDrop::"nat \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow>  'c\<^sup>\<Omega>"is
"(\<lambda> n sb.  sbMapStream (Rep_cfun(sdrop n)) sb)"
  apply(simp add: cfun_def)
  apply(rule Cont.contI2)
  apply(rule monofunI)
  apply (simp add: Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI sbMapStream_def)
  apply(simp add: Abs_sb_inverse below_sb_def sbMapStream_def)
  apply(rule fun_belowI)
  apply(simp add: cont2contlubE)
  apply(simp add: Abs_sb_inverse below_sb_def)
  by (smt cont_pref_eq1I contlub_lambda is_ub_thelub lub_eq po_class.chain_def po_eq_conv)

lemmas sbdrop_insert = sbDrop.rep_eq

subsubsection \<open>sbRt abbreviation\<close>

abbreviation sbRt :: "'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"  where 
"sbRt \<equiv> sbDrop 1"

subsubsection \<open>sbDrop lemmas\<close>

subsection \<open>sbTake\<close>

subsubsection \<open>sbTake definition\<close>

lemma sbtake_well[simp]:"sb_well (\<lambda>c::'c. stake n\<cdot>(x  \<^enum>  c))"
  apply(rule sbmapstream_well)
  by(simp add: sValues_def)

lift_definition sbTake::"lnat \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow>  'c\<^sup>\<Omega>"is
"(\<lambda> ln sb. case ln of Fin n \<Rightarrow> sbMapStream (Rep_cfun(stake n)) sb | _ \<Rightarrow> sb)"
  apply(simp add: cfun_def)
  apply(case_tac "lnat= \<infinity>")
   apply simp
  apply(subgoal_tac "\<exists>n. lnat = Fin n")
  apply auto
  apply(rule Cont.contI2)
  apply(rule monofunI)
  apply (simp add: Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI sbMapStream_def)
  apply(simp add: Abs_sb_inverse below_sb_def sbMapStream_def)
  apply(rule fun_belowI)
  apply(simp add: cont2contlubE)
  apply(simp add: Abs_sb_inverse below_sb_def)
  apply (smt cont_pref_eq1I contlub_lambda is_ub_thelub lub_eq po_class.chain_def po_eq_conv)
  using SBv3.lnat.exhaust by auto

lemmas sbtake_insert = sbTake.rep_eq

lemma sbtake_mono[simp]:"monofun sbTake"
  apply(rule monofunI)
  apply(rule cfun_belowI)
  apply(simp add: sbTake.rep_eq)
  apply(case_tac "x = \<infinity>")
  apply simp
  apply(subgoal_tac "\<exists>n. x = Fin n")
  apply auto
  apply(case_tac "y = \<infinity>")
  apply simp
  apply(simp add: sbMapStream_def)
  apply(simp add: below_sb_def)
  apply(subst Abs_sb_inverse)
  apply simp
  apply(simp add: sbgetch_insert2)
  apply (simp add: fun_belowI)
  apply (subgoal_tac "\<exists>m. y = Fin m")
  apply auto
  apply(simp add: sbMapStream_def)
  apply(simp add: below_sb_def)
  apply(simp add: Abs_sb_inverse)
  apply(simp add: sbgetch_insert2)
  apply (simp add: fun_belowI stake_mono)
  using SBv3.lnat.exhaust by auto

subsubsection \<open>sbHd abbreviation\<close>

abbreviation sbHd :: "'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"  where 
"sbHd \<equiv> sbTake 1"

subsubsection \<open>sbTake lemmas\<close>

lemma sbmap_stake_eq:"(Abs_sb (\<lambda>c::'a. stake n\<cdot>((sb::'a\<^sup>\<Omega>)  \<^enum>  c))  \<^enum>  (c::'a)) = stake n\<cdot>(sb  \<^enum>  c)"
  apply(simp add: sbgetch_insert2)
  apply(subst Abs_sb_inverse)
  apply simp
  apply(rule sbwellI)
  apply (metis sbgetch_insert2 sbgetch_ctypewell dual_order.trans sdom_sconc split_streaml1)
  by simp

lemma sbtake_max_len [simp]: "#(sbTake ln\<cdot>(sb::'a\<^sup>\<Omega>) \<^enum> (c::'a)) \<le> ln"
  apply(simp add: sbTake.rep_eq)
  apply(cases "ln = \<infinity>")
  apply simp
  apply(subgoal_tac "\<exists>n. ln = Fin n")
  apply auto
  apply(simp add: sbMapStream_def sbmap_stake_eq)
  by (meson SBv3.lnat.exhaust) 


subsection \<open>sbConc\<close>

subsubsection \<open>sbConc definition \<close>

lemma sbconc_well[simp]:"sb_well (\<lambda>c. (sb1 \<^enum> c )\<bullet>(sb2 \<^enum> c))"
  apply(rule sbwellI)
  by (metis (no_types, hide_lams) Un_subset_iff dual_order.trans sbgetch_ctypewell sconc_sdom)


lift_definition sbConc:: "'c\<^sup>\<Omega>  \<Rightarrow>  'c\<^sup>\<Omega> \<rightarrow>  'c\<^sup>\<Omega>" is
"\<lambda> sb1 sb2. Abs_sb(\<lambda>c. (sb1 \<^enum> c )\<bullet>(sb2 \<^enum> c))"
  apply(simp add: cfun_def)
  apply(rule Cont.contI2)
  apply(rule monofunI)
  apply (simp add: Abs_sb_inverse below_sb_def cont_pref_eq1I fun_belowI sbMapStream_def)
  apply(simp add: Abs_sb_inverse below_sb_def sbMapStream_def)
  apply(rule fun_belowI)
  apply(simp add: cont2contlubE)
  apply(simp add: Abs_sb_inverse below_sb_def)
  by (smt cont_pref_eq1I contlub_lambda is_ub_thelub lub_eq po_class.chain_def po_eq_conv)

lemmas sbconc_insert = sbConc.rep_eq

subsubsection \<open> sbConc abbreviation \<close>

abbreviation sbConc_abbr :: "'c\<^sup>\<Omega>  \<Rightarrow>  'c\<^sup>\<Omega> \<Rightarrow>  'c\<^sup>\<Omega>" (infixr "\<bullet>\<^sup>\<Omega>" 70) where 
"sb1 \<bullet>\<^sup>\<Omega> sb2 \<equiv> sbConc sb1\<cdot>sb2"


subsubsection \<open>sbConc lemmas\<close>

lemma sbconc_eq:"sb \<bullet>\<^sup>\<Omega> \<bottom> = sb"
  apply(simp add: sbconc_insert sbgetch_bot)
  by (metis sbconv_eq sbconvert_insert)

subsection \<open>sbLen\<close>

subsubsection \<open>sbLen definition \<close>

definition sbLen::"'c\<^sup>\<Omega> \<Rightarrow> lnat"where
"sbLen sb = (LEAST n . n\<in>(insert (\<infinity>::lnat) {#(sb \<^enum> (c::'c)) | c. ((Rep::'c \<Rightarrow> channel) c)\<notin>cEmpty}))"


lemma sblen_mono:"monofun sbLen"
  apply(rule monofunI)

  apply(simp add: sbLen_def)

proof -
fix x :: "'a\<^sup>\<Omega>" and y :: "'a\<^sup>\<Omega>"
  assume a1: "x \<sqsubseteq> y"
obtain aa :: "lnat \<Rightarrow> 'a" where
  f2: "\<And>l. (l \<noteq> \<infinity> \<and> (\<forall>a. l \<noteq> #(y \<^enum> (a::'a)) \<or> Rep a \<in> cEmpty) \<or> Rep (aa l) \<notin> cEmpty \<or> l = \<infinity>) \<and> (l \<noteq> \<infinity> \<and> (\<forall>a. l \<noteq> #(y \<^enum> (a::'a)) \<or> Rep a \<in> cEmpty) \<or> #(y \<^enum> aa l) = l \<or> l = \<infinity>)"
by moura
  then have f3: "\<And>l. l \<noteq> \<infinity> \<and> (\<forall>a. l \<noteq> #(y \<^enum> (a::'a)) \<or> Rep a \<in> cEmpty) \<or> l = \<infinity> \<or> #(Rep_sb x (aa l)) \<le> l"
using a1 by (metis (full_types) sbgetch_below_slen sbgetch_insert2)
  obtain ll :: "(lnat \<Rightarrow> bool) \<Rightarrow> (lnat \<Rightarrow> bool) \<Rightarrow> lnat" where
    f4: "\<And>p l pa la. (\<not> p l \<or> pa (Least p) \<or> p (ll p pa)) \<and> (\<not> p la \<or> \<not> pa (ll p pa) \<or> pa (Least p))"
by (metis LeastI2_wellorder_ex)
  then have "((LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) = \<infinity> \<or> (\<exists>a. (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<and> (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<noteq> \<infinity> \<or> (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) = \<infinity>"
 
    by smt
moreover
  { assume "((LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) = \<infinity> \<or> (\<exists>a. (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<and> (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<noteq> \<infinity>"
then have "Rep (aa (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty))) \<notin> cEmpty"
  using f2 by meson
  then have "#(Rep_sb x (aa (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)))) = \<infinity> \<or> (\<exists>a. #(Rep_sb x (aa (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)))) = #(x \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)"
    by (metis (no_types) sbgetch_insert2)
then have "(LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(x \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<le> #(Rep_sb x (aa (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty))))"
  by (simp add: Least_le)
then have "((LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) = \<infinity> \<or> (\<exists>a. (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<and> (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(x \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<le> #(Rep_sb x (aa (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)))) \<and> (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<noteq> \<infinity> \<or> (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) = \<infinity>"
  using f4 
  using calculation by blast
  then have "(LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) = \<infinity> \<or> (\<exists>l\<le>LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty). (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(x \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<le> l)"
    using f3 by meson }
  ultimately have "\<exists>l\<le>LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty). (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(x \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<le> l"
    using inf_less_eq inf_ub by blast
then show "(LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(x \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<le> (LEAST l. l = \<infinity> \<or> (\<exists>a. l = #(y \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty))"
  by (meson dual_order.trans)
qed
 

subsubsection \<open> sbLen lemmas \<close>

lemma sblen_min_len [simp]: "sbLen sb \<le> #((sb::'a\<^sup>\<Omega>) \<^enum> (c::'a))" (* TODO: vermutlich typ von "c" fixieren *)
  
   sledgehammer[cvc4 z3 spass e remote_vampire]
  
   oops

lemma sbtake_len [simp]: "#((sbTake (sbLen (sb::'a\<^sup>\<Omega>))\<cdot>sb) \<^enum> (c::'a)) = sbLen sb" (* TODO: vermutlich typ von "c" fixieren *)
  apply(simp add:sbTake_def sbLen_def)
  



  oops

lemma sblen_sbeqI:"x \<sqsubseteq> y \<Longrightarrow> sbLen x = \<infinity> \<Longrightarrow> x = y"
  apply(simp add: sbLen_def)

proof -
assume a1: "x \<sqsubseteq> y"
  assume a2: "(LEAST n. n = \<infinity> \<or> (\<exists>c. n = #(x \<^enum> (c::'a)) \<and> Rep c \<notin> cEmpty)) = \<infinity>"
have f3: "\<And>c. (c\<cdot>x::M stream) \<sqsubseteq> c\<cdot>y"
  using a1 by (metis monofun_cfun_arg)
  have f4: "\<And>l. \<not> (l = \<infinity> \<or> (\<exists>a. l = #(x \<^enum> (a::'a)) \<and> Rep a \<notin> cEmpty)) \<or> \<infinity> \<le> l"
    using a2
    by (metis (mono_tags, lifting) Least_le)
have f5: "\<And>c. c \<notin> cEmpty \<or> ctype c = {}"
  using cEmpty_def by blast
obtain aa :: "'a\<^sup>\<Omega> \<Rightarrow> 'a\<^sup>\<Omega> \<Rightarrow> 'a" where
  "\<And>s sa. s \<^enum> aa s sa \<noteq> sa \<^enum> aa s sa \<or> s = sa"
  using sb_eqI by moura
  then show ?thesis
    using f5 f4 f3 by (metis eq_less_and_fst_inf inf_less_eq sbgetch_ctype_notempty)
qed
 

subsection\<open>sbIsLeast Predicate\<close>

(* TODO: Lemma, zB mit "sbLeast" und "sbECons" *)
definition sbIsLeast::"'cs\<^sup>\<Omega> \<Rightarrow> bool" where
"sbIsLeast sb = ((sbLen sb = 0) \<or> (chIsEmpty (TYPE('cs))))"

subsection \<open>sbIsLeast lemmas\<close>

lemma "sbIsLeast \<bottom>"
  apply(simp add: sbIsLeast_def sbLen_def sbgetch_bot chIsEmpty_def)
  apply(case_tac "(\<exists>c::'a. Rep c \<notin> cEmpty)",simp_all)
  apply (metis (mono_tags, lifting) Inf'_neq_0_rev LeastI_ex Least_le inf_less_eq)
  by (simp add: image_subset_iff)

lemma sbtypeepmpty_sbbot[simp]:"chIsEmpty TYPE ('cs) \<Longrightarrow> (sb::'cs\<^sup>\<Omega>) = \<bottom>"
  apply(simp add: chIsEmpty_def)
  apply(rule sb_eqI)
  apply(simp add: sbgetch_insert2 bot_sb)
  apply(subst Abs_sb_inverse)
  apply(simp add: sb_well_def sValues_def)
  by (smt Rep_sb bot.extremum cEmpty_def f_inv_into_f image_subset_iff iso_tuple_UNIV_I 
      mem_Collect_eq rangeI range_eqI sValues_def sbGetCh.abs_eq sb_well_def sbgetch_insert 
      sbgetch_insert2 strict_sdom_rev subset_antisym)

section \<open>sbElem functions \<close>

subsection\<open>sbe2sb\<close>

subsubsection \<open>sbe2sb definition\<close>

lift_definition sbe2sb::" 'c\<^sup>\<surd> \<rightarrow> 'c\<^sup>\<Omega>" is
"(\<lambda> sbe. if  (Rep_sbElem sbe) =None then \<bottom> else Abs_sb(\<lambda>c. \<up>((the (Rep_sbElem sbe)) c))) "
  by(simp add: cfun_def)

lemmas sbe2sb_insert = sbe2sb.rep_eq


subsubsection \<open>sbe2sb lemmas\<close>

subsection\<open>sbECons\<close>

subsubsection \<open>sbE2Cons definition\<close>

lift_definition sbECons::"'c\<^sup>\<surd> \<rightarrow> 'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>" is
"(\<lambda> sbe. sbConc (sbe2sb\<cdot>sbe))"
  by (simp add: cfun_def)

lemmas sbecons_insert = sbECons.rep_eq

subsubsection \<open>sbE2Cons abbreviation\<close>

abbreviation sbECons_abbr :: "'c\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega>" (infixr "\<bullet>\<^sup>\<surd>" 100) where 
"sbe \<bullet>\<^sup>\<surd> sb \<equiv> sbECons\<cdot>sbe\<cdot>sb"


subsubsection \<open>sbE2Cons lemmas\<close>


lemma sbecons_len:"sbLen (sbe \<bullet>\<^sup>\<surd> sb) = lnsuc\<cdot>(sbLen sb)"
  oops

lemma sbtypeempty_sbecons_bot[simp]:"chIsEmpty TYPE ('cs) \<Longrightarrow> (sbe::'cs\<^sup>\<surd>) \<bullet>\<^sup>\<surd> sb = \<bottom>"
  by simp

lemma [simp]:"chIsEmpty TYPE ('cs) \<Longrightarrow> P(sb) \<Longrightarrow> P( (sbe::'cs\<^sup>\<surd>) \<bullet>\<^sup>\<surd> sb)"
  by (metis (full_types) sbtypeepmpty_sbbot)

lemma sb_cases [case_names least sbeCons, cases type: sb]: 
  "(sbIsLeast (sb'::'cs\<^sup>\<Omega>) \<Longrightarrow> P) 
  \<Longrightarrow> (\<And>sbe sb. sb' = sbECons\<cdot>sbe\<cdot>sb \<Longrightarrow> \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> P) 
  \<Longrightarrow> P"
  oops

lemma sb_finind:
    fixes x::"'cs\<^sup>\<Omega>"
  assumes "sbLen x < \<infinity>"
      and "\<And>sb. sbIsLeast sb \<Longrightarrow> P sb"
      and "\<And>sbe sb. P sb \<Longrightarrow> \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb)"
    shows "P x"
  oops

lemma sb_ind[case_names adm least sbeCons, induct type: sb]:
    fixes x::"'cs\<^sup>\<Omega>"
  assumes "adm P" 
      and "\<And>sb. sbIsLeast sb \<Longrightarrow> P sb"
      and "\<And>sbe sb. P sb  \<Longrightarrow> \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb)"   
  shows  "P x"
  oops

subsection\<open>sbHdElem\<close>

subsubsection \<open>sbHdElem definition\<close>

lemma sbhdelem_mono:"monofun
     (\<lambda>sb::'c\<^sup>\<Omega>.
         if range (Rep::'c \<Rightarrow> channel) \<subseteq> cEmpty then Iup (Abs_sbElem None)
         else if \<exists>c::'c. sb  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (sb  \<^enum>  c)))))"
  apply(rule monofunI)
  apply(cases "range (Rep::'c \<Rightarrow> channel) \<subseteq> cEmpty")
  apply simp
  apply auto
  apply (metis below_bottom_iff monofun_cfun_arg)
  by (meson below_shd monofun_cfun_arg)

definition sbHdElem_h::"'c\<^sup>\<Omega> \<Rightarrow> ('c\<^sup>\<surd>) u"where 
"sbHdElem_h = (\<lambda> sb. if (range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty) then Iup(Abs_sbElem None) else 
        if (\<exists>c::'c. sb \<^enum> c = \<epsilon>) then \<bottom> else Iup(Abs_sbElem (Some (\<lambda>c. shd((sb) \<^enum> c)))))"

definition sbHdElem::"'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<surd>"where
"sbHdElem = (\<lambda> sb. case (sbHdElem_h sb) of Iup sbElem \<Rightarrow> sbElem | _ \<Rightarrow> undefined)"

subsubsection \<open>sbHdElem abbreviation \<close> (*TODO: better abbreviation lfloor*)

abbreviation sbHdElem_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<surd>" ( "\<lfloor>_" 70) where 
"\<lfloor>sb \<equiv> sbHdElem sb"

subsubsection \<open>sbHdElem lemmas\<close>

lemma sbhdelem_none[simp]:"(range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty) \<Longrightarrow> sbHdElem((x::('c)\<^sup>\<Omega>)) = Abs_sbElem(None)"
  by(simp add: sbHdElem_def sbHdElem_h_def)

lemma sbhdelem_some:"((\<forall>c::'c. x \<^enum> c \<noteq> \<epsilon>) \<and> x\<noteq>\<bottom>) \<Longrightarrow> sbHdElem((x::('c)\<^sup>\<Omega>)) = Abs_sbElem(Some(\<lambda>c. shd((x) \<^enum> c)))"
  apply(simp add: sbHdElem_def sbHdElem_h_def,auto)
  using cEmpty_def sbgetch_ctype_notempty by fastforce

lemma sbhdelem_mono_empty[simp]:"((range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty)) \<Longrightarrow> (x::('c)\<^sup>\<Omega>) \<sqsubseteq> y \<Longrightarrow> sbHdElem x = sbHdElem y"
  by(simp)

lemma sbhdelem_mono_eq[simp]:"(\<And>c::'a. (x::'a\<^sup>\<Omega>) \<^enum> c \<noteq> \<epsilon>) \<Longrightarrow>  x \<sqsubseteq> y \<Longrightarrow> sbHdElem x = sbHdElem y"
proof-
  assume a1:"(\<And>c::'a. x  \<^enum>  c \<noteq> \<epsilon>)"
  assume a2:"x \<sqsubseteq> y"
  then have "\<And>c::'a. ctype (Rep c) \<noteq> {}"
    using a1 sbgetch_ctype_notempty by auto
  then have not_none:"\<not>(range(Rep::'a\<Rightarrow> channel)\<subseteq>cEmpty)"
    by(simp add: cEmpty_def,auto)
  then have a3:"(\<And>c::'a. y  \<^enum>  c \<noteq> \<epsilon>)"
    by (metis a1 a2 below_bottom_iff monofun_cfun_arg)
  then have not_bot:"x\<noteq>\<bottom> \<and> y \<noteq> \<bottom>"
    using a1 sbgetch_bot by auto
  then have h1:"\<And>c::'a. shd (x  \<^enum>  c) = shd (y  \<^enum>  c)"
    by (simp add: a1 a2 below_shd monofun_cfun_arg)
  then show ?thesis
    apply(subst sbhdelem_some)
    using not_bot a1  not_none apply auto[1]
    apply(subst sbhdelem_some)
    using not_bot a3 not_none apply auto[1]
    by(simp add: h1)
qed                               

lemma sbecons_eq:assumes "sbLen sb \<noteq> 0" shows "(sbHdElem sb) \<bullet>\<^sup>\<surd> (sbRt\<cdot>sb) = sb"
  oops

(*
lemma sblen_mono[simp]:"monofun sbLen"
  apply(rule monofunI)
proof(simp add: sbLen_def)
  fix x::"'a\<^sup>\<Omega>" and y::"'a\<^sup>\<Omega>"
  assume a1:"x \<sqsubseteq> y"
  then have h1:"\<forall>c::'a . #(x  \<^enum>  c) \<sqsubseteq> #(y  \<^enum>  c)"
    by simp
  then have "\<exists>c::'a. #(x  \<^enum>  c) \<sqsubseteq> #(y  \<^enum>  c)"
    by simp
  then show "(LEAST n::lnat. n = \<infinity> \<or> (\<exists>c::'a. n = #(x  \<^enum>  c) \<and> Rep c \<notin> cEmpty)) \<le> (LEAST n::lnat. n = \<infinity> \<or> (\<exists>c::'a. n = #(y  \<^enum>  c) \<and> Rep c \<notin> cEmpty))"
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
    have "\<exists>(c::'a).  \<forall>c2::'a.  #(x  \<^enum>  c) \<sqsubseteq> #((x \<^enum> c2))"(*? ? ?*)
    proof(cases "\<exists>(c::'a).  \<forall>c2::'a.  #(x  \<^enum>  c) \<sqsubseteq> #((x \<^enum> c2))" )
      case True
      then show ?thesis 
         by simp
    next
      case False
      then have "\<forall>c2::'a. \<exists>c::'a. #(x  \<^enum>  c2) \<sqsubseteq> #(x  \<^enum>  c)"
        by auto
      then have "\<exists>(c::'a).  \<forall>c2::'a.  #(x  \<^enum>  c) \<sqsubseteq> #((x \<^enum> c2))"
        sorry
      then show ?thesis
        by auto
    qed
    then show ?thesis
      apply auto 
      sorry
  qed

lemma sblen_notbot:"\<exists>c::'c. (Rep::'c\<Rightarrow> channel) c \<noteq> cbot \<Longrightarrow> sbLen (sb::'c\<^sup>\<Omega>) = (LEAST n. n\<in>{#(sb \<^enum> c) | c::'c. True})"
  apply(simp add: sbLen_def)
  apply(cases "\<exists>c::'c. #(sb  \<^enum>  c) = \<infinity>")
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
  assume a2:"chain (\<lambda>i::nat. LEAST n::lnat. n = \<infinity> \<or> (\<exists>c::'c. n = #(Y i  \<^enum>  c) \<and> Rep c \<noteq> cbot))"
  assume a3:"\<exists>c::'c. Rep c \<noteq> cbot"
  then show "(LEAST n::lnat. \<exists>c::'c. n = #(Lub Y  \<^enum>  c)) \<le> (\<Squnion>i::nat. LEAST n::lnat. \<exists>c::'c. n = #(Y i  \<^enum>  c))"
    apply(subst contlub_cfun_arg, simp add: a1)
    apply(subst contlub_cfun_arg)
    sorry
qed
*)

end
