(*<*)(*:maxLineLen=68:*)
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


default_sort %invisible chan

section \<open>Stream Bundles \label{sec:sb}\<close>

text \<open>Streams are the backbone of this verification 
framework and stream bundles are used to model components with 
multiple input and output streams by bundleing streams together. Any
stream in a stream bundle is identifiable through its channel. 
Hence, a \gls{sb} is a function from channels to streams.
Since the allowed messages on a channel may be restricted, the 
streams of a \gls{sb} only contain streams of elements from the
@{const ctype} of their channel. Similar to @{type sbElem}s, we 
formulate a predicate to describe the properties of a \gls{sb}.\<close>

definition sb_well :: "('c::chan \<Rightarrow> M stream) \<Rightarrow> bool" where
"sb_well f \<equiv> \<forall>c. sValues\<cdot> (f c) \<subseteq> ctype (Rep c)"

text\<open>This definition uses @{const sValues} defined as
@{thm sValues_def}
to obtain a set, which contains every element occurring in a stream.
If the values of each stream are a subset of the allowed messages 
on their corresponding channels, the function is a \gls{sb}. Unlike 
to our @{type sbElem} predicate, a differentiation for the empty
domain is not necessary, because it follows directly from 
@{const sb_well} that there can be no non-empty stream for bundles 
with an empty domain.\<close>

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

text\<open>Since we define stream bundles as total functions from channels
to streams, we can also instantiate them as a \gls{pcpo}.\<close>

pcpodef 'c::chan sb("(_\<^sup>\<Omega>)" [1000] 999) 
         = "{f::('c::chan \<Rightarrow> M stream). sb_well f}"
  by (auto simp add: sbwell_ex sbwell_adm lambda_strict[symmetric])

(* TODO: Remove Warning
 Information at the bottom of Stream.thy *)
setup_lifting %invisible type_definition_sb

subsection \<open>SB Type Properties \label{sub:svtpro}\<close>

text\<open>Then the \<open>\<bottom>\<close> element of our \gls{sb} type, is of course a 
mapping to empty streams.\<close>

theorem bot_sb:"\<bottom> = Abs_sb(\<lambda>c. \<epsilon>)"
  by (simp add: Abs_sb_strict lambda_strict)

lemma rep_sb_well[simp]:"sb_well(Rep_sb sb)"
  using Rep_sb by auto

lemma abs_rep_sb_sb[simp]:"Abs_sb(Rep_sb sb) = sb"
  using Rep_sb_inverse by auto

lemma sbrep_cont[simp, cont2cont]: "cont Rep_sb"
  using cont_Rep_sb cont_id by blast
(*
text\<open>This is a continuity property for SBs.\<close>*)
lemma sb_abs_cont2cont [cont2cont]: 
  assumes "cont h" 
  and "\<And>x. sb_well (h x)"
  shows "cont (\<lambda>x. Abs_sb (h x))"
  by (simp add: assms(1) assms(2) cont_Abs_sb)

lemma sb_rep_eqI:assumes"\<And>c. (Rep_sb sb1) c = (Rep_sb sb2) c"
  shows "sb1 = sb2"
  by(simp add: po_eq_conv below_sb_def fun_belowI assms)

text\<open>In case of an empty domain, no stream should be in a \gls{sb}.
Hence, every \gls{sb} with an empty domain should be \<open>\<bottom>\<close>. This is
proven in the following theorem.\<close>

theorem sbtypeepmpty_sbbot[simp]:
  "chDomEmpty TYPE ('cs::chan) 
  \<Longrightarrow> (sb::'cs\<^sup>\<Omega>) = \<bottom>"
  unfolding chDom_def cEmpty_def bot_sb
  apply(rule sb_rep_eqI)
  apply(subst Abs_sb_inverse)
  apply (simp add: sbwell_ex,auto)
  apply(insert sb_well_def[of "Rep_sb sb"],auto)
  using strict_sValues_rev by fastforce

lemma sbwell2fwell[simp]:"Rep_sb sb = f \<Longrightarrow> sb_well f"
  using Rep_sb by auto

subsection \<open>SB Functions \label{sub:sbfun}\<close>

text\<open>This section defines and explains the most commonly used 
functions for \Gls{sb}. Also, the main properties of important 
functions will be discussed.\<close>

subsubsection \<open>Converter from sbElem to SB \label{subsub:sbe2sb}\<close>

text\<open>First we construct a converter from @{type sbElem}s to 
\Gls{sb}. This is rather straight forward, since we either have a 
function from channels to messages, which we can easily convert to a
function from channels to streams, which consists only of streams 
with the exact message from the @{type sbElem}. In the case of an 
empty domain, we map @{const None} to the \<open>\<bottom>\<close> element of \Gls{sb}.\<close> 

lift_definition sbe2sb::" 'c\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<Omega>" is
"\<lambda> sbe. case (Rep_sbElem sbe) of Some f \<Rightarrow> (\<lambda>c. \<up>(f c))
                                | None  \<Rightarrow> \<bottom> "
  apply(rule sbwellI, auto)
  apply(case_tac "Rep_sbElem sbElem = None")
  apply auto
  apply(subgoal_tac "sbElem_well (Some y)",simp)
  by(simp only: sbelemwell2fwell)

text\<open>Through the usage of keyword \<open>lift_definition\<close> instead of 
\<open>definition\<close> we automatically have to proof that the output is 
indeed a \gls{sb}.\<close>

subsubsection \<open>Extracting a single stream \label{subsub:sbgetch}\<close>

text\<open>The direct access to a stream on a specific channel is one of
the most important functions for defining the framework and also 
often used for verifying components. Intuitively, the signature of
such a function should be \<open>'c \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow> M stream \<close>, but we use a 
slightly more general signature. This facilitates later function 
definitions and also reduces the total framework size.\<close>

lift_definition sbGetCh :: "'e \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow> M stream" is
"(\<lambda>c sb. if Rep c\<in>chDom TYPE('c) 
            then Rep_sb sb (Abs(Rep c)) 
            else \<epsilon>)"
  apply(intro cont2cont)
  by(simp add: cont2cont_fun)

text\<open>Our general signature allows the input of any channel from the
@{type channel} type. If the channel is in the domain of the input
\gls{sb}, we obtain the corresponding channel. Is the channel not in
the domain, the empty stream \<open>\<epsilon>\<close> is returned. The continuity of this
function is also immediately proven.\<close> 

lemmas sbgetch_insert = sbGetCh.rep_eq

text\<open>The next abbreviations are defined to differentiate between the
intuitive and the expanded signature of @{const sbGetCh}. The first 
abbreviation is an abbreviation for the general signature, the 
second restricts to the intuitive signature.\<close>

abbreviation sbgetch_magic_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'e \<Rightarrow> M stream"
(infix " \<^enum>\<^sub>\<star> " 65) where "sb \<^enum>\<^sub>\<star> c \<equiv> sbGetCh c\<cdot>sb"

abbreviation sbgetch_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'c \<Rightarrow> M stream"
(infix " \<^enum> " 65) where "sb \<^enum> c \<equiv> sbGetCh c\<cdot>sb"

text \<open>Obtaining a @{type sbElem} form a \gls{sb} is not always 
possible. If the domain of a bundle is not empty but there is an 
empty stream on a channel, the resulting @{type sbElem} could not 
map that channel to a message from the stream. Hence, no slice of 
such a \gls{sb} can be translated to a @{type sbElem}. The following
predicate states, that the first slice of an \gls{sb} with a 
non-empty domain can be transformed to a @{type sbElem}, because it 
checks, if all streams in the bundle are not empty.\<close>

definition sbHdElemWell::"'c\<^sup>\<Omega>  \<Rightarrow> bool" where
"sbHdElemWell  \<equiv> \<lambda> sb. (\<forall>c. sb  \<^enum>  c \<noteq> \<epsilon>)"  

paragraph \<open>sbGetCh Properties\<close>

text\<open>When using the intuitively variant of @{const sbGetCh}, it
obtains a stream from a channel. It should never be able to do
anything else. This behavior is verified by the following theorem.
Obtaining a stream from its \gls{sb} is the same as obtaining the 
output from the function realizing the \gls{sb}.\<close>

theorem sbgetch_insert2:"sb \<^enum> c = (Rep_sb sb) c"
  apply(simp add: sbgetch_insert)
  by (metis (full_types)Rep_sb_strict app_strict cnotempty_cdom 
      sbtypeepmpty_sbbot)

lemma sbhdelemchain[simp]:
  "sbHdElemWell x \<Longrightarrow>  x \<sqsubseteq> y \<Longrightarrow> sbHdElemWell y"
  apply(simp add: sbHdElemWell_def sbgetch_insert2)
  by (metis below_antisym below_sb_def fun_belowD minimal)

lemma sbgetch_ctypewell[simp]:"sValues\<cdot>(sb \<^enum>\<^sub>\<star> c) \<subseteq> ctype (Rep c)"
  apply(simp add: sbgetch_insert)
  by (metis DiffD1 chDom_def f_inv_into_f sb_well_def sbwell2fwell)

lemma sbmap_well:assumes"\<And>s. sValues\<cdot>(f s) \<subseteq> sValues\<cdot>s" 
                 shows"sb_well (\<lambda>c. f (b \<^enum>\<^sub>\<star> c))"
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

lemma sbhdelemnotempty:
  "sbHdElemWell (sb::'cs\<^sup>\<Omega>) \<Longrightarrow>  \<not> chDomEmpty TYPE('cs)"
  apply(auto simp add: sbHdElemWell_def chDom_def cEmpty_def)
  by (metis (mono_tags) Collect_mem_eq Collect_mono_iff repinrange 
      sbgetch_ctype_notempty)

text\<open>If a \gls{sb} \<open>x\<close> is @{const below} another \gls{sb} \<open>y\<close>, the 
order also holds for each streams on every channel.\<close>

theorem sbgetch_sbelow[simp]:"sb1 \<sqsubseteq> sb2 \<Longrightarrow> (sb1 \<^enum>\<^sub>\<star> c) \<sqsubseteq> (sb2 \<^enum>\<^sub>\<star> c)"
  by (simp add: mono_slen monofun_cfun_arg)

lemma sbgetch_below_slen[simp]:
  "sb1 \<sqsubseteq> sb2 \<Longrightarrow> #(sb1 \<^enum>\<^sub>\<star> c) \<le> #(sb2 \<^enum>\<^sub>\<star> c)"
  by (simp add: mono_slen monofun_cfun_arg)

lemma sbgetch_bot[simp]:"\<bottom> \<^enum>\<^sub>\<star> c = \<epsilon>"
  apply(simp add: sbGetCh.rep_eq bot_sb)
  by (metis Rep_sb_strict app_strict bot_sb)

text\<open>Now we can show the equality and below property of two \Gls{sb}
though the relation of their respective streams.\<close>

theorem sb_belowI:
  fixes sb1 sb2::"'cs\<^sup>\<Omega>"
    assumes "\<And>c.  sb1 \<^enum> c \<sqsubseteq> sb2 \<^enum> c"
    shows "sb1 \<sqsubseteq> sb2"
  apply(subst below_sb_def)
  apply(rule fun_belowI)
  by (metis (full_types) assms sbgetch_insert2)

text\<open>If all respectively chosen streams of one bundle are 
\@{const below} the streams of another bundle, the @{const below}
relation holds for the bundles as well.\<close>

theorem sb_eqI:
  fixes sb1 sb2::"'cs\<^sup>\<Omega>"
    assumes "\<And>c. sb1 \<^enum> c = sb2 \<^enum> c"
    shows "sb1 = sb2"
  apply(cases "chDom TYPE('cs) \<noteq> {}")
  apply (metis assms sb_rep_eqI sbgetch_insert2)
  by (metis (full_types) sbtypeepmpty_sbbot)

text\<open>If all respectively chosen streams of one bundle are equal to 
the streams of another bundle, these bundles are the same.\<close>

lemma slen_empty_eq:  assumes"chDomEmpty(TYPE('c))"
  shows " #(sb \<^enum> (c::'c)) =0"
  using assms chDom_def cEmpty_def sbgetch_ctype_notempty 
  by fastforce

text\<open>Lastly, the conversion from a @{type sbElem} to a \gls{sb}
should never result in a \gls{sb} which maps its domain to \<open>\<epsilon>\<close>.\<close>

theorem sbgetch_sbe2sb_nempty: assumes "\<not>chDomEmpty(TYPE('a))"
  shows "\<forall>c::'a. sbe2sb sbe  \<^enum>  c \<noteq> \<epsilon>"
  apply (simp add: sbe2sb_def)
  apply (simp split: option.split) 
  apply (rule conjI)
  apply (rule impI)
  using assms chDom_def sbElem_well.simps(1) sbelemwell2fwell 
  apply blast
  apply (rule allI, rule impI, rule allI)
  by (metis (no_types) option.simps(5) sbe2sb.abs_eq sbe2sb.rep_eq 
      sbgetch_insert2 sconc_snd_empty srcdups_step srcdupsimposs 
      strict_sdropwhile)


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
"sbLen sb = (if (chDomEmpty TYPE('c)) then \<infinity> else (LEAST n . n\<in>({#(sb \<^enum> c) | c. True})))"

subsubsection \<open> sbLen lemmas \<close>

lemma sblen_min_len_empty[simp]:
  assumes"chDomEmpty(TYPE('c))"
  shows " sbLen (sb::'c\<^sup>\<Omega>) = \<infinity>"
  by(simp add: sbLen_def assms slen_empty_eq)
lemma sblen_min_len [simp]:
  assumes"\<not>chDomEmpty(TYPE('c))"
  shows"sbLen (sb :: 'c\<^sup>\<Omega>) \<le> #(sb \<^enum> c)"
  apply(simp add: sbLen_def assms)
  by (metis (mono_tags, lifting) Least_le)


lemma sblenleq: assumes "\<not> chDomEmpty TYPE('a)" and
 "\<exists>c::'a. #(sb\<^enum>c) \<le> k"
  shows "sbLen sb \<le> k" 
  apply(simp add: sbLen_def assms)
  apply(subgoal_tac "\<And>c::'a. Rep c \<notin> cEmpty") 
  apply auto
  apply (metis (mono_tags, lifting) Least_le assms(2) dual_order.trans)
  using assms(1) by simp

lemma sblengeq: assumes "\<And>c::'c. k\<le> #(sb\<^enum>c)"
  shows "k \<le> sbLen sb" 
  apply(cases  "chDomEmpty(TYPE('c))",simp add: assms)
  apply(simp add: sbLen_def)
  using LeastI2_wellorder_ex inf_ub insert_iff mem_Collect_eq sbLen_def assms by smt

lemma sblen_sbconc: "((sbLen sb1) + (sbLen sb2)) \<le> (sbLen (sb1 \<bullet>\<^sup>\<Omega> sb2))"
  apply(cases  "chDomEmpty(TYPE('a))",simp)
  apply(rule sblengeq)
  by (metis lessequal_addition sbconc_getch sblen_min_len sconc_slen2)

lemma sblen_mono:"monofun sbLen"
  apply(rule monofunI,simp)
  apply(cases "chDomEmpty TYPE('a)",simp)
  apply(rule sblengeq)
  apply(rule sblenleq)
  using sbgetch_below_slen by auto

lemma sblen_monosimp[simp]:"x \<sqsubseteq> y \<Longrightarrow> sbLen x \<le> sbLen y"
  using lnle_conv monofunE sblen_mono by blast

lemma sblen_rule:assumes "\<not>chDomEmpty(TYPE('a))" and "\<And>c. k \<le> #(sb \<^enum> (c :: 'a ))" and "\<exists>c. #(sb \<^enum> (c :: 'a )) = k"
  shows" sbLen sb = k"
  by (metis assms(1) assms(2) assms(3) dual_order.antisym sblen_min_len sblengeq)
 
lemma sblen_sbeqI:"x \<sqsubseteq> y \<Longrightarrow> sbLen x = \<infinity> \<Longrightarrow> x = y"
  apply(cases "chDomEmpty TYPE('a)")
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

lemma sblen_leadm:"adm (\<lambda>sb. k \<le> sbLen sb)"
proof(rule admI)
 fix Y :: "nat \<Rightarrow>'a\<^sup>\<Omega> " and k :: lnat
  assume chY:  "chain Y" and  as2: "  \<forall>i::nat. k \<le> sbLen (Y i) "
  have "\<And>i. sbLen (Y i) \<sqsubseteq>sbLen( \<Squnion>i. Y i)"
    using sblen_mono chY is_ub_thelub lnle_def monofun_def by blast
  then show " k \<le> sbLen (\<Squnion>i::nat. Y i)" 
    using as2 box_below lnle_def sblen_mono chY is_ub_thelub lnle_def monofun_def by blast
qed

lemma sblen2slen_h:
  fixes "c1"
  assumes"\<not>chDomEmpty(TYPE('c))"
  and "\<forall>c2. #((sb :: 'c\<^sup>\<Omega>) \<^enum> c1) \<le> #(sb \<^enum> c2)"
  shows "#((sb :: 'c\<^sup>\<Omega>) \<^enum> c1) = sbLen sb"
  apply(simp add: sbLen_def)
  apply(subst Least_equality[of "\<lambda>n. \<exists>c::'c. n = #(sb  \<^enum>  c)" "#((sb :: 'c\<^sup>\<Omega>) \<^enum> c1)"])
  apply(simp_all add: assms)
   apply auto[1]
  using assms(2) by auto

lemma sb_minstream_exists:
  assumes "\<not>chDomEmpty(TYPE('c))"
  shows "\<exists>c1. \<forall>c2. #((sb :: 'c\<^sup>\<Omega>) \<^enum> c1) \<le> #(sb \<^enum> c2)"
  using  assms
proof -
  { fix cc :: "'c \<Rightarrow> 'c"
    have ff1: "\<forall>s c l. l \<le> #(s \<^enum> (c::'c)) \<or> \<not> l \<le> sbLen s"
      by (meson assms sblen_min_len trans_lnle)
    { assume "\<exists>c l. \<not> l \<le> #(sb \<^enum> c)"
      then have "\<not> \<infinity> \<le> sbLen sb"
        using ff1 by (meson inf_ub trans_lnle)
      then have "\<exists>c. #(sb \<^enum> c) \<le> #(sb \<^enum> cc c)"
        using ff1 by (metis less_le_not_le ln_less Orderings.linorder_class.linear lnle2le sblengeq) }
    then have "\<exists>c. #(sb \<^enum> c) \<le> #(sb \<^enum> cc c)"
      by meson }
  then show ?thesis
    by metis
qed

theorem sblen2slen:
  assumes"\<not>chDomEmpty(TYPE('c))"
  shows"\<exists>c. sbLen (sb :: 'c\<^sup>\<Omega>) = #(sb \<^enum> c)"
proof -
  obtain min_c where "\<forall>c2. #((sb :: 'c\<^sup>\<Omega>) \<^enum> min_c) \<le> #(sb \<^enum> c2)" using sb_minstream_exists assms by blast
  then have "sbLen (sb :: 'c\<^sup>\<Omega>) = #(sb \<^enum> min_c)" using sblen2slen_h
    using assms by fastforce
  then show ?thesis
    by auto 
qed

lemma sbconc_chan_len:"#(sb1 \<bullet>\<^sup>\<Omega> sb2  \<^enum>  c) = #(sb1 \<^enum> c)+ #(sb2  \<^enum>  c)"
  by (simp add: sconc_slen2)

lemma sblen_sbconc_eq: assumes "\<And>c.#(sb1 \<^enum> c) = k" shows "(sbLen (sb1 \<bullet>\<^sup>\<Omega> sb2)) = (sbLen sb2) + k"
  apply(cases  "chDomEmpty(TYPE('a))",simp)
  apply (simp add: plus_lnatInf_r)
  apply(subgoal_tac "sbLen sb1 = k")
  apply(rule sblen_rule,simp)
  apply (metis add.commute dual_order.trans sblen_min_len sblen_sbconc)
  apply (metis assms lnat_plus_commu sbconc_chan_len sblen2slen)  
  by(rule sblen_rule,simp_all add: assms)

lemma sblen_sbconc_rule: assumes "\<And>c.#(sb1 \<^enum> c) \<ge> k" shows "(sbLen (sb1 \<bullet>\<^sup>\<Omega> sb2)) \<ge> (sbLen sb2) + k"
  by (metis (full_types) add.commute assms dual_order.trans lessequal_addition order_refl 
      sblen_sbconc sblengeq)

lemma sbelen_one[simp]:
  assumes"\<not>chDomEmpty(TYPE('a))"
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


lemma sbe2slen_1:  assumes"\<not>chDomEmpty(TYPE('a))"
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
"sbIsLeast sb \<equiv> sbLen sb=0  \<or>  chDomEmpty TYPE('cs)"

subsubsection \<open>sbIsLeast lemmas\<close>

lemma botsbleast[simp]:"sbIsLeast \<bottom>"
  apply(simp add: sbIsLeast_def sbLen_def chDom_def)
  apply(case_tac "(\<exists>c::'a. Rep c \<notin> cEmpty)",simp_all)
  apply (metis (mono_tags, lifting) LeastI_ex)
  by (simp add: image_subset_iff) 

lemma sbleast_mono[simp]:"x \<sqsubseteq> y \<Longrightarrow> \<not>sbIsLeast x \<Longrightarrow> \<not> sbIsLeast y"
  apply(simp add: sbIsLeast_def)
  apply(cases "chDomEmpty TYPE('a)",auto)
  using below_bottom_iff sblen_monosimp by fastforce

lemma sbnleast_mex[simp]:"\<not>sbIsLeast x \<Longrightarrow> x \<^enum> c \<noteq> \<epsilon>"
  apply(simp add: sbIsLeast_def)
  by (metis gr_0 less2eq lnle2le lnzero_def sblen_min_len strict_slen)

lemma sbnleast_mexs[simp]:"\<not>sbIsLeast x \<Longrightarrow> \<exists>a s. x \<^enum> c = \<up>a \<bullet> s"
  using sbnleast_mex scases by blast

lemma sbnleast_hdctype[simp]:"\<not>sbIsLeast x \<Longrightarrow> \<forall>c. shd (x \<^enum> c) \<in> ctype (Rep c)"
  apply auto
  apply(subgoal_tac "sValues\<cdot>(x \<^enum> c)\<subseteq> ctype(Rep c) ")
  apply (metis sbnleast_mex sfilter_ne_resup sfilter_sValuesl3)
  by simp



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

lemma abs_sb_eta:
  assumes "sb_well  (\<lambda>c::'cs. f\<cdot>(sb \<^enum> c))"
  and "\<not>chDomEmpty TYPE('cs)"
  shows "(Abs_sb (\<lambda>c::'cs. f\<cdot>(sb  \<^enum>  c))  \<^enum>  c) = f\<cdot>(sb  \<^enum>  c)"
  by (metis Abs_sb_inverse assms(1) mem_Collect_eq sbgetch_insert2)

lemma sbconc_sconc:
  assumes  "sb_well  (\<lambda>c::'cs. f\<cdot>(sb \<^enum> c))"
  and  "sb_well  (\<lambda>c::'cs. g\<cdot>( sb \<^enum> c))"
  and "\<not>chDomEmpty TYPE('cs)"
  shows "Abs_sb (\<lambda>c::'cs. f\<cdot>(sb  \<^enum>  c)) \<bullet>\<^sup>\<Omega> Abs_sb (\<lambda>c::'cs. g\<cdot>(sb  \<^enum>  c)) =
        Abs_sb (\<lambda>c::'cs. f\<cdot>(sb  \<^enum>  c) \<bullet> g\<cdot>(sb  \<^enum>  c))"
  by (simp add: assms abs_sb_eta sbconc_insert)
 
theorem sbcons [simp]: " sbConc (sbHd\<cdot>sb)\<cdot>(sbRt\<cdot>sb) = sb"
  apply(cases "chDomEmpty TYPE('a)")
  apply (metis (full_types) sbtypeepmpty_sbbot)
  apply (simp add: sbtake_insert sbdrop_insert)
  apply (subst sbconc_sconc,simp_all)
  by (simp add: sbgetch_insert2)


subsection\<open>sbHdElem\<close>

subsubsection \<open>sbHdElem definition\<close>

lemma sbhdelem_mono:"monofun
     (\<lambda>sb::'c\<^sup>\<Omega>.
         if chDomEmpty TYPE('c) then Iup (Abs_sbElem None)
         else if sbIsLeast sb then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (sb  \<^enum>\<^sub>\<star>  c)))))"
  apply(rule monofunI)
  apply(cases "chDomEmpty TYPE('c)")
  apply auto
  by (metis below_shd_alt monofun_cfun_arg sbnleast_mex)
 

definition sbHdElem_h::"'c\<^sup>\<Omega> \<Rightarrow> ('c\<^sup>\<surd>) u"where
"sbHdElem_h = (\<lambda> sb. if chDomEmpty TYPE('c) then Iup(Abs_sbElem None) else
        if sbIsLeast sb then \<bottom> else Iup(Abs_sbElem (Some (\<lambda>c. shd((sb) \<^enum> c)))))"

definition sbHdElem::"'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<surd>"where
"sbHdElem = (\<lambda> sb. case (sbHdElem_h sb) of Iup sbElem \<Rightarrow> sbElem | _ \<Rightarrow> undefined)"

subsubsection \<open>sbHdElem abbreviation \<close> (*TODO: better abbreviation lfloor*)

abbreviation sbHdElem_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<surd>" ( "\<lfloor>_" 70) where
"\<lfloor>sb \<equiv> sbHdElem sb"

subsubsection \<open>sbHdElem lemmas\<close>

lemma sbhdelem_none[simp]:"chDomEmpty TYPE('c) \<Longrightarrow> sbHdElem((x::('c)\<^sup>\<Omega>)) = Abs_sbElem(None)"
  by(simp add: sbHdElem_def sbHdElem_h_def)

lemma sbhdelem_some:"sbHdElemWell x \<Longrightarrow> sbHdElem((x::('c)\<^sup>\<Omega>)) = Abs_sbElem(Some(\<lambda>c. shd((x) \<^enum>\<^sub>\<star> c)))"
  apply(simp add: sbHdElem_def sbHdElem_h_def sbHdElemWell_def sbIsLeast_def,auto)
  apply (metis Stream.slen_empty_eq equals0D sblen2slen)
  using cEmpty_def sbgetch_ctype_notempty by fastforce

lemma sbhdelem_mono_empty[simp]:"chDomEmpty TYPE('c) \<Longrightarrow> (x::('c)\<^sup>\<Omega>) \<sqsubseteq> y \<Longrightarrow> sbHdElem x = sbHdElem y"
  by(simp)

lemma sbhdelem_mono_eq[simp]:"sbHdElemWell x \<Longrightarrow>  x \<sqsubseteq> y \<Longrightarrow> sbHdElem x = sbHdElem y"
  apply(cases "chDomEmpty(TYPE('a))")
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


lemma sbtypeempty_sbecons_bot[simp]:"chDomEmpty TYPE ('cs) \<Longrightarrow> (sbe::'cs\<^sup>\<surd>) \<bullet>\<^sup>\<surd> sb = \<bottom>"
  by simp

lemma exchange_bot_sbecons:"chDomEmpty TYPE ('cs) \<Longrightarrow> P(sb) \<Longrightarrow> P( (sbe::'cs\<^sup>\<surd>) \<bullet>\<^sup>\<surd> sb)"
  by (metis (full_types) sbtypeepmpty_sbbot)

lemma sbrt_sbecons: "sbRt\<cdot>(sbe \<bullet>\<^sup>\<surd> sb) = sb"
  apply (cases "chDomEmpty(TYPE('a))", simp)
  apply (simp add: sbDrop.rep_eq)
  apply (simp add: sbECons_def)
  apply (subst sdropl6)
  apply (subgoal_tac "\<And>c. \<exists>m. sbe2sb sbe  \<^enum>  c = \<up>m")
  apply (metis Fin_0 Fin_Suc lnzero_def lscons_conv slen_scons strict_slen sup'_def)
  apply (simp add: sbgetch_insert2 sbe2sb.rep_eq chDom_def)
  apply (metis Diff_eq_empty_iff chDom_def option.simps(5) sbtypenotempty_fex)
  by (simp add: sb_rep_eqI sbgetch_insert2 Rep_sb_inverse)

lemma sbhdelem_h_sbe:" sbHdElem_h (sbe \<bullet>\<^sup>\<surd> sb) = up\<cdot>sbe"
  apply (cases "chDomEmpty(TYPE('a))",simp)
  apply (simp_all add: sbHdElem_def sbHdElem_h_def sbIsLeast_def)+
  apply (simp_all add: up_def)
  apply (metis sbtypeepmpty_sbenone)
  apply (simp add: sbECons_def,auto)
  apply (metis emptyE gr_0 leD lnat_plus_commu lnat_plus_suc lnzero_def sbelen_one sblen_sbconc)
  apply (subgoal_tac "\<forall>c::'a. sbe2sb sbe  \<^enum>  c \<noteq> \<epsilon>")
  apply (simp add: sbgetch_sbe2sb_nempty chDom_def)+
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
  using sbgetch_sbe2sb_nempty by auto

lemma sbhdelem_sbecons: "sbHdElem (sbe  \<bullet>\<^sup>\<surd> sb) = sbe"
  by(simp add: sbHdElem_def sbhdelem_h_sbe up_def)

lemma sbecons_len:
  shows "sbLen (sbe \<bullet>\<^sup>\<surd> sb) = lnsuc\<cdot>(sbLen sb)"
  apply(cases "chDomEmpty(TYPE('a))")
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

lemma sbHdElem:"sbLen (sb::'cs\<^sup>\<Omega>) \<noteq> (0::lnat) \<Longrightarrow> sbe2sb (sbHdElem sb) = sbHd\<cdot>sb"
  apply (case_tac "chDomEmpty (TYPE ('cs))")
  apply (metis (full_types) sbtypeepmpty_sbbot)
  apply (rule sb_rep_eqI)
  apply (simp add: sbHdElem_def sbHdElem_h_def)
  apply rule+
  apply (simp add: sbIsLeast_def)
  by (simp add:sbtake_insert stake2shd sbe2sb.abs_eq sbe2sb.rep_eq Abs_sbElem_inverse Abs_sb_inverse 
      sb_well_def)

(*sb_ind*)

lemma sbtake_chain:"chain (\<lambda>i::nat. sbTake i\<cdot>x)"
  apply (rule chainI)
  apply(simp add: below_sb_def)
  apply(rule fun_belowI)
  apply(simp add: sbtake_insert)
  by (metis (no_types) Suc_leD le_refl sbgetch_insert2 sbmap_stake_eq stake_mono)

lemma sblen_sbtake:" \<not>chDomEmpty TYPE ('c) \<Longrightarrow> sbLen (sbTake n\<cdot>(x :: 'c\<^sup>\<Omega>)) \<le> Fin (n)"
proof- 
assume a0:"\<not>chDomEmpty TYPE ('c)"
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

lemma sbECons_sbLen:"sbLen (sb::'cs\<^sup>\<Omega>) \<noteq> (0::lnat) \<Longrightarrow> \<not> chDomEmpty TYPE('cs) \<Longrightarrow> \<exists> sbe sb'. sb = sbe \<bullet>\<^sup>\<surd> sb'"
  by (metis sbECons_def sbHdElem sbcons)

lemma sb_cases [case_names least sbeCons, cases type: sb]: 
  "(sbIsLeast (sb'::'cs\<^sup>\<Omega>) \<Longrightarrow> P) 
  \<Longrightarrow> (\<And>sbe sb. sb' = sbECons sbe\<cdot>sb \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) \<Longrightarrow> P) 
  \<Longrightarrow> P"
  by (meson sbECons_sbLen sbIsLeast_def)

lemma sb_finind1:
    fixes x::"'cs\<^sup>\<Omega>"
    shows "sbLen x = Fin k\<Longrightarrow> (\<And>sb. sbIsLeast sb \<Longrightarrow> P sb) \<Longrightarrow> (\<And>sbe sb. P sb 
          \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb))
    \<Longrightarrow>P x"
  apply(induction k  arbitrary:x)
  apply (simp add: sbIsLeast_def)
  by (metis Fin_Suc inject_lnsuc sb_cases sbecons_len)

lemma sb_finind:
    fixes x::"'cs\<^sup>\<Omega>"
  assumes "sbLen x < \<infinity>"
      and "\<And>sb. sbIsLeast sb \<Longrightarrow> P sb"
      and "\<And>sbe sb. P sb \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb)"
    shows "P x"
  by (metis assms(1) assms(2) assms(3) lnat_well_h2 sb_finind1)

lemma sbtakeind1: 
  fixes x::"'cs\<^sup>\<Omega>"
  shows "\<forall>x. (( \<forall>(sb::'cs\<^sup>\<Omega>) . sbIsLeast sb \<longrightarrow> P sb) \<and> 
        (\<forall> (sbe::'cs\<^sup>\<surd>) sb::'cs\<^sup>\<Omega>. P sb  \<longrightarrow> \<not>chDomEmpty TYPE ('cs) \<longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb))) \<and> 
        ( \<not>chDomEmpty TYPE ('cs) \<longrightarrow> sbLen x \<le> Fin n) \<longrightarrow> P (x)"
  by (metis (no_types, lifting) inf_ub less2eq order.not_eq_order_implies_strict sb_cases sb_finind sb_finind1)

lemma sbtakeind: 
  fixes x::"'cs\<^sup>\<Omega>"
  shows "\<forall>x. (( \<forall>(sb::'cs\<^sup>\<Omega>) . sbIsLeast sb \<longrightarrow> P sb) \<and> 
         (\<forall> (sbe::'cs\<^sup>\<surd>) sb::'cs\<^sup>\<Omega>. P sb  \<longrightarrow> \<not>chDomEmpty TYPE ('cs) \<longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb))) 
          \<longrightarrow> P (sbTake  n\<cdot>x)"
  apply rule+
  apply(subst sbtakeind1, simp_all) 
  using sblen_sbtake sbtakeind1 by auto

lemma sb_ind[case_names adm least sbeCons, induct type: sb]:
    fixes x::"'cs\<^sup>\<Omega>"
  assumes "adm P" 
      and "\<And>sb. sbIsLeast sb \<Longrightarrow> P sb"
      and "\<And>sbe sb. P sb  \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb)"   
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

lemma sbconvert_getch [simp]: "sb \<star> \<^enum> c = sb \<^enum>\<^sub>\<star> c"
  by (simp add: sbgetch_insert2)


subsection \<open>sbUnion\<close>

subsubsection\<open>sbUnion definition\<close>

definition sbUnion::"'c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega> \<rightarrow> 'e\<^sup>\<Omega>" where
"sbUnion = (\<Lambda> sb1 sb2. Abs_sb (\<lambda> c. if (Rep c \<in> chDom TYPE('c)) then 
                  sb1 \<^enum>\<^sub>\<star> c else  sb2\<^enum>\<^sub>\<star> c))"

lemma sbunion_sbwell[simp]: "sb_well ((\<lambda> (c::'e). if (Rep c \<in> chDom TYPE('c)) then 
                  (sb1::'c\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c else  (sb2::'d\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c))"
  apply(rule sbwellI)
  by simp

lemma sbunion_insert:"sbUnion\<cdot>(sb1::'c\<^sup>\<Omega>)\<cdot>sb2 = Abs_sb (\<lambda> c. if (Rep c \<in> chDom TYPE('c)) then 
                  sb1 \<^enum>\<^sub>\<star> c else  sb2 \<^enum>\<^sub>\<star> c)"
  unfolding sbUnion_def
  apply(subst beta_cfun, intro cont2cont, simp)+
  ..
(* TODO: sbunion_rep_eq 
  Namin_convention: "insert" = Abs_cfun weg
                      rep_eq = Abs_XXX weg *)

lemma sbunion_rep_eq:"Rep_sb (sbUnion\<cdot>(sb1::'c\<^sup>\<Omega>)\<cdot>sb2) = (\<lambda> c. if (Rep c \<in> chDom TYPE('c)) then 
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
      assumes"Rep c \<in> chDom TYPE('c)"
      shows  "(sbUnion::'a\<^sup>\<Omega>\<rightarrow> 'b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>)\<cdot>cb\<cdot>db \<^enum>\<^sub>\<star> c = cb \<^enum> c"
  apply(simp add: sbgetch_insert sbunion_rep_eq)
  by (metis assms Diff_iff chDom_def chan_eq range_eqI sbgetch_insert sbgetch_insert2)

lemma sbunion_eq [simp]: "sb1 \<uplus>\<^sub>\<star> sb2 = sb1"
  apply(rule sb_eqI)
  by simp


lemma sbunion_sbconvert_eq[simp]:"cb \<uplus>\<^sub>\<star> cb = (cb\<star>)"
  by(simp add: sbunion_insert sbconvert_insert)

lemma ubunion_commu:
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
    assumes "chDom (TYPE ('cs1)) \<inter> chDom (TYPE ('cs2)) = {}"
    shows "sb1 \<uplus>\<^sub>\<star> sb2 = ((sb2 \<uplus>\<^sub>\<star> sb1)::'cs3\<^sup>\<Omega>)"
  apply(rule sb_eqI)
  apply(rename_tac c)
  apply(case_tac "Rep c \<in> chDom (TYPE ('cs1))"; case_tac "Rep c \<in> chDom (TYPE ('cs2))"; case_tac "Rep c \<in> chDom (TYPE ('cs3))")
  using assms  by(auto simp add: sbGetCh.rep_eq sbunion_rep_eq)

lemma ubunion_fst[simp]:
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "chDom (TYPE ('cs2)) \<inter> chDom (TYPE ('cs3)) = {}"
  shows "sb1 \<uplus>\<^sub>\<star> sb2 = (sb1\<star> :: 'cs3\<^sup>\<Omega>)"
  apply(rule sb_eqI)  (* Exakt gleicher beweis wie "ubunion_commu" ... *)
  apply(rename_tac c)
  apply(case_tac "Rep c \<in> chDom (TYPE ('cs1))"; case_tac "Rep c \<in> chDom (TYPE ('cs2))"; case_tac "Rep c \<in> chDom (TYPE ('cs3))")
  apply(case_tac "Rep c \<in> chDom (TYPE ('cs1))"; case_tac "Rep c \<in> chDom (TYPE ('cs2))"; case_tac "Rep c \<in> chDom (TYPE ('cs3))")
  using assms  by(auto simp add: sbGetCh.rep_eq sbunion_rep_eq)

lemma ubunion_id[simp]: "out\<star>\<^sub>1 \<uplus> (out\<star>\<^sub>2) = out"
proof(rule sb_eqI)
  fix c::"'a \<union> 'b"
  assume as:"Rep c \<in> chDom TYPE('a \<union> 'b)"
  have "Rep c \<in> chDom (TYPE ('a)) \<Longrightarrow> out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c"
    by (metis sbgetch_insert2 sbunion_getch sbunion_rep_eq sbunion_sbconvert_eq)
  moreover have "Rep c \<in> chDom (TYPE ('b)) \<Longrightarrow> out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c"
    by (metis sbgetch_insert2 sbunion_getch sbunion_rep_eq sbunion_sbconvert_eq)
  moreover have "(Rep c \<in> chDom (TYPE ('a))) \<or> (Rep c \<in> chDom (TYPE ('b)))"
    using as chdom_in by fastforce
  ultimately show  "out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c" by fastforce
qed


lemma sbunion_getchl[simp]:
    fixes sb1 ::"'cs1\<^sup>\<Omega>"
      and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<in> chDom TYPE('cs1)"
    shows "(sb1 \<uplus> sb2) \<^enum>\<^sub>\<star> c = sb1 \<^enum>\<^sub>\<star> c"
  apply(auto simp add: sbgetch_insert sbunion_rep_eq assms)
  apply (metis Rep_union_def UnI1 assms equals0D f_inv_into_f union_range_union)
  apply (metis Rep_union_def UnCI assms f_inv_into_f union_range_union)
  apply (metis Rep_union_def UnCI assms chan_eq union_range_union)
  by (metis Rep_union_def Un_iff assms chan_eq empty_iff union_range_union)

lemma sbunion_getchr[simp]:
    fixes sb1 ::"'cs1\<^sup>\<Omega>"
      and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<notin> chDom TYPE('cs1)"
  shows "(sb1 \<uplus> sb2) \<^enum>\<^sub>\<star> c = sb2 \<^enum>\<^sub>\<star> c"
  apply(auto simp add: sbgetch_insert sbunion_rep_eq assms)
  apply (metis Rep_union_def UnCI assms f_inv_into_f union_range_union)
  apply (metis Rep_union_def UnCI chan_eq union_range_union)
   apply (metis Rep_union_def UnCI f_inv_into_f union_range_union)
  by (metis Rep_union_def Un_iff chan_eq empty_iff union_range_union)

lemma sbunion_getch_nomag [simp]: "sb1 \<uplus>\<^sub>\<star> sb2  \<^enum>  c = (sb1 \<uplus> sb2) \<^enum>\<^sub>\<star> c"
  by(auto simp add: sbgetch_insert2 sbunion_rep_eq)

lemma sbunion_magic: 
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
  shows "(sb1 \<uplus> sb2)\<star> = sb1 \<uplus>\<^sub>\<star> sb2"
  apply(rule sb_eqI)
  by auto

lemma sbunion_fst[simp]: "(sb1 \<uplus> sb2)\<star>\<^sub>1 = sb1"
  by (simp add: sbunion_magic)

lemma sbunion_snd[simp]:
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "chDom (TYPE ('cs1)) \<inter> chDom (TYPE ('cs2)) = {}"
  shows "(sb1 \<uplus> sb2)\<star>\<^sub>2 = sb2"
  by (metis assms sbconv_eq sbunion_magic ubunion_commu ubunion_fst)

lemma sbunion_eqI:
  assumes "sb1 = (sb\<star>\<^sub>1)"
    and "sb2 = (sb\<star>\<^sub>2)"
  shows "sb1 \<uplus> sb2 = sb"
  by (simp add: assms)

(*<*)
end
(*>*)
