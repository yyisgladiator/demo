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

paragraph \<open>SB Type Properties \\\<close>

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

abbreviation sbIsLeast::"'cs\<^sup>\<Omega> \<Rightarrow> bool" where
"sbIsLeast sb \<equiv> \<not>sbHdElemWell sb"

text\<open>The negation of this property is called @{const sbIsLeast}, 
because these \Gls{sb} do not contain any complete slices.\<close>

paragraph \<open>sbGetCh Properties \\\<close>

text\<open>When using the intuitively variant of @{const sbGetCh}, it
obtains a stream from a channel. It should never be able to do
anything else. This behavior is verified by the following theorem.
Obtaining a stream from its \gls{sb} is the same as obtaining the 
output from the function realizing the \gls{sb}.\<close>

theorem sbgetch_insert2:"sb \<^enum> c = (Rep_sb sb) c"
  apply(simp add: sbgetch_insert)
  by (metis (full_types)Rep_sb_strict app_strict cnotempty_cdom 
      sbtypeepmpty_sbbot)

lemma sbgetch_empty: fixes sb::"'cs\<^sup>\<Omega>"
    assumes "Rep c \<notin> chDom TYPE('cs)"
    shows "sb \<^enum>\<^sub>\<star> c = \<epsilon>"
  by(simp add: sbgetch_insert assms)

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

lemma sbgetch_ctype_notempty:"sb  \<^enum>\<^sub>\<star>  c \<noteq> \<epsilon> \<Longrightarrow> ctype (Rep c) \<noteq> {}"
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
though the relation of their respective streams. In both cases we 
only have to check channels from the domain, hence the properties 
automatically hold for \Gls{sb} with an empty domain.\<close>

theorem sb_belowI:
  fixes sb1 sb2::"'cs\<^sup>\<Omega>"
    assumes "\<And> c. Rep c\<in>chDom TYPE('cs) \<Longrightarrow>  sb1 \<^enum> c \<sqsubseteq> sb2 \<^enum> c"
    shows "sb1 \<sqsubseteq> sb2"
  apply(subst below_sb_def)
  apply(rule fun_belowI)
  by (metis (full_types) assms  po_eq_conv sbGetCh.rep_eq 
      sbgetch_insert2)

text\<open>If all respectively chosen streams of one bundle are 
@{const below} the streams of another bundle, the @{const below}
relation holds for the bundles as well.\<close>

theorem sb_eqI:
  fixes sb1 sb2::"'cs\<^sup>\<Omega>"
    assumes "\<And>c. Rep c\<in>chDom TYPE('cs) \<Longrightarrow>sb1 \<^enum> c = sb2 \<^enum> c"
    shows "sb1 = sb2"
  apply(cases "chDom TYPE('cs) \<noteq> {}")
  apply(metis Diff_eq_empty_iff Diff_triv assms chDom_def 
        chan_botsingle rangeI sb_rep_eqI sbgetch_insert2)
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

lemma botsbleast[simp]:"sbIsLeast \<bottom>"
  by(simp add: sbHdElemWell_def)

lemma sbleast_mono[simp]:"x \<sqsubseteq> y \<Longrightarrow> \<not>sbIsLeast x \<Longrightarrow> \<not> sbIsLeast y"
  by simp

lemma sbnleast_mex:"\<not>sbIsLeast x \<Longrightarrow> x \<^enum> c \<noteq> \<epsilon>"
  by(simp add: sbHdElemWell_def)

lemma sbnleast_mexs[simp]:"\<not>sbIsLeast x \<Longrightarrow> \<exists>a s. x \<^enum> c = \<up>a \<bullet> s"
  using sbnleast_mex scases by blast

lemma sbnleast_hdctype[simp]:
"\<not>sbIsLeast x \<Longrightarrow> \<forall>c. shd (x \<^enum> c) \<in> ctype (Rep c)"
  apply auto
  apply(subgoal_tac "sValues\<cdot>(x \<^enum> c)\<subseteq> ctype(Rep c) ")
  apply (metis sbnleast_mex sfilter_ne_resup sfilter_sValuesl3)
  by simp

lemma sbgetchid[simp]:"Abs_sb (( \<^enum> ) (x)) = x"
  by(simp add: sbgetch_insert2)

subsubsection \<open>Concatination \label{subsub:sbconc}\<close>

text\<open>Concatenating two \Gls{sb} is equivalent to concatenating their 
streams whilst minding the channels. The output is also a \gls{sb},
because the values of both streams are in @{const ctype}, therefore,
the same holds for the union.\<close>

lemma sbconc_well[simp]:"sb_well (\<lambda>c. (sb1 \<^enum> c) \<bullet> (sb2 \<^enum> c))"
  apply(rule sbwellI)
  by (metis (no_types, hide_lams) Un_subset_iff dual_order.trans 
      sbgetch_ctypewell sconc_sValues)

lift_definition sbConc:: "'c\<^sup>\<Omega>  \<Rightarrow>  'c\<^sup>\<Omega> \<rightarrow>  'c\<^sup>\<Omega>" is
"\<lambda> sb1 sb2. Abs_sb(\<lambda>c. (sb1 \<^enum> c )\<bullet>(sb2 \<^enum> c))"
  by(intro cont2cont, simp)

lemmas sbconc_insert = sbConc.rep_eq

text\<open> For easier usability, we introduce a concatenation 
abbreviation.\<close>

abbreviation sbConc_abbr :: "'c\<^sup>\<Omega>  \<Rightarrow>  'c\<^sup>\<Omega> \<Rightarrow>  'c\<^sup>\<Omega>"
(infixr "\<bullet>\<^sup>\<Omega>" 70) where "sb1 \<bullet>\<^sup>\<Omega> sb2 \<equiv> sbConc sb1\<cdot>sb2"

text\<open>After concatenating two \Gls{sb}, the resulting \gls{sb} has to
contain the streams from both \Gls{sb} in the correct order. Hence,
obtaining a stream by its channel from the concatenation of two 
\Gls{sb} is equivalent to obtaining the stream by the same channel
from the input \Gls{sb} and then concatenating the streams from the
first input bundle with the stream from the second input bundle.\<close>

theorem sbconc_getch [simp]: "sb1 \<bullet>\<^sup>\<Omega> sb2  \<^enum> c = (sb1 \<^enum> c) \<bullet> sb2 \<^enum> c"
  unfolding sbgetch_insert2 sbconc_insert
  apply(subst Abs_sb_inverse)
  apply simp
  apply(rule sbwellI)
  apply (metis (no_types, hide_lams) Un_subset_iff dual_order.trans
         sbgetch_ctypewell sbgetch_insert2 sconc_sValues)
  ..

text\<open>It follows, that concatenating a \gls{sb} with the \<open>\<bottom>\<close> bundle
in any order, results in the same \gls{sb}.\<close>

theorem sbconc_bot_r[simp]:"sb \<bullet>\<^sup>\<Omega> \<bottom> = sb"
  by(rule sb_eqI, simp)

theorem sbconc_bot_l[simp]:"\<bottom> \<bullet>\<^sup>\<Omega> sb = sb"
  by(rule sb_eqI, simp)

subsubsection \<open>Length of SBs \lable{subsub:sblen}\<close>

text\<open>The length of a \gls{sb} can be interpreted differently. Since
we will use the length of bundles to define causal \Gls{spf} and an
induction rule for \Gls{sb}, we have to define the length as
follows:
  \<^item> A \gls{sb} with an empty domain is infinitely long
  \<^item> A \gls{sb} with an non-empty domain is as long as its shortest 
    stream


Therefore, the length of a \gls{sb} with a non empty domain is also 
equal to the number of complete slices it consists of.\<close>

definition sbLen::"'c\<^sup>\<Omega> \<Rightarrow> lnat"where
"sbLen sb \<equiv> if (chDomEmpty TYPE('c)) 
                then \<infinity> 
                else LEAST n . n\<in>{#(sb \<^enum> c) | c. True}"

text\<open>Our @{const sbLen} function works exactly as described. It 
returns \<open>\<infinity>\<close>, if the domain is empty. Else it chooses the minimal 
length of all the bundles streams.\<close>

paragraph \<open>SB Length Properties \\\<close>

text\<open>Now we verify the behavior. First we show, that all \gls{sb} 
with an empty domain are infinitely long.\<close>

theorem sblen_empty[simp]:
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
  apply (metis (mono_tags, lifting) Least_le assms(2) 
         dual_order.trans)
  using assms(1) by simp

lemma sblengeq: assumes "\<And>c::'c. k\<le> #(sb\<^enum>c)"
  shows "k \<le> sbLen sb" 
  apply(cases  "chDomEmpty(TYPE('c))",simp add: assms)
  apply(simp add: sbLen_def)
  using LeastI2_wellorder_ex inf_ub insert_iff mem_Collect_eq 
        sbLen_def assms by smt

text\<open>Furthermore, the length of two concatenated bundles is greater 
or equal to the added length of both bundles. If both bundles have a
minimal stream on the same channel, the resulting length would be 
equal.\<close>

theorem sblen_sbconc:"sbLen sb1 + sbLen sb2 \<le> sbLen (sb1 \<bullet>\<^sup>\<Omega> sb2)"
  apply(cases  "chDomEmpty(TYPE('a))",simp)
  apply(rule sblengeq)
  by (metis lessequal_addition sbconc_getch sblen_min_len 
      sconc_slen2)

lemma sblen_mono:"monofun sbLen"
  apply(rule monofunI,simp)
  apply(cases "chDomEmpty TYPE('a)",simp)
  apply(rule sblengeq)
  apply(rule sblenleq)
  using sbgetch_below_slen by auto

lemma sblen_monosimp[simp]:"x \<sqsubseteq> y \<Longrightarrow> sbLen x \<le> sbLen y"
  using lnle_conv monofunE sblen_mono by blast

text\<open>This rule captures all necessary assumptions to obtain the 
exact length of a \gls{sb} with a non-empty domain:
  \<^item> All streams must be at least equally long to the length of the 
    \gls{sb}
  \<^item> There exists a stream with length equal to the length of the 
    \gls{sb}\<close>

theorem sblen_rule:
  assumes "\<not>chDomEmpty(TYPE('a))" 
  and "\<And>c. k \<le> #(sb \<^enum> (c::'a))"
  and "\<exists>c. #(sb \<^enum> (c :: 'a )) = k"
  shows" sbLen sb = k"
  by (metis assms(1) assms(2) assms(3) dual_order.antisym 
      sblen_min_len sblengeq)

text\<open>If two \Gls{sb} are in an order and also infinitely long, there
have to be equal. This holds because either the domain is empty or
every stream of the bundles is infinitely long.\<close>

theorem sblen_sbeqI:"x \<sqsubseteq> y \<Longrightarrow> sbLen x = \<infinity> \<Longrightarrow> x = y"
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
    using as2 box_below lnle_def sblen_mono chY is_ub_thelub 
    lnle_def monofun_def by blast
qed

lemma sblen2slen_h:
  fixes "c1"
  assumes"\<not>chDomEmpty(TYPE('c))"
  and "\<forall>c2. #((sb :: 'c\<^sup>\<Omega>) \<^enum> c1) \<le> #(sb \<^enum> c2)"
  shows "#((sb :: 'c\<^sup>\<Omega>) \<^enum> c1) = sbLen sb"
  apply(simp add: sbLen_def)
  apply(subst Least_equality)
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
        using ff1 by (metis less_le_not_le ln_less 
                Orderings.linorder_class.linear lnle2le sblengeq) }
    then have "\<exists>c. #(sb \<^enum> c) \<le> #(sb \<^enum> cc c)"
      by meson }
  then show ?thesis
    by metis
qed

text\<open>We can also show, that the length of any \gls{sb} that has a 
not empty domain, is equal to the length of one of its streams.\<close>

theorem sblen2slen:
  assumes"\<not>chDomEmpty(TYPE('c))"
  shows"\<exists>c. sbLen (sb :: 'c\<^sup>\<Omega>) = #(sb \<^enum> c)"
proof -
  obtain min_c where "\<forall>c2. #((sb :: 'c\<^sup>\<Omega>) \<^enum> min_c) \<le> #(sb \<^enum> c2)"
    using sb_minstream_exists assms by blast
  then have "sbLen (sb :: 'c\<^sup>\<Omega>) = #(sb \<^enum> min_c)" using sblen2slen_h
    using assms by fastforce
  then show ?thesis
    by auto 
qed

lemma sbconc_chan_len:"#(sb1 \<bullet>\<^sup>\<Omega> sb2 \<^enum> c) = #(sb1 \<^enum> c)+ #(sb2 \<^enum> c)"
  by (simp add: sconc_slen2)

lemma sblen_sbconc_eq: 
  assumes "\<And>c.#(sb1 \<^enum> c) = k" 
  shows "(sbLen (sb1 \<bullet>\<^sup>\<Omega> sb2)) = (sbLen sb2) + k"
  apply(cases  "chDomEmpty(TYPE('a))",simp)
  apply (simp add: plus_lnatInf_r)
  apply(subgoal_tac "sbLen sb1 = k")
  apply(rule sblen_rule,simp)
  apply (metis add.commute dual_order.trans sblen_min_len 
        sblen_sbconc)
  apply (metis assms lnat_plus_commu sbconc_chan_len sblen2slen)  
  by(rule sblen_rule,simp_all add: assms)

lemma sblen_sbconc_rule: 
  assumes "\<And>c.#(sb1 \<^enum> c) \<ge> k" 
  shows "(sbLen (sb1 \<bullet>\<^sup>\<Omega> sb2)) \<ge> (sbLen sb2) + k"
  by (metis (full_types) add.commute assms dual_order.trans 
      lessequal_addition order_refl sblen_sbconc sblengeq)

text\<open>The length of a @{type sbElem} is 1, if the domain is not 
empty, else it is \<open>\<infinity>\<close>.\<close>

theorem sbelen_one[simp]:
  assumes"\<not>chDomEmpty(TYPE('a))"
  shows " sbLen (sbe2sb (sbe::'a\<^sup>\<surd>)) = 1"
proof-
  have "\<And>c. #(sbe2sb (sbe::'a\<^sup>\<surd>) \<^enum> (c :: 'a )) = 1"
    apply(simp add: sbe2sb_def)
    apply(subgoal_tac "Rep_sbElem sbe \<noteq> None")
    apply auto
    apply(simp add: sbgetch_insert2)
    apply(subst Abs_sb_inverse,auto)
    apply (metis (full_types) option.simps(5) sbe2sb.rep_eq 
          sbwell2fwell)
    apply (simp add: one_lnat_def)
    by(simp add: assms)
  then show ?thesis
    apply(subst sblen_rule)
    by(simp_all add: assms)
qed

theorem sbelen_inf[simp]:
  assumes"chDomEmpty(TYPE('a))"
  shows " sbLen (sbe2sb (sbe::'a\<^sup>\<surd>)) = \<infinity>"
  by (simp add: assms)

lemma sbe2slen_1:  assumes"\<not>chDomEmpty(TYPE('a))"
  shows  "\<And>c::'a. #(sbe2sb sbe  \<^enum>  c) = (1::lnat)"
    apply(simp add: sbe2sb_def)
    apply(subgoal_tac "Rep_sbElem sbe \<noteq> None")
    apply auto
    apply(simp add: sbgetch_insert2)
    apply(subst Abs_sb_inverse,auto)
    apply (metis (full_types) option.simps(5) sbe2sb.rep_eq 
           sbwell2fwell)
    apply (simp add: one_lnat_def)
    by(simp add: assms)
 
lemma sbnleast_len[simp]:"\<not>sbIsLeast x \<Longrightarrow> sbLen x \<noteq> 0"
  apply(rule ccontr,auto)
  apply(simp add: sbHdElemWell_def)
  apply(cases "chDomEmpty TYPE('a)",simp)
  by (metis Stream.slen_empty_eq sblen2slen)


lemma sbnleast_dom[simp]:
  "\<not>sbIsLeast (x::'cs\<^sup>\<Omega>) \<Longrightarrow> \<not>chDomEmpty TYPE('cs)"
  using sbhdelemnotempty by blast

lemma sbleast2sblenempty[simp]:
"sbIsLeast (x::'cs\<^sup>\<Omega>) \<Longrightarrow> chDomEmpty TYPE('cs) \<or> sbLen x = 0"
  apply(simp add: sbLen_def sbHdElemWell_def,auto)
  by (metis (mono_tags, lifting) LeastI_ex Least_le gr_0 leD lnle2le
      neqE strict_slen) 

subsubsection \<open>Dropping SB Elements \label{subsub:sbdrop}\<close>

text\<open>Through dropping a number of \gls{sb} elements, it is possible
to access any element in the \gls{sb} or to get a later part.
Dropping the first \<open>n\<close> Elements of a \gls{sb} means dropping the 
first \<open>n\<close> elements of every stream in the \gls{sb}.\<close>  

lemma sbdrop_well[simp]:"sb_well (\<lambda>c. sdrop n\<cdot>(b \<^enum>\<^sub>\<star> c))"
  apply(rule sbwellI)
  by (meson dual_order.trans sbgetch_ctypewell sdrop_sValues)

lift_definition sbDrop::"nat \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"is
"\<lambda> n sb. Abs_sb (\<lambda>c. sdrop n\<cdot>(sb \<^enum> c))"
  apply(intro cont2cont)
  by(simp add: sValues_def)

lemmas sbdrop_insert = sbDrop.rep_eq

text\<open>A special case of @{const sbDrop} is to drop only the first
element of the \gls{sb}. It is the rest operator on \Gls{sb}.\<close>

abbreviation sbRt :: "'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"  where 
"sbRt \<equiv> sbDrop 1"

lemma sbdrop_bot[simp]:"sbDrop n\<cdot>\<bottom> = \<bottom>"
  apply(simp add: sbdrop_insert)
  by (simp add: bot_sb)

lemma sbdrop_eq[simp]:"sbDrop 0\<cdot>sb = sb"
  by(simp add: sbdrop_insert sbgetch_insert2)
 
subsubsection \<open>Taking SB Elements \label{subsub:sbtake}\<close>

text\<open>Through taking the first \<open>n\<close> elements of a \gls{sb}, it is
possible to reduce any \gls{sb} to a finite part of itself. The 
output is always @{const below} the input.\<close>  

lemma sbtake_well[simp]:"sb_well (\<lambda>c. stake n\<cdot>(sb  \<^enum>\<^sub>\<star>  c))"
  by(simp add: sbmap_well)

lift_definition sbTake::"nat \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow>  'c\<^sup>\<Omega>"is
"\<lambda> n sb. Abs_sb (\<lambda>c. stake n\<cdot>(sb \<^enum> c))"
  by(intro cont2cont, simp)

lemmas sbtake_insert = sbTake.rep_eq

text\<open>A special case of @{const sbTake} is to take only the first
element of the \gls{sb}. It is the head operator on \Gls{sb}.\<close>

abbreviation sbHd :: "'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>"  where 
"sbHd \<equiv> sbTake 1"

paragraph \<open>sbTake Properties \\\<close>

text\<open>Obtaining some stream form a \gls{sb} after applying 
@{const sbTake}, is the same as applying  @{const stake} after
obtaining the stream from the \gls{sb}.\<close>

theorem sbtake_getch[simp]:"sbTake n\<cdot>sb \<^enum> c = stake n\<cdot>(sb \<^enum> c)"
  apply(simp add: sbgetch_insert sbTake.rep_eq)
  apply(subst Abs_sb_inverse,auto simp add: sb_well_def)
  by (metis sValues_sconc sbgetch_ctypewell sbgetch_insert2 
      split_streaml1 subsetD)

text\<open>The output of @{const sbTake} is always @{const below} the
input.\<close>

theorem sbtake_below[simp]: "sbTake i\<cdot>sb \<sqsubseteq> sb"
  by (simp add: sb_belowI)

lemma sbtake_idem[simp]:
  assumes "n \<ge> i"
  shows"sbTake n\<cdot>(sbTake i\<cdot>sb) = (sbTake i\<cdot>sb)"
  by (simp add: sb_eqI assms min_absorb2)

lemma sbmap_stake_eq:"
  Abs_sb (\<lambda>c::'a. stake n\<cdot>(sb \<^enum> c)) \<^enum> c = stake n\<cdot>(sb \<^enum> c)"
  apply(simp add: sbgetch_insert2)
  apply(subst Abs_sb_inverse)
  apply simp
  apply(rule sbwellI)
  apply (metis sbgetch_insert2 sbgetch_ctypewell dual_order.trans 
         sValues_sconc split_streaml1)
  by simp

lemma sbtake_max_len [simp]:"#(sbTake n\<cdot>sb  \<^enum>  c) \<le> Fin n"
  by simp

lemma abs_sb_eta:
  assumes "sb_well  (\<lambda>c::'cs. f\<cdot>(sb \<^enum> c))"
  and "\<not>chDomEmpty TYPE('cs)"
  shows "(Abs_sb (\<lambda>c::'cs. f\<cdot>(sb  \<^enum>  c))  \<^enum>  c) = f\<cdot>(sb  \<^enum>  c)"
  by (metis Abs_sb_inverse assms(1) mem_Collect_eq sbgetch_insert2)

lemma sbconc_sconc:
  assumes  "sb_well  (\<lambda>c::'cs. f\<cdot>(sb \<^enum> c))"
  and  "sb_well  (\<lambda>c. g\<cdot>( sb \<^enum> c))"
  and "\<not>chDomEmpty TYPE('cs)"
  shows "Abs_sb (\<lambda>c. f\<cdot>(sb  \<^enum>  c)) \<bullet>\<^sup>\<Omega> Abs_sb (\<lambda>c. g\<cdot>(sb  \<^enum>  c)) =
        Abs_sb (\<lambda>c. f\<cdot>(sb  \<^enum>  c) \<bullet> g\<cdot>(sb  \<^enum>  c))"
  by (simp add: assms abs_sb_eta sbconc_insert)

text\<open>Concatenating the head of a \gls{sb} to the rest of a \gls{sb}
results in the \gls{sb} itself.\<close>

theorem sbcons [simp]:"sbConc (sbHd\<cdot>sb)\<cdot>(sbRt\<cdot>sb) = sb"
  apply(cases "chDomEmpty TYPE('a)")
  apply (metis (full_types) sbtypeepmpty_sbbot)
  apply (simp add: sbtake_insert sbdrop_insert)
  by (subst sbconc_sconc,simp_all)
  
lemma sbtake_len:
  assumes "\<not>chDomEmpty TYPE('b)"
    and "Fin i \<le> sbLen (sb::'b\<^sup>\<Omega>)"
  shows "sbLen (sbTake i\<cdot>sb) = Fin i"
  using assms
  apply (induction i)
  apply (simp add: sbLen_def)
  apply (metis (mono_tags, lifting) LeastI)
  by (metis (no_types, hide_lams) assms(1) order_trans sblen2slen 
      sbtake_getch slen_stake sblen_min_len)

subsubsection \<open>Converter from SB to sbElem \label{subsub:sbhdelem}\<close>

text\<open>Converting a \gls{sb} to a @{type sbElem} is rather complex. 
The main goal is to obtain the first slice of a \gls{sb} as a 
@{type sbElem}. This is not possible, if there is an empty stream in
the bundle domain, hence: 
  \<^item> if the domain is empty, the head element is @{const None}
  \<^item> if the domain is non-empty and contains no empty stream, the 
    head element is some function that maps to the head of the 
    corresponding bundle streams
  \<^item> if the domain is non-empty and contains an empty stream, the 
    head element is undefined


For defining the sbHdElem function we use a helper that has no 
undefined output. Instead we lift it the output to an discrete
\gls{pcpo}. In the later part we will also show its continuity for 
finite bundles.\<close>

lemma sbhdelem_mono:
"monofun (\<lambda>sb::'c\<^sup>\<Omega>. 
          if chDomEmpty TYPE('c) 
             then Iup (Abs_sbElem None)
             else if sbIsLeast sb 
                     then \<bottom> 
                     else Iup (Abs_sbElem 
                          (Some (\<lambda>c::'c. shd (sb  \<^enum>\<^sub>\<star>  c)))))"
  apply(rule monofunI)
  apply(cases "chDomEmpty TYPE('c)")
  apply auto
  by (metis below_shd_alt monofun_cfun_arg sbnleast_mex)
 

definition sbHdElem_h::"'c\<^sup>\<Omega> \<Rightarrow> ('c\<^sup>\<surd>) u"where
"sbHdElem_h = 
(\<lambda> sb. if chDomEmpty TYPE('c) 
          then Iup(Abs_sbElem None) 
          else if sbIsLeast sb 
                  then \<bottom> 
                  else Iup(Abs_sbElem (Some (\<lambda>c. shd((sb) \<^enum> c)))))"

definition sbHdElem::"'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<surd>"where
"sbHdElem = (\<lambda> sb. case (sbHdElem_h sb) of 
                   Iup sbElem \<Rightarrow> sbElem | 
                   _          \<Rightarrow> undefined)"


text\<open> The @{const sbHdElem} function checks if the output of
@{const sbHdElem_h} is a @{type sbElem}. And then returns it. If the
helper returns \<open>\<bottom>\<close> our converter maps to \<open>undefined\<close> as mentioned 
above.\<close>
(*<*)
(*TODO: better abbreviation lfloor*)
abbreviation sbHdElem_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<surd>" ( "\<lfloor>_" 70) where
"\<lfloor>sb \<equiv> sbHdElem sb"
(*>*)
paragraph \<open>sbHdElem Properties \\\<close>

text\<open>Our @{const sbHdElem} operator maps each \gls{sb} to a 
corresponding @{type sbElem} exactly as intended. If the domain of 
the \gls{sb} is empty, it results in the @{const None} 
@{type sbElem} and if the input bundle contains no empty stream, the
resulting @{type sbElem} maps to the head of the corresponding 
streams.\<close>  

theorem sbhdelem_none[simp]:
"chDomEmpty TYPE('c) \<Longrightarrow> sbHdElem(sb::('c)\<^sup>\<Omega>) = Abs_sbElem(None)"
  by(simp add: sbHdElem_def sbHdElem_h_def)

theorem sbhdelem_some:
"sbHdElemWell sb \<Longrightarrow> 
 sbHdElem(sb::('c)\<^sup>\<Omega>) = Abs_sbElem(Some(\<lambda>c. shd(sb \<^enum>\<^sub>\<star> c)))"
  by(simp add: sbHdElem_def sbHdElem_h_def)

text\<open>Another interesting property is that two bundles contain no
empty stream in their domain, but are in order, will be mapped to 
the same @{type sbElem}.\<close>

theorem sbhdelem_mono_empty[simp]:
"chDomEmpty TYPE('cs) \<Longrightarrow> sbHdElem (x::'cs\<^sup>\<Omega>) = sbHdElem y"
  by simp

theorem sbhdelem_mono_eq[simp]:
"sbHdElemWell x \<Longrightarrow> (x::'cs\<^sup>\<Omega>) \<sqsubseteq> y \<Longrightarrow> sbHdElem x = sbHdElem y"
  apply(cases "chDomEmpty TYPE('cs)",simp)
  apply(simp_all add: sbhdelem_some)
  by (metis below_shd_alt monofun_cfun_arg sbnleast_mex)

subsubsection \<open>Constructing SBs with sbElem \label{subsub:sbconc}\<close>

text\<open>Given a @{type sbElem} and a \gls{sb}, we can append the 
\gls{sb} to the @{type sbElem}. Of course we also have to mind the 
domain when appending the bundle:
  \<^item> If the domain is empty, the output \gls{sb} is \<open>\<bottom>\<close>
  \<^item> If the domain is not empty, the output \gls{sb} has the input
    @{type sbElem} as its first element.


Only using this operator allows us to construct all \Gls{sb} where
every stream has the same length. But since there is no restriction
for the input bundle, we can map to any \gls{sb} with a a length
greater 0.\<close>

definition sbECons::"'c\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>" where
"sbECons sbe = sbConc (sbe2sb sbe)"

text\<open>Because we already constructed a converter \ref{subsub:sbe2sb}
from @{type sbElem}s to \Gls{sb} and the concatenation 
\ref{subsub:sbconc}, the definition of @{const sbECons} is straight 
forward. We also add another abbreviation for this function.\<close>

abbreviation sbECons_abbr::"'c\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega>"(infixr "\<bullet>\<^sup>\<surd>" 100) where
"sbe \<bullet>\<^sup>\<surd> sb \<equiv> sbECons sbe\<cdot>sb"

text\<open>Indeed results the concatenation in \<open>\<bottom> \<close> when the domain is
empty\<close>

theorem sbtypeempty_sbecons_bot[simp]:
"chDomEmpty TYPE ('cs) \<Longrightarrow> (sbe::'cs\<^sup>\<surd>) \<bullet>\<^sup>\<surd> sb = \<bottom>"
  by simp

lemma exchange_bot_sbecons:
"chDomEmpty TYPE ('cs) \<Longrightarrow> P sb \<Longrightarrow> P((sbe::'cs\<^sup>\<surd>) \<bullet>\<^sup>\<surd> sb)"
  by (metis (full_types) sbtypeepmpty_sbbot)

text\<open>It also holds, that the rest operator \ref{subsub:sbtake} of a
with @{const sbECons} constructed \gls{sb} is a destructor.\<close>

theorem sbrt_sbecons: "sbRt\<cdot>(sbe \<bullet>\<^sup>\<surd> sb) = sb"
  apply (cases "chDomEmpty(TYPE('a))", simp)
  apply (simp add: sbDrop.rep_eq)
  apply (simp add: sbECons_def)
  apply (subst sdropl6)
  apply (subgoal_tac "\<And>c. \<exists>m. sbe2sb sbe  \<^enum>  c = \<up>m")
  apply (metis Fin_0 Fin_Suc lnzero_def lscons_conv slen_scons 
         strict_slen sup'_def)
  apply (simp add: sbgetch_insert2 sbe2sb.rep_eq chDom_def)
  apply (metis Diff_eq_empty_iff chDom_def option.simps(5)
         sbtypenotempty_fex)
  by (simp add: sb_rep_eqI sbgetch_insert2 Rep_sb_inverse)

lemma sbhdelem_h_sbe:" sbHdElem_h (sbe \<bullet>\<^sup>\<surd> sb) = up\<cdot>sbe"
  apply (cases "chDomEmpty(TYPE('a))",simp)
  apply (simp_all add: sbHdElem_def sbHdElem_h_def)+
  apply (simp_all add: up_def)
  apply (metis sbtypeepmpty_sbenone)
  apply (simp add: sbECons_def,auto)
  apply (subgoal_tac "\<forall>c::'a. sbe2sb sbe  \<^enum>  c \<noteq> \<epsilon>") 
  apply (simp add: sbe2sb_def)
  apply (simp split: option.split)
  apply (rule conjI)
  apply (metis Abs_sb_strict option.simps(4) sbgetch_bot) 
  apply (metis (no_types, lifting) option.simps(5) sbHdElemWell_def 
         sbconc_bot_r sbconc_getch strictI) 
  using sbgetch_sbe2sb_nempty apply auto[1]
  apply(simp add: sbHdElemWell_def sbe2sb_def)
  apply (simp split: option.split,auto)
  apply (metis emptyE option.discI sbtypenotempty_fex)
  apply (subgoal_tac 
        "\<forall>c::'a. Abs_sb (\<lambda>c::'a. \<up>(x2 c))  \<^enum>  c = \<up>(x2 c)")
  apply (simp add: Abs_sbElem_inverse)
  apply (metis Rep_sbElem_inverse)
  by (metis option.simps(5) sbe2sb.abs_eq sbe2sb.rep_eq 
      sbgetch_insert2)

text\<open>Obtaining the head of such an constructed \gls{sb} results in 
a the @{type sbElem} used for constructing.\<close>

theorem sbhdelem_sbecons: "sbHdElem (sbe  \<bullet>\<^sup>\<surd> sb) = sbe"
  by(simp add: sbHdElem_def sbhdelem_h_sbe up_def)

text\<open>Constructing a \gls{sb} with @{const sbECons} increases its 
length by exactly 1. This also holds for empty domains, because we 
interpret the length of those \Gls{sb} as \<open>\<infinity>\<close>.\<close>

theorem sbecons_len:
  shows "sbLen (sbe \<bullet>\<^sup>\<surd> sb) = lnsuc\<cdot>(sbLen sb)"
  apply(cases "chDomEmpty(TYPE('a))")
  apply(simp)
  apply(rule sblen_rule,simp)
  apply(simp add: sbECons_def sbgetch_insert2 sbconc_insert)
  apply(subst Abs_sb_inverse)
  apply simp
  apply(insert sbconc_well[of "sbe2sb sbe" sb],simp add: 
        sbgetch_insert2)
  apply(subst sconc_slen2)
  apply(subgoal_tac "#(Rep_sb (sbe2sb sbe) c) = 1",auto)
  apply (metis equals0D lessequal_addition lnat_plus_commu 
         lnat_plus_suc sbelen_one sbgetch_insert2 sblen_min_len)
  apply (metis emptyE sbe2slen_1 sbgetch_insert2) 
  apply(simp add: chDom_def)
  by (metis (no_types, hide_lams) add.left_neutral cempty_rule 
      f_inv_into_f lnat_plus_commu one_def only_empty_has_length_0 
      sbECons_def sbconc_chan_len sbe2slen_1 sblen2slen sconc_slen2
      slen_scons)

lemma sbHdElem:
"sbLen (sb::'cs\<^sup>\<Omega>) \<noteq> (0::lnat) \<Longrightarrow> sbe2sb (sbHdElem sb) = sbHd\<cdot>sb"
  apply (case_tac "chDomEmpty (TYPE ('cs))")
  apply (metis (full_types) sbtypeepmpty_sbbot)
  apply (rule sb_rep_eqI)
  apply (simp add: sbHdElem_def sbHdElem_h_def)
  apply rule+ 
  using sbleast2sblenempty apply blast
  apply(simp add:sbtake_insert stake2shd sbe2sb.abs_eq 
        sbe2sb.rep_eq Abs_sbElem_inverse Abs_sb_inverse sb_well_def)
  by (metis (no_types) sbgetch_insert2 sbmap_stake_eq sbnleast_mex 
      stake2shd)

(*sb_ind*)

lemma sbtake_chain:"chain (\<lambda>i::nat. sbTake i\<cdot>x)"
  apply (rule chainI)
  apply(simp add: below_sb_def)
  apply(rule fun_belowI)
  apply(simp add: sbtake_insert)
  by (metis (no_types) Suc_leD le_refl sbgetch_insert2 
      sbmap_stake_eq stake_mono)

lemma sblen_sbtake:
"\<not>chDomEmpty TYPE ('c) \<Longrightarrow> sbLen (sbTake n\<cdot>(x :: 'c\<^sup>\<Omega>)) \<le> Fin (n)"
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

lemma sbECons_sbLen:"sbLen (sb::'cs\<^sup>\<Omega>) \<noteq> (0::lnat) \<Longrightarrow>
 \<not> chDomEmpty TYPE('cs) \<Longrightarrow> \<exists> sbe sb'. sb = sbe \<bullet>\<^sup>\<surd> sb'"
  by (metis sbECons_def sbHdElem sbcons)

paragraph \<open>SB induction and case rules \\\<close>

text\<open>This framework also offers the proof methods using the 
@{type sbElem} constructor, that offer an easy proof process in when 
applied correctly. The first method is a case distinction for 
\Gls{sb}. It differentiates between the small \Gls{sb} where an 
empty stream exists and all other \Gls{sb}.\<close>

theorem sb_cases [case_names least sbeCons, cases type: sb]: 
  "(sbIsLeast (sb'::'cs\<^sup>\<Omega>) \<Longrightarrow> P) 
  \<Longrightarrow> (\<And>sbe sb. sb' = sbe \<bullet>\<^sup>\<surd> sb \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) \<Longrightarrow> P) 
  \<Longrightarrow> P"
  by (meson sbECons_sbLen sbnleast_dom sbnleast_len)

lemma sb_finind1:
    fixes x::"'cs\<^sup>\<Omega>"
    shows "sbLen x = Fin k
          \<Longrightarrow> (\<And>sb. sbIsLeast sb \<Longrightarrow> P sb) 
          \<Longrightarrow> (\<And>sbe sb. P sb 
          \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb))
          \<Longrightarrow>P x"
  apply(induction k  arbitrary:x)
  using sbnleast_len apply fastforce
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
        (\<forall> (sbe::'cs\<^sup>\<surd>) sb::'cs\<^sup>\<Omega>. P sb  \<longrightarrow> \<not>chDomEmpty TYPE ('cs) 
        \<longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb))) \<and> 
        ( \<not>chDomEmpty TYPE ('cs) \<longrightarrow> sbLen x \<le> Fin n) \<longrightarrow> P (x)"
  by (metis (no_types, lifting) inf_ub less2eq 
      order.not_eq_order_implies_strict sb_cases sb_finind 
      sb_finind1)

lemma sbtakeind: 
  fixes x::"'cs\<^sup>\<Omega>"
  shows "\<forall>x. (( \<forall>(sb::'cs\<^sup>\<Omega>) . sbIsLeast sb \<longrightarrow> P sb) \<and> 
         (\<forall> (sbe::'cs\<^sup>\<surd>) sb::'cs\<^sup>\<Omega>. P sb  \<longrightarrow> \<not>chDomEmpty TYPE ('cs) 
          \<longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb))) 
          \<longrightarrow> P (sbTake  n\<cdot>x)"
  apply rule+
  apply(subst sbtakeind1, simp_all) 
  using sblen_sbtake sbtakeind1 by auto

text\<open>The second showcased proof method is the induction for
\Gls{sb}. Beside the admissibility of the predicate, we divide the
induction into to the case tactic similar predicates.\<close>  

theorem sb_ind[case_names adm least sbeCons, induct type: sb]:
  fixes x::"'cs\<^sup>\<Omega>"
  assumes "adm P" 
  and "\<And>sb. sbIsLeast sb \<Longrightarrow> P sb"
  and "\<And>sbe sb. P sb \<Longrightarrow> \<not>chDomEmpty TYPE ('cs) \<Longrightarrow> P (sbe \<bullet>\<^sup>\<surd> sb)"   
  shows  "P x"
  using assms(1) assms(2) assms(3) 
  apply(unfold adm_def)
  apply(erule_tac x="\<lambda>i. sbTake i\<cdot>x" in allE,auto)
  apply(simp add: sbtake_chain)
  apply(simp add: sbtakeind)
  by(simp add: sbtake_lub)

lemma sbecons_eq:
  assumes "sbLen sb \<noteq> 0" 
  shows "(sbHdElem sb) \<bullet>\<^sup>\<surd> (sbRt\<cdot>sb) = sb"
  by (metis assms sbECons_def sbHdElem sbcons)

subsubsection \<open>Converting Domains of SBs \label{subsub:sbconvert}\<close>

text\<open>Two \Gls{sb} with a different type are not comparable, since 
only \Gls{sb} with the same type have an order. This holds even if 
the domain of both types is the same. To make them comparable we
introduce a converter that converts the type of a \Gls{sb}. This
converter can then make two \Gls{sb} of different type comparable.
Since it does change the type, it can also restrict or expand the 
domain of a \gls{sb}. Newly added channels map to \<open>\<epsilon>\<close>.\<close>

lemma sbconvert_well[simp]:"sb_well (\<lambda>c. sb \<^enum>\<^sub>\<star> c)"
  by(rule sbwellI, simp)

lift_definition sbConvert::"'c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega>"is
"(\<lambda> sb. Abs_sb (\<lambda>c.  sb \<^enum>\<^sub>\<star> c ))"
  by(intro cont2cont, simp)

text\<open>Because restricting the domain of a \gls{sb} is an important 
feature of this framework, we offer explicit abbreviations for such
cases.\<close>

lemmas sbconvert_insert = sbConvert.rep_eq

abbreviation sbConvert_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega>" ( "_\<star>" 200) where 
"sb\<star> \<equiv> sbConvert\<cdot>sb"

abbreviation sbConvert_abbr_fst :: "('c \<union> 'd)\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega>"
( "_\<star>\<^sub>1" 200) where "sb\<star>\<^sub>1 \<equiv> sbConvert\<cdot>sb"

abbreviation sbConvert_abbr_snd :: "('c\<union>'d)\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega>"
 ( "_\<star>\<^sub>2" 200) where "sb\<star>\<^sub>2 \<equiv> sbConvert\<cdot>sb"

lemma sbconvert_rep[simp]: "Rep_sb(sb\<star>) = (\<lambda>c. sb \<^enum>\<^sub>\<star> c)"
  by (simp add: Abs_sb_inverse sbconvert_insert)

lemma fixes sb ::"'a\<^sup>\<Omega>"
  shows "sb\<star> \<^enum>\<^sub>\<star> c = sb \<^enum>\<^sub>\<star> c"
  apply(cases "Rep c\<in>(range(Rep::'a\<Rightarrow>channel))")
   apply(auto simp add: sbgetch_insert)
  oops (* gilt nicht, wenn 'b kleiner ist als 'a *)

lemma sbconv_eq[simp]:"sb\<star> = sb"
  apply(rule sb_eqI)
  by (metis (no_types) Abs_sb_inverse mem_Collect_eq 
        sbconvert_insert sbconvert_well sbgetch_insert2)

lemma sbconvert_getch [simp]: "sb \<star> \<^enum> c = sb \<^enum>\<^sub>\<star> c"
  by (simp add: sbgetch_insert2)


subsubsection \<open>Union of SBs\<close>

text\<open>The union operator for streams merges two \Gls{sb} together.
The output domain is equal to the union of its input domains.
But again we use a slightly different signature for the
general definition. It is equal to applying the converter after
building the exact union of both bundles. \<close>

definition sbUnion::"'c\<^sup>\<Omega> \<rightarrow> 'd\<^sup>\<Omega> \<rightarrow> 'e\<^sup>\<Omega>" where
"sbUnion \<equiv> \<Lambda> sb1 sb2. Abs_sb (\<lambda> c. 
                  if Rep c \<in> chDom TYPE('c) 
                  then sb1 \<^enum>\<^sub>\<star> c 
                  else sb2 \<^enum>\<^sub>\<star> c)"

lemma sbunion_sbwell[simp]: "sb_well ((\<lambda> (c::'e). 
                  if (Rep c \<in> chDom TYPE('c)) then 
                  (sb1::'c\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c else  (sb2::'d\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c))"
  apply(rule sbwellI)
  by simp

lemma sbunion_insert:"sbUnion\<cdot>(sb1::'c\<^sup>\<Omega>)\<cdot>sb2 = Abs_sb (\<lambda> c. if 
                  (Rep c \<in> chDom TYPE('c)) then 
                  sb1 \<^enum>\<^sub>\<star> c else  sb2 \<^enum>\<^sub>\<star> c)"
  unfolding sbUnion_def
  apply(subst beta_cfun, intro cont2cont, simp)+
  ..
(* TODO: sbunion_rep_eq 
  Namin_convention: "insert" = Abs_cfun weg
                      rep_eq = Abs_XXX weg *)

lemma sbunion_rep_eq:"Rep_sb (sbUnion\<cdot>(sb1::'c\<^sup>\<Omega>)\<cdot>sb2) = 
 (\<lambda> c. if (Rep c \<in> chDom TYPE('c))
         then sb1 \<^enum>\<^sub>\<star> c 
         else  sb2 \<^enum>\<^sub>\<star> c)"
  apply(subst sbunion_insert)
  apply(subst Abs_sb_inverse)
  by auto

text\<open>The following abbreviations restrict the input and output
domains of @{const sbUnion} to specific cases. These are displayed 
by its signature.\<close>

abbreviation sbUnion_magic_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega> \<Rightarrow> 'e\<^sup>\<Omega>"
(infixr "\<uplus>\<^sub>\<star>" 100) where "sb1 \<uplus>\<^sub>\<star> sb2 \<equiv> sbUnion\<cdot>sb1\<cdot>sb2"

abbreviation sbUnion_minus_abbr :: "('c - ('d))\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega>"
(infixr "\<uplus>\<^sub>-" 100) where "sb1 \<uplus>\<^sub>- sb2 \<equiv> sbUnion\<cdot>sb1\<cdot>sb2"

abbreviation sbUnion_abbr :: "'c\<^sup>\<Omega> \<Rightarrow> 'd\<^sup>\<Omega> \<Rightarrow> ('c\<union>'d)\<^sup>\<Omega>"
(infixr "\<uplus>" 100) where "sb1 \<uplus> sb2 \<equiv> sb1 \<uplus>\<^sub>\<star> sb2"


paragraph \<open>sbUnion Properties \\\<close>

text \<open>Here we show how our union operator works.\<close>

lemma sbunion_getch[simp]:fixes c::"'a"
      assumes"Rep c \<in> chDom TYPE('c)"
      shows  "(sbUnion::'a\<^sup>\<Omega>\<rightarrow> 'b\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>)\<cdot>cb\<cdot>db \<^enum>\<^sub>\<star> c = cb \<^enum> c"
  apply(simp add: sbgetch_insert sbunion_rep_eq)
  by (metis assms Diff_iff chDom_def chan_eq range_eqI 
      sbgetch_insert sbgetch_insert2)

lemma sbunion_eq [simp]: "sb1 \<uplus>\<^sub>\<star> sb2 = sb1"
  apply(rule sb_eqI)
  by simp

lemma sbunion_sbconvert_eq[simp]:"cb \<uplus>\<^sub>\<star> cb = (cb\<star>)"
  by(simp add: sbunion_insert sbconvert_insert)

text\<open>The union operator is commutative, if the domains of its input
are disjoint.\<close>

theorem ubunion_commu:
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
    assumes "chDom (TYPE ('cs1)) \<inter> chDom (TYPE ('cs2)) = {}"
    shows "sb1 \<uplus>\<^sub>\<star> sb2 = ((sb2 \<uplus>\<^sub>\<star> sb1)::'cs3\<^sup>\<Omega>)"
  apply(rule sb_rep_eqI)
  apply(simp add: sbunion_rep_eq sbgetch_insert)
  using assms cdom_notempty cempty_rule cnotempty_cdom by blast

lemma ubunion_fst[simp]:
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "chDom (TYPE ('cs2)) \<inter> chDom (TYPE ('cs3)) = {}"
  shows "sb1 \<uplus>\<^sub>\<star> sb2 = (sb1\<star> :: 'cs3\<^sup>\<Omega>)"
  apply(rule sb_rep_eqI)
  apply(simp add: sbunion_rep_eq sbgetch_insert)
  using assms cdom_notempty cempty_rule cnotempty_cdom by blast

lemma ubunion_id[simp]: "out\<star>\<^sub>1 \<uplus> (out\<star>\<^sub>2) = out"
proof(rule sb_eqI)
  fix c::"'a \<union> 'b"
  assume as:"Rep c \<in> chDom TYPE('a \<union> 'b)"
  have "Rep c \<in> chDom (TYPE ('a)) \<Longrightarrow> out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c"
    by (metis sbgetch_insert2 sbunion_getch sbunion_rep_eq 
        sbunion_sbconvert_eq)
  moreover have "Rep c \<in> chDom (TYPE ('b)) 
                 \<Longrightarrow> out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c"
    by (metis sbgetch_insert2 sbunion_getch sbunion_rep_eq 
        sbunion_sbconvert_eq)
  moreover have "Rep c \<in> chDom TYPE ('a) \<or> Rep c \<in> chDom TYPE ('b)"
    using as chdom_in by fastforce
  ultimately show  "out\<star> \<uplus> (out\<star>) \<^enum> c = out \<^enum> c" by fastforce
qed

text\<open>The union of two \Gls{sb} maps each channel in the domain of 
the first input \gls{sb} to the corresponding stream of the first 
\gls{sb}.\<close>

theorem sbunion_getchl[simp]:
    fixes sb1 ::"'cs1\<^sup>\<Omega>"
      and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<in> chDom TYPE('cs1)"
    shows "(sb1 \<uplus> sb2) \<^enum>\<^sub>\<star> c = sb1 \<^enum>\<^sub>\<star> c"
  apply(auto simp add: sbgetch_insert sbunion_rep_eq assms)
  apply (metis Rep_union_def UnI1 assms equals0D f_inv_into_f 
         union_range_union)
  apply (metis Rep_union_def UnCI assms f_inv_into_f 
         union_range_union)
  apply (metis Rep_union_def UnCI assms chan_eq union_range_union)
  by (metis Rep_union_def Un_iff assms chan_eq empty_iff 
      union_range_union)

text\<open>This also holds for the second input \gls{sb}, if the domains
of both \Gls{sb} are disjoint.\<close>

theorem sbunion_getchr[simp]:
    fixes sb1 ::"'cs1\<^sup>\<Omega>"
      and sb2 ::"'cs2\<^sup>\<Omega>"
  assumes "Rep c \<notin> chDom TYPE('cs1)"
  shows   "(sb1 \<uplus> sb2) \<^enum>\<^sub>\<star> c = sb2 \<^enum>\<^sub>\<star> c"
  apply(auto simp add: sbgetch_insert sbunion_rep_eq assms)
  apply (metis Rep_union_def UnCI assms f_inv_into_f 
         union_range_union)
  apply (metis Rep_union_def UnCI chan_eq union_range_union)
  apply (metis Rep_union_def UnCI f_inv_into_f union_range_union)
  by (metis Rep_union_def Un_iff chan_eq empty_iff 
      union_range_union)

lemma sbunion_getch_nomag [simp]:
"sb1 \<uplus>\<^sub>\<star> sb2  \<^enum>  c = (sb1 \<uplus> sb2) \<^enum>\<^sub>\<star> c"
  by(auto simp add: sbgetch_insert2 sbunion_rep_eq)

text\<open>Our general union operator is equivalent to the restricted
union with an conversion of the output.\<close>

theorem untion_convert_mag:"sb1 \<uplus>\<^sub>\<star> sb2 = ((sb1 \<uplus> sb2)\<star>)"
  by(simp add: sb_eqI)

lemma sbunion_magic: 
  fixes sb1 ::"'cs1\<^sup>\<Omega>"
    and sb2 ::"'cs2\<^sup>\<Omega>"
  shows "(sb1 \<uplus> sb2)\<star> = sb1 \<uplus>\<^sub>\<star> sb2"
  apply(rule sb_eqI)
  by auto

text\<open>It then follows directly, that restricting the unions domain 
to the first inputs domain is equal to the first input. Analogous
this also holds for the second input, if the input domains are
disjoint.\<close>

theorem sbunion_fst[simp]: "(sb1 \<uplus> sb2)\<star>\<^sub>1 = sb1"
  by (simp add: sbunion_magic)

theorem sbunion_snd[simp]:
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


lemma union_minus_nomagfst[simp]:
        fixes sb1 ::"(('a \<union> 'b) - 'c \<union> 'd)\<^sup>\<Omega>"
          and sb2 ::"('c \<union> 'd)\<^sup>\<Omega>"
        shows "sb1 \<uplus>\<^sub>\<star> sb2 = ((sb1 \<uplus>\<^sub>- sb2)\<star>\<^sub>1)"
  apply(rule sb_eqI,simp)
  apply(case_tac "Rep c\<in> chDom TYPE('c \<union> 'd)",auto)
  apply(simp_all add: sbgetch_insert sbunion_rep_eq,auto)
  by (metis Rep_union_def UnCI all_not_in_conv chan_eq 
      union_range_union)+

lemma union_minus_nomagsnd[simp]:
        fixes sb1 ::"(('a \<union> 'b) - 'c \<union> 'd)\<^sup>\<Omega>"
          and sb2 ::"('c \<union> 'd)\<^sup>\<Omega>"
        shows "sb1 \<uplus>\<^sub>\<star> sb2 = ((sb1 \<uplus>\<^sub>- sb2)\<star>\<^sub>2)"
  apply(rule sb_eqI,simp)
  apply(case_tac "Rep c\<in> chDom TYPE('c \<union> 'd)",auto)
  apply(simp_all add: sbgetch_insert sbunion_rep_eq,auto)
  by (metis Rep_union_def UnCI all_not_in_conv chan_eq 
      union_range_union)+

(*<*)
end
(*>*)
