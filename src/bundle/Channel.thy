(*<*)
theory Channel

imports HOLCF user.Datatypes
begin
(*>*)

section \<open>Global message type\<close>

text\<open>Depending on the time model, we allow to transmit slightly different versions of @{type M_pure} 
messages. In every time slot of the synchronous time model, every channel transmits at most one 
message. But in every time slot of the general timed model, it is possible to transmit an arbitrary 
high, but finite number of messages \ref{sec:focus}. To allow the usage of both models and also the untimed model, 
we introduce the M datatype:\<close>
datatype M = Untimed "M_pure" | Timed "M_pure list" | Tsyn "M_pure option"  (* option = tsyn *)

text\<open>We interpret the messages in a time slot of a time model as:
\begin{itemize}
  \<^item> a message, for the untimed model and there is no time slot
  \<^item> either Some message or None message at all, for the synchronous time model
  \<^item> a finite list of messages, for the timed model
\end{itemize}
In this interpretation a untimed stream can be seen as a special case of a synchronous timed stream
(it contains a message in every time slot) and a synchronous timed stream is a special case of a 
timed stream (it contains at most one element in each list). Now we defined, how a transmitted 
message in a time slot can look like, respectively to its time model. For this we define a mapping
from channel to a set of elements from M. Obviously, we have to restrict the channels to their time
models, else there could be timed and untimed messages on the same channel.\<close>

lemma inj_tsyn[simp]: "inj Tsyn"
  by (simp add: inj_def)

lemma inj_tsyncons[simp]:"inj f \<Longrightarrow> inj (Tsyn o (map_option) f)"
  by (meson comp_inj_on inj_eq inj_onI inj_tsyn option.inj_map)

lemma inj_timed[simp]: "inj Timed"
  by (simp add: inj_def)

lemma inj_timedcons[simp]:"inj f \<Longrightarrow> inj (Timed o map f)"
  by(simp add: inj_compose)

lemma inj_untimed[simp]: "inj Untimed"
  by (simp add: inj_def)

lemma inj_untimedcons[simp]:"inj f \<Longrightarrow> inj (Untimed o f)"
  by(simp add: inj_compose)

instance M::countable
  by(countable_datatype)

definition ctype::"channel \<Rightarrow> M set" where
"ctype c \<equiv> if (cMsg c) = {} then {} else 
  case (cTime c) of TUntimed   \<Rightarrow> Untimed ` (cMsg c) | 
                   TTimed     \<Rightarrow>  Timed ` {ls. set ls \<subseteq> (cMsg c)} |
                   TTsyn      \<Rightarrow> Tsyn ` (insert None (Some ` cMsg c))"

theorem ctype_empty_gdw: "ctype c = {} \<longleftrightarrow> cMsg c = {}"
  apply(cases "(cTime c)")
  apply (auto simp add: ctype_def)
  by (metis bot.extremum empty_set)

theorem ctypeempty_ex:"\<exists>c. ctype c = {}"
  by (simp add: cmsgempty_ex ctype_empty_gdw)




definition cEmpty :: "channel set" where
"cEmpty = {c. ctype c = {}}"
text \<open>@{const cEmpty} contains all channels on which no message is allowed to be transmitted.\<close> 

section\<open>@{type channel} class definitions\<close>

subsection\<open>Class chan\<close>
class chan =
  fixes Rep :: "'a \<Rightarrow> channel"
  assumes chan_botsingle:
      "(range Rep) \<subseteq> cEmpty 
           \<or> (range Rep) \<inter> cEmpty = {}" 
  assumes chan_inj[simp]:"inj Rep"
begin
abbreviation "Abs \<equiv> inv Rep"

end

subsubsection \<open>@{class chan} Functions\<close>

definition chDom::"'cs::chan itself \<Rightarrow> channel set" where
"chDom a = (range (Rep::'cs \<Rightarrow> channel)) - cEmpty"

definition chIsEmpty ::"'cs::chan itself \<Rightarrow> bool" where
"chIsEmpty cs = (range(Rep::'cs\<Rightarrow>channel) \<subseteq> cEmpty)"

text \<open>Types of @{class chan} can be interpreted as a subset of @{type channel}s, where on every
channel either no message can be transmitted, or on every channel some message is allowed to be
transmitted. Now we define classes for these two options:\<close>

subsection\<open>Class somechan\<close>
class somechan = chan +
  assumes chan_notempty:
      "(range Rep) \<inter> cEmpty = {}"
begin

corollary somechannotempty[simp]:"\<not>chIsEmpty(TYPE('c::somechan))"
  using chIsEmpty_def somechan_class.chan_notempty by fastforce

corollary somechandom:"chDom(TYPE('c::somechan)) = range(Rep::'c\<Rightarrow>channel)"
  by(simp add: chDom_def somechan_class.chan_notempty Diff_triv)

end
text\<open>Types of  @{class somechan} can transmit at least one message on every channel.\<close>
subsection\<open>Class emptychan\<close>
class emptychan = chan +
  assumes chan_empty:
      "(range Rep) \<subseteq> cEmpty" 
begin

lemma %invisible emptychanempty[simp]:"chIsEmpty(TYPE('c::emptychan))"
  by (simp add: chIsEmpty_def emptychan_class.chan_empty)

lemma %invisible emptychandom[simp]:"chDom(TYPE('c::emptychan)) = {}"
  by(simp add: chDom_def emptychan_class.chan_empty)

end
text\<open>Types of @{class emptychan} can not transmit any message on any channel.\<close>



section %invisible\<open> rep abs chan lemmata \<close>
lemma repinrange[simp]:"Rep (c::'c::chan) = x \<Longrightarrow> x\<in> range(Rep::'c \<Rightarrow> channel)"
  by blast

lemma chan_eq[simp]:"Rep (c::'c::chan) = x \<Longrightarrow> x\<in> range(Rep::'d::chan \<Rightarrow> channel) 
                        \<Longrightarrow> Rep((Abs::channel \<Rightarrow> 'd)(Rep c)) = x"
  by (simp add: f_inv_into_f)

lemma cempty_rule[simp]:assumes"chIsEmpty(TYPE('c::chan))"
  shows"Rep (c::'c) \<in> cEmpty"
  using assms chan_botsingle chIsEmpty_def by blast

lemma cnotempty_rule[simp]:assumes"\<not>chIsEmpty(TYPE('c::chan))"
  shows"Rep (c::'c) \<notin> cEmpty"
  using assms chan_botsingle chIsEmpty_def by blast

lemma cnotempty_cdom[simp]:assumes"\<not>chIsEmpty(TYPE('c::chan))"
  shows"Rep (c::'c) \<in> chDom(TYPE('c))"
  by (simp add: assms chDom_def)


declare %invisible[[show_types]]
declare %invisible[[show_consts]]

section \<open>chan \<open>\<union>\<close> and \<open>-\<close> \<close>

typedef ('c1::chan, 'c2::chan) union (infixr "\<union>" 20) = "if range (Rep::'c1\<Rightarrow>channel)\<subseteq>cEmpty \<and>  range (Rep::'c2\<Rightarrow>channel)\<subseteq>cEmpty then cEmpty
                                                        else (range (Rep::'c1\<Rightarrow>channel) \<union> range (Rep::'c2\<Rightarrow>channel)) - cEmpty" 
   apply(auto)
  done

(* Axiom :/ *)
lemma cempty_exists: "cEmpty \<noteq> {}"
  by(simp add: cEmpty_def ctypeempty_ex)


typedef ('c1::chan, 'c2::chan) minus (infixr "-" 20) = "(if range (Rep::'c1\<Rightarrow>channel) \<subseteq> range (Rep::'c2\<Rightarrow>channel) then cEmpty
                                                         else range (Rep::'c1\<Rightarrow>channel) - range (Rep::'c2\<Rightarrow>channel))" 
apply(cases "range Rep \<subseteq> range Rep", auto)
  using cempty_exists by blast+

instantiation union :: (chan, chan) chan 
begin
definition "Rep == Rep_union"
instance
  apply intro_classes
  apply auto
  apply (metis (full_types) Diff_iff Rep_union Rep_union_def)
  by (simp add: Channel.Rep_union_def Rep_union_inject inj_on_def)
end

instantiation minus :: (chan, chan) chan 
begin
definition "Rep == Rep_minus"
instance
  apply intro_classes
   apply auto
  apply (metis (mono_tags, lifting) Diff_eq_empty_iff Diff_iff IntI Rep_minus Rep_minus_def chan_botsingle)
  by (smt Rep_minus_def Rep_minus_inject injI)
end


default_sort chan
theorem chdom_minus[simp]: "chDom (TYPE('cs1 - 'cs2)) = chDom (TYPE ('cs1)) - chDom (TYPE('cs2))"
  apply(simp add: chDom_def Rep_minus_def)
  apply auto
  apply (meson Diff_iff Rep_minus)
  apply (metis DiffE Rep_minus repinrange)
proof -
  fix xa :: 'cs1
  assume a1: "Rep xa \<notin> range (\<lambda>x. Rep (x::'cs2))"
  then have f2: "\<not> range (Rep::'cs1 \<Rightarrow> channel) \<subseteq> range (Rep::'cs2 \<Rightarrow> channel)"
    by (metis repinrange subsetD)
  have "range (Rep_minus::'cs1 - 'cs2 \<Rightarrow> channel) = (if range (Rep::'cs1 \<Rightarrow> channel) \<subseteq> range (Rep::'cs2 \<Rightarrow> channel) then cEmpty else range (Rep::'cs1 \<Rightarrow> channel) - range (Rep::'cs2 \<Rightarrow> channel))"
    using type_definition.Rep_range type_definition_minus by blast
  then show "Rep xa \<in> range (\<lambda>m. Rep_minus (m::'cs1 - 'cs2))"
    using f2 a1 by (metis (full_types) DiffI repinrange)
qed


theorem chdom_union[simp]: "chDom (TYPE('cs1 \<union> 'cs2)) = chDom (TYPE ('cs1)) \<union> chDom (TYPE('cs2))"
  apply(simp add: chDom_def Rep_union_def)
  apply auto
  apply (meson DiffD1 Rep_union UnE)
proof -
  fix xa :: 'cs1
  assume "Rep xa \<notin> cEmpty"
then have f1: "\<not> chIsEmpty (TYPE('cs1)::'cs1 itself)"
  by (metis cempty_rule)
  have "type_definition (Rep_union::'cs1 \<union> 'cs2 \<Rightarrow> channel) Abs_union (if range (Rep::'cs1 \<Rightarrow> channel) \<subseteq> cEmpty \<and> range (Rep::'cs2 \<Rightarrow> channel) \<subseteq> cEmpty then cEmpty else range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel) - cEmpty) = type_definition (Rep_union::'cs1 \<union> 'cs2 \<Rightarrow> channel) Abs_union (if \<not> range (Rep::'cs1 \<Rightarrow> channel) \<subseteq> cEmpty \<or> \<not> range (Rep::'cs2 \<Rightarrow> channel) \<subseteq> cEmpty then range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel) - cEmpty else cEmpty)"
by presburger
  then have "type_definition (Rep_union::'cs1 \<union> 'cs2 \<Rightarrow> channel) Abs_union (if \<not> range (Rep::'cs1 \<Rightarrow> channel) \<subseteq> cEmpty \<or> \<not> range (Rep::'cs2 \<Rightarrow> channel) \<subseteq> cEmpty then range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel) - cEmpty else cEmpty)"
    by (meson type_definition_union)
  then show "Rep xa \<in> range (\<lambda>u. Rep_union (u::'cs1 \<union> 'cs2))"
using f1 by (simp add: chIsEmpty_def type_definition.Rep_range)
next
  fix xa :: 'cs2
  assume "Rep xa \<notin> cEmpty"
then have f1: "\<not> chIsEmpty (TYPE('cs2)::'cs2 itself)"
  by (metis cempty_rule)
  have "type_definition (Rep_union::'cs1 \<union> 'cs2 \<Rightarrow> channel) Abs_union (if range (Rep::'cs1 \<Rightarrow> channel) \<subseteq> cEmpty \<and> range (Rep::'cs2 \<Rightarrow> channel) \<subseteq> cEmpty then cEmpty else range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel) - cEmpty) = type_definition (Rep_union::'cs1 \<union> 'cs2 \<Rightarrow> channel) Abs_union (if \<not> range (Rep::'cs1 \<Rightarrow> channel) \<subseteq> cEmpty \<or> \<not> range (Rep::'cs2 \<Rightarrow> channel) \<subseteq> cEmpty then range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel) - cEmpty else cEmpty)"
by presburger
  then have "type_definition (Rep_union::'cs1 \<union> 'cs2 \<Rightarrow> channel) Abs_union (if \<not> range (Rep::'cs1 \<Rightarrow> channel) \<subseteq> cEmpty \<or> \<not> range (Rep::'cs2 \<Rightarrow> channel) \<subseteq> cEmpty then range (Rep::'cs1 \<Rightarrow> channel) \<union> range (Rep::'cs2 \<Rightarrow> channel) - cEmpty else cEmpty)"
    by (meson type_definition_union)
  then show "Rep xa \<in> range (\<lambda>u. Rep_union (u::'cs1 \<union> 'cs2))"
    using f1 by (simp add: chIsEmpty_def type_definition.Rep_range)
qed

theorem "chDom (TYPE('cs1 - 'cs2)) \<inter> chDom (TYPE ('cs2)) = {}"
  by auto

(*<*)
end
(*>*)