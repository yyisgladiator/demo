(*<*)(*:maxLineLen=68:*)
theory Channel

imports HOLCF user.Datatypes
begin
(*>*)

section \<open>Global message type \label{sec:gmt}\<close>

text\<open>Depending on the time model, we allow to transmit slightly 
different versions of @{type M_pure} messages. In every time slot of 
the synchronous time model, every channel transmits at most one 
message. But in every time slot of the general timed model, it is 
possible to transmit an arbitrary high, but finite number of 
messages. To allow the usage of both models and also the untimed
model, we introduce the M datatype:\<close>

datatype M = Untimed "M_pure" | 
             Timed "M_pure list" | 
             Tsyn "M_pure option"  
             (* option = tsyn *)

text\<open>We interpret the messages in a time slot of a time model as:
  \<^item> a message, for the untimed model and there is no time slot
  \<^item> either Some message or None message at all, for the synchronous 
    time model
  \<^item> a finite list of messages, for the timed model


In this interpretation a untimed stream can be seen as a special
case of a synchronous timed stream (it contains a message in every
time slot) and a synchronous timed stream is a special case of a 
timed stream (it contains at most one element in each list). Now we 
defined, how a transmitted message in a time slot can look like, 
respectively to its time model. For this, we define a mapping from 
channels to sets of elements from M. Obviously, we have to restrict 
the channels to their time models, else there could be timed and 
untimed messages on the same channel.\<close>

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
"ctype c \<equiv> if (cMsg c) = {} then {} else case (cTime c) of 
                 TUntimed   \<Rightarrow> Untimed ` (cMsg c) | 
                 TTimed     \<Rightarrow>  Timed ` {ls. set ls \<subseteq> (cMsg c)} |
                 TTsyn      \<Rightarrow> Tsyn ` (insert None (Some ` cMsg c))"

text\<open>This is exactly what @{const ctype} does. It then checks the 
timing of a channel and then returns the respectively correct set of 
timeslot messages, where the pure messages depend on @{const cMsg}.
  \<^item> Untimed channels can send any message from @{const cMsg}
  \<^item> Timesynchronous channels can send \<open>Some\<close> message from 
    @{const cMsg} or the  \<open>None\<close> message, interpreted as no Message
  \<^item> Timed channels can send finite lists, where every list element 
    is in @{const cMsg}.


Because we interpret channels without any allowed transmitted 
messages as no channel at all, we define their @{const ctype} as 
empty. Hence the following theorems hold.\<close>

theorem ctype_empty_iff: "ctype c = {} \<longleftrightarrow> cMsg c = {}"
  apply(cases "(cTime c)")
  apply (auto simp add: ctype_def)
  by (metis bot.extremum empty_set)

theorem ctypeempty_ex:"\<exists>c. ctype c = {}"
  by (simp add: cmsgempty_ex ctype_empty_iff)

text\<open>Again, these properties are necessary for defining an empty 
stream bundle\ref{sec:pmsgdata}.\<close>


section\<open>Channel class definitions\label{sec:chan}\<close>

text\<open>In this section we restrict the domain of a stream bundle
trough the usage of classes. The main Idea is to never construct a 
stream bundle which has channels with an empty @{const ctype} and 
channels with non-empty @{const ctype}. With our interpretation of 
empty bundles, this case would make no sense, because it would be 
equivalent to the bundle without channels with empty 
@{const ctype}s. Hence, we restrict the Domain of stream bundles to 
subsets of the @{type channel} type, where its either possible that 
every channel transmits a message, or non of the channels can 
transmit any message at all. We will then use these classes to 
define the union and subtraction of two domains. This is helpful for
combining two stream bundles and hence, necessary for defining the 
input and output domain of the general composition operator.\<close>

subsection \<open>Preliminaries \label{sub:prelim}\<close>
text\<open>For understandable assumptions in our classes we first define 
the channel set, that contains all channels with an empty 
@{const ctype}.\<close>

definition cEmpty :: "channel set" where
"cEmpty = {c. ctype c = {}}"

text \<open>@{const cEmpty} contains all channels on which no message is 
allowed to be transmitted.\<close> 

lemma cempty_exists: "cEmpty \<noteq> {}"
  by(simp add: cEmpty_def ctypeempty_ex)

subsection\<open>Class chan \label{sub:chan}\<close>

text\<open>The following class restricts its type to be injective to our 
@{type channel} type and to also comply with our main Idea. Through 
its injectivity, the type is isomorphic to a subset of our 
@{type channel} type.\<close>

class chan =
  fixes Rep :: "'a \<Rightarrow> channel"
  assumes chan_botsingle:
      "(range Rep) \<subseteq> cEmpty \<or>
       (range Rep) \<inter> cEmpty = {}" 
  assumes chan_inj[simp]:"inj Rep"
begin
  abbreviation "Abs \<equiv> inv Rep"
end

text\<open> With @{const Rep} we require a representation function, that 
maps a type of @{class chan} to the @{type channel} type. The first 
class assumption ensures our channel separation and the second the 
injectivity. Furthermore, our abstraction function @{const Abs} is 
the inverse of @{const Rep}.\<close>

subsubsection \<open>Class functions \label{sub:clfun}\<close>

text\<open>We will now define a function for types of @{class chan}. It 
returns the Domain of the type. As a result of our class assumptions 
and of interpreting empty channels as non existing, our domain is 
empty, if and only if the input type contains channel(s) from 
@{const cEmpty}. Then we have the empty domain.\<close>

definition chDom::"'cs::chan itself \<Rightarrow> channel set" where
"chDom a = (range (Rep::'cs \<Rightarrow> channel)) - cEmpty"

text\<open>The following abbreviation checks, if a type of @{class chan} 
is empty.\<close>

abbreviation chDomEmpty ::"'cs::chan itself \<Rightarrow> bool" where
"chDomEmpty cs \<equiv> chDom cs = {}"

lemma inchdom[simp]:"\<not>chDomEmpty TYPE('cs) 
                     \<Longrightarrow> Rep (c::'cs::chan) \<in> chDom TYPE('cs)"
  apply(simp add: chDom_def)
  using chan_botsingle by blast

text \<open>As mentioned before, types of @{class chan} can be interpreted 
as a subset of @{type channel}s, where on every channel either no 
message can be transmitted, or on every channel some message is 
allowed to be transmitted. The core theories do not use these 
classes, but the additional assumptions can be useful for the user. 
Now we define classes for these two options.\<close>

subsubsection\<open>Class somechan\<close>
class somechan = chan +
  assumes chan_notempty:"(range Rep) \<inter> cEmpty = {}"
begin

lemma somechannotempty[simp]:"\<not>chDomEmpty(TYPE('c::somechan))"
  using chDom_def somechan_class.chan_notempty by fastforce

lemma somechandom:"chDom(TYPE('c::somechan)) 
                   = range(Rep::'c\<Rightarrow>channel)"
  by(simp add: chDom_def somechan_class.chan_notempty Diff_triv)

end

text\<open>Types of  @{class somechan} can transmit at least one message 
on every channel. Hence, we know @{thm somechannotempty} and 
@{thm somechandom}.\<close>

subsubsection\<open>Class emptychan\<close>
class emptychan = chan +
  assumes chan_empty:"(range Rep) \<subseteq> cEmpty" 
begin

lemma emptychanempty[simp]:"chDomEmpty(TYPE('c::emptychan))"
  by (simp add: chDom_def emptychan_class.chan_empty)

end
text\<open>Types of @{class emptychan} can not transmit any message on any 
channel. Hence, the Domain is empty @{thm emptychanempty}.\<close>



section %invisible\<open> rep abs chan lemmata \<close>
default_sort %invisible chan

lemma repinrange[simp]:"Rep (c::'c) = x 
                        \<Longrightarrow> x\<in> range(Rep::'c \<Rightarrow> channel)"
  by blast

lemma chan_eq[simp]:"Rep (c::'c) = x \<Longrightarrow> x\<in> range(Rep::'d\<Rightarrow>channel) 
                        \<Longrightarrow> Rep((Abs::channel \<Rightarrow> 'd)(Rep c)) = x"
  by (simp add: f_inv_into_f)

lemma cempty_rule[simp]:assumes"chDomEmpty(TYPE('c))"
  shows"Rep (c::'c) \<in> cEmpty"
  using assms chan_botsingle chDom_def by blast

lemma cnotempty_rule[simp]:assumes"\<not>chDomEmpty(TYPE('c))"
  shows"Rep (c::'c) \<notin> cEmpty"
  using assms chan_botsingle chDom_def by blast

lemma cnotempty_cdom[simp]:assumes"\<not>chDomEmpty(TYPE('c))"
  shows"Rep (c::'c) \<in> chDom(TYPE('c))"
  using assms by (simp add: chDom_def)

lemma cdom_notempty[simp]:assumes"c \<in>chDom TYPE('c)"
  shows" c \<notin> cEmpty"
  using assms by (simp add: chDom_def)

lemma notcdom_empty[simp]:assumes"Rep (c::'c) \<notin>chDom TYPE('c)"
  shows" Rep c \<in> cEmpty"
  using assms by (simp add: chDom_def)

lemma chdom_in: fixes c::"'cs::chan"
  assumes "chDom TYPE('cs) \<noteq> {}"
    shows "Rep c \<in> chDom TYPE('cs)"
  by (metis Diff_eq_empty_iff Diff_triv assms chDom_def 
      chan_botsingle rangeI)


declare %invisible[[show_types]]
declare %invisible[[show_consts]]

section \<open>Interconnecting Domain Types \label{sec:interdom}\<close>

text\<open>There are two interesting interconnections between domains. 
Intuitively, the union operator takes all channels from both domains 
and the minus operator only channels that are in the first, but not 
the second domain. But because we also have to check for channels 
from @{const cEmpty}, its not that trivial.\<close>

subsection\<open>Type union operator\<close>

text\<open>The union of two domains should contain every channel of each 
domain. So the union of two empty domains should also be empty. But 
because the type itself can never be empty, we again have to use 
channels in @{const cEmpty} to define the union.\<close> 
typedef ('c1,'c2) union (infixr "\<union>" 20) = 
        "if chDomEmpty TYPE ('c1) \<and>  chDomEmpty TYPE ('c2) 
            then cEmpty
            else chDom TYPE('c1) \<union> chDom TYPE('c2)" 
  apply(auto)
  using chDom_def by blast

text\<open>Because we interpret channels in @{const cEmpty} as no real 
channels, we can define the union of two empty domains as the 
channel set @{const cEmpty}. The next step is to instantiate the 
union of two members of class @{class chan} as a member of class 
@{class chan}. This is rather easy, because either the union results
in @{const cEmpty}, so there are only channels where no message can 
be transmitted, or it results in the union of the domains without 
channels from @{const cEmpty}. Hence, we can fulfill the class 
assumptions with the from "typdef" generated representation function 
@{const Rep_union}.\<close>

instantiation union :: (chan, chan) chan 
begin
  definition "Rep == Rep_union"
instance
  apply intro_classes
  apply auto
  apply (metis Rep_union Rep_union_def Un_iff cdom_notempty)
  by (simp add: Channel.Rep_union_def Rep_union_inject inj_on_def)
end

lemma union_range_empty:"chDomEmpty TYPE ('cs1) 
                         \<and>  chDomEmpty TYPE ('cs2) \<Longrightarrow> 
                    range (Rep_union::'cs1 \<union> 'cs2 \<Rightarrow> channel) = 
                    cEmpty"
  by (metis (mono_tags, lifting) type_definition.Rep_range 
      type_definition_union)

lemma union_range_union:"\<not>(chDomEmpty TYPE ('cs1) 
                         \<and>  chDomEmpty TYPE ('cs2)) \<Longrightarrow> 
                   range (Rep_union::'cs1 \<union> 'cs2 \<Rightarrow> channel) = 
                   chDom TYPE ('cs1) \<union> chDom TYPE('cs2)"
  by (smt type_definition.Rep_range type_definition_union)

text\<open>After the instantiation, class definition like the 
@{const chDom} function can be used. To verify the correctness of 
our definition we obtain the domain of the union type and proof, 
that it is indeed the union of the two sub domains.\<close>

theorem chdom_union[simp]:"chDom (TYPE('cs1 \<union> 'cs2)) = 
                           chDom (TYPE ('cs1)) \<union> chDom (TYPE('cs2))"
  apply(subst chDom_def)
  apply(simp_all add: Rep_union_def)
  using chDom_def union_range_empty union_range_union by auto

subsection\<open>Type minus operator\<close>

text\<open>Subtracting one domain from another results in the empty 
domain. But analogous to the union, our resulting type always 
contains channels. Subtracting a set from one of its subsets would 
result in an empty type. Hence, our result for this case is again 
@{const cEmpty}.\<close>

typedef ('c1,'c2) minus (infixr "-" 20) = 
        "(if chDom TYPE('c1) \<subseteq> chDom TYPE('c2) 
             then cEmpty
             else chDom TYPE('c1) - chDom TYPE('c2))" 
apply(cases "range Rep \<subseteq> range Rep", auto)
  using cempty_exists by blast+

text\<open>Instantiating the subtraction result of two @{class chan} types
is also in the class. The proof is, like above, straight forward.\<close>

instantiation minus :: (chan, chan) chan
begin
definition "Rep == Rep_minus"
instance
  apply intro_classes
   apply auto 
  apply (metis Diff_iff Rep_minus Rep_minus_def cdom_notempty)
  by (smt Rep_minus_def Rep_minus_inject injI)
end


lemma minus_range_empty:"chDom TYPE('cs1) \<subseteq> chDom TYPE('cs2) \<Longrightarrow> 
                 range (Rep_minus::'cs1 - 'cs2 \<Rightarrow> channel) = cEmpty"
  by (metis (mono_tags, lifting) type_definition.Rep_range 
      type_definition_minus)

lemma minus_range_minus:"\<not>(chDom TYPE('cs1) \<subseteq> chDom TYPE('cs2)) \<Longrightarrow> 
                   range (Rep_minus::'cs1 - 'cs2 \<Rightarrow> channel) = 
                   chDom TYPE('cs1) - chDom TYPE('cs2)"
  by (metis (mono_tags, lifting) type_definition.Rep_range 
      type_definition_minus)

text\<open>For verifying the minus operator we again take a look at the
resulting domain in the following theorem.\<close>

theorem chdom_minus[simp]:"chDom (TYPE('cs1 - 'cs2)) = 
                           chDom (TYPE ('cs1)) - chDom (TYPE('cs2))"
  apply(subst chDom_def)
  apply(simp_all add: Rep_minus_def)
  using Diff_Int_distrib2 minus_range_empty minus_range_minus 
  by auto
 
text\<open>If we subtract domain \<open>A\<close> from domain \<open>B\<close> the resulting domain 
should contain no channels from \<open>A\<close>.We also verify this correctness
property.\<close>

theorem [simp]:"chDom TYPE('cs1 - 'cs2) \<inter> chDom TYPE ('cs2) = {}"
  by auto

(*<*)
end
(*>*)