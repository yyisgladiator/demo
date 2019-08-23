theory SPS

imports spf.SPFcomp
begin



subsection \<open>SPS \label{sec:sps}\<close>

text\<open>The behaviour of under-specified or nondeterministic components
can often not be modeled by a single \gls{spf} but by a set of 
\Gls{spf}. Similar to the \gls{spf} type, we define \gls{sps} type 
as a type synonym.\<close> 

type_synonym ('I,'O) SPS = "('I,'O) SPF set"

(* TODO: move *)
definition spfIO::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) \<Rightarrow> ('I1\<^sup>\<Omega> \<times> 'O1\<^sup>\<Omega>) set" where
"spfIO spf = {(sb, spf\<cdot>sb) | sb. True}"

definition spsIO::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I1\<^sup>\<Omega> \<times> 'O1\<^sup>\<Omega>) set" where
"spsIO sps = {(sb, spf\<cdot>sb) | sb spf. spf\<in>sps}"

definition spsComplete ::"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set" where
"spsComplete sps = {spf . spfIO spf \<subseteq> spsIO sps}"


subsection \<open>I/O-Behaviour\<close>
lemma spsio_empty[simp]: "spsIO {} = {}"
  unfolding spsIO_def
  by blast

subsection \<open>Completion\<close>

lemma spscomplete_belowI: 
  assumes "\<And>spf sb. spf\<in>S1 \<Longrightarrow> \<exists>spf2 \<in> S2. spf\<cdot>sb = spf2\<cdot>sb"
  shows "S1 \<subseteq> spsComplete S2"
  unfolding spsComplete_def spsIO_def spfIO_def
  apply auto
  using assms by auto

lemma spscomplete_below: "sps \<subseteq> spsComplete sps"
  using spscomplete_belowI by auto

lemma spscomplete_set: "spsComplete sps = {spf. \<forall>sb. \<exists>spf2\<in>sps. spf\<cdot>sb = spf2\<cdot>sb}"
  unfolding spsComplete_def spsIO_def spfIO_def
  apply auto
  by auto

lemma spscomplete_complete [simp]: "spsComplete (spsComplete sps) = spsComplete sps"
  unfolding spscomplete_set apply auto
  by metis

lemma spscomplete_mono: assumes "sps1 \<subseteq> sps2"
  shows "spsComplete sps1 \<subseteq> spsComplete sps2"
  apply(rule spscomplete_belowI)
  unfolding spscomplete_set
  apply (auto)
  by (meson assms in_mono)

lemma spscomplete_io: "spsIO (spsComplete sps) = spsIO sps"
  unfolding spscomplete_set spsIO_def
  apply auto
  by auto

lemma spscomplete_empty[simp]: "spsComplete {} = {}"
  unfolding spscomplete_set by auto

lemma spscomplete_one[simp]: "spsComplete {f} = {f}"
  unfolding spscomplete_set apply auto
  by (simp add: cfun_eqI)

lemma spscomplete_univ[simp]: "spsComplete UNIV = UNIV"
  by (simp add: spscomplete_below top.extremum_uniqueI)


subsection\<open>General Composition of SPSs\<close>

text\<open>With our general composition operator for \Gls{spf} we can also
define the general composition operator for \Gls{sps}. It composes
every combination of \Gls{spf} possible from both input \Gls{sps}.\<close> 

definition spsComp::
"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set \<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set \<Rightarrow> ( 'E\<^sup>\<Omega> \<rightarrow> 'F\<^sup>\<Omega>) set"  where
"spsComp F G = {f \<otimes>\<^sub>\<star> g | f g. f\<in>F \<and> g\<in>G }"


abbreviation spsComp_abbr (infixr "\<Otimes>\<^sub>\<star>" 70) where 
"sps1 \<Otimes>\<^sub>\<star> sps2 \<equiv> spsComp sps1 sps2"

text\<open>Hence, we restrict the signature of our general composition 
operator to always obtain a \gls{sps} with desired input and output
domains.\<close>

abbreviation genComp_nomabbr::
"('I1\<^sup>\<Omega> \<rightarrow> 'O1\<^sup>\<Omega>) set\<Rightarrow> ('I2\<^sup>\<Omega> \<rightarrow> 'O2\<^sup>\<Omega>) set
 \<Rightarrow> ((('I1 \<union> 'I2) - ('O1 \<union> 'O2))\<^sup>\<Omega> \<rightarrow> ('O1 \<union> 'O2)\<^sup>\<Omega>) set" 
(infixr "\<Otimes>" 70) where "sps1 \<Otimes> sps2 \<equiv> spsComp sps1 sps2"




theorem spscomp_praedicate: 
      fixes P::"'I1\<^sup>\<Omega> \<Rightarrow> 'O1\<^sup>\<Omega> \<Rightarrow> bool"
        and H::"'I2\<^sup>\<Omega> \<Rightarrow> 'O2\<^sup>\<Omega> \<Rightarrow> bool"
      assumes "chDom TYPE ('O1) \<inter> chDom TYPE ('O2) = {}"
      shows  "{p . \<forall>sb. P sb (p\<cdot>sb)} \<Otimes> {h . \<forall>sb. H sb (h\<cdot>sb)} \<subseteq>   
            {g. \<forall>sb. 
                  let all = sb \<uplus> g\<cdot>sb in 
                    P (all\<star>) (all\<star>) \<and> H (all\<star>) (all\<star>)
            }"
  apply (auto simp add: spsComp_def Let_def)
  apply (simp add: spfcomp_extract_l)
  apply (simp add: assms spfcomp_extract_r)
  done
(* TODO: ähnliches Lemma mit spsIO *)


lemma spscomp_praedicate2: 
      fixes P::"'I1\<^sup>\<Omega> \<Rightarrow> 'O1\<^sup>\<Omega> \<Rightarrow> bool"
        and H::"'I2\<^sup>\<Omega> \<Rightarrow> 'O2\<^sup>\<Omega> \<Rightarrow> bool"
      assumes "chDom TYPE ('O1) \<inter> chDom TYPE ('O2) = {}"
      shows  "  
            {g. \<forall>sb. 
                  let all = sb \<uplus> g\<cdot>sb in 
                    P (all\<star>) (all\<star>) \<and> H (all\<star>) (all\<star>)
            } \<subseteq> spsComp {p . \<forall>sb. P sb (p\<cdot>sb)} {h . \<forall>sb. H sb (h\<cdot>sb)}" (is "?LHS \<subseteq> ?RHS")
  oops
(*
proof 
  fix g
  assume "g\<in>?LHS"
  hence "\<And>sb. P ((sb\<uplus>g\<cdot>sb)\<star>) ((sb\<uplus>g\<cdot>sb)\<star>)"
    by (metis (mono_tags, lifting) mem_Collect_eq)
  have "\<exists>p h. p\<otimes>h = g" oops*)
(*  from this obtain p h where "p\<otimes>h = g" by auto
  have "\<And>sb. P (sb) (p\<cdot>sb)" oops *)
(*  show "g\<in>?RHS" oops *)

(* Gegenbeispiel ... soweit ich sehe:
    P = H = "ist schwachkausal"
    bleibt nicht unter der feedbackkomposition erhalten *)


lemma "(spsComplete sps1) \<Otimes>\<^sub>\<star> (spsComplete sps2) = spsComplete (sps1 \<Otimes>\<^sub>\<star> sps2)"
  oops

end
