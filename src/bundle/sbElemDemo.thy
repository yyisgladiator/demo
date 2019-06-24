theory sbElemDemo

imports sbElem

begin
default_sort chan
declare[[show_types]]
section \<open>sbElem examples\<close>
text \<open>This Theory gives a few examples for sbElem. First we will show how sbElems can be defined,
      later we also test some sbElem functions.\<close>

subsection\<open>sbElem definition\<close>

definition somesbElem::"'ch\<^sup>\<surd>"where
"somesbElem = Abs_sbElem(Some(\<lambda>c. SOME m. m \<in> ctype (Rep c)))"

text \<open>somesbElem is a sbElem, that has an element m of M on every channel.
      Element m also has to be in ctype of its channel, else somesbElem is not sbElem_well. 
      chIsEmpty is True, iff the ctype of its channels is empty.\<close>

lemma somesbelem_well:"\<not>(chIsEmpty TYPE('c))\<Longrightarrow> sbElem_well (Some(\<lambda>c::'c. SOME m. m \<in> ctype (Rep c)))"
proof(simp add: chIsEmpty_def)
  assume ch_not_bot:"\<not> range (Rep::'c\<Rightarrow>channel) \<subseteq> cEmpty"
  then have "(range (Rep::'c\<Rightarrow>channel)) \<inter> cEmpty = {}"
    using chan_botsingle by blast
  text\<open> Because we know that the channels of tpye \<open>'c \<close>are not in cEmpty(from the assumption of the class
        chan), we can proof that there is at least one element in the ctype of channels in \<open>'c \<close>.\<close>
  then have "\<forall>c::'c. \<exists>m. m\<in>ctype (Rep c)"
    using cEmpty_def by force
  text\<open> Hence, somesbElem is sbElem_well.\<close>
  then show "\<forall>c::'c. (SOME m. m \<in> ctype (Rep c)) \<in> ctype (Rep c)"
    using some_in_eq by auto
qed

definition sbElemNone::"'ch\<^sup>\<surd>"where
"sbElemNone = Abs_sbElem None"


text \<open>sbElemNone represents the empty sbElem. 
      It only exists, iff the ctype of all its channels is empty. This holds, iff chIsEmpty of the
      sbElem channel type is True. It follows directly from the chIsEmpty definition.\<close>

lemma"chIsEmpty TYPE('c)\<Longrightarrow> sbElem_well (None::('c \<Rightarrow> M)option)"
  by(simp add: chIsEmpty_def)

subsection\<open>sbElem function tests\<close>

text \<open>Now we will test some functions with out defined sbElems.\<close>

text\<open>First we test the sbegetch function, that obtains the Element on a specific channel of the 
     sbElem. It indeed returns us the Element defined in the somesbElem definition.\<close>

lemma sbegetch_sbelemone:"\<not>(chIsEmpty TYPE('c)) \<Longrightarrow> sbegetch (c::'c) (somesbElem::'c\<^sup>\<surd>) = (SOME m. m \<in> ctype (Rep c))"
  apply(simp add: somesbElem_def sbegetch_def)
  apply(subst Abs_sbElem_inverse)
  using somesbelem_well apply auto[1]
  by simp

(*TODO: More tests*)


end