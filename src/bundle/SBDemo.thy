theory SBDemo

imports SB sbElemDemo

begin
default_sort chan
declare[[show_types]]
section \<open>SB examples\<close>
text \<open>This Theory gives a few examples for SB. First we will show how a SB can be defined, later we 
      also test some SB functions. Some of these functions will also use sbElems.\<close>

subsection\<open>sbElem definition\<close>

definition someSB::"'ch\<^sup>\<Omega>"where
"someSB = Abs_sb((\<lambda>c. SOME s. sValues s \<subseteq> ctype (Rep c)))"

text \<open>someSB is a SB, that has a M stream s on every channel. Every element of stream s also has to
      be in the ctype of its channel. This is checked with the function sValues, that returns a set
      of all elements in a stream. Because sValues of \<open> \<epsilon> \<close> is the empty set, there always exists a
      stream where every of its element is in the ctype of its channel.\<close>

lemma somesb_well:"sb_well ((\<lambda>c::'c. SOME s. sValues s \<subseteq> ctype (Rep c)))"
proof-
  have eps_well:"\<forall>c::'c. sValues \<epsilon> \<subseteq> ctype (Rep c)"
    by(simp add: sValues_def)
  then show ?thesis
    apply(simp add: sb_well_def)
    using eps_well tfl_some by metis
qed

subsection\<open>SB function tests\<close>

text \<open>First we take a look at the sbECons function, that prepends an sbElem to a SB.\<close>
lemma sbecons_none_test:"chIsEmpty TYPE('c) \<Longrightarrow> sbElemNone \<bullet>\<^sup>\<surd> (someSB::'c\<^sup>\<Omega>) = someSB"
  by simp
text \<open>If we assume that the ctype of all channels is empty, we now that there can only be the None
      sbElem and the empty SB \<open>\<bottom> \<close>. Hence, prepending the None sbElem to a SB results in \<open>\<bottom> \<close>.\<close>
lemma sbecons_none_test2:"chIsEmpty TYPE('c) \<Longrightarrow> sbElemNone \<bullet>\<^sup>\<surd> (someSB::'c\<^sup>\<Omega>) = \<bottom>"
  by simp

text \<open>The sbGetCh function retrieves the stream of a channel.\<close>
lemma "(someSB::'c\<^sup>\<Omega>) \<^enum> (c::'c) = (SOME s. sValues s \<subseteq> ctype (Rep c))"
  by(simp add: sbgetch_insert someSB_def Abs_sb_inverse somesb_well)

text \<open>Now we take a look at the sbUnion function. The result of the union of the same SB is the SB
      itself.\<close>
lemma "(sbUnion::'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>)\<cdot>someSB\<cdot>someSB = someSB"
  by simp

text \<open>But if the union output type is different from the input type, the union of the same SB is
      equivalent to converting the input type to the output type.\<close>

lemma "(sbUnion::'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega> \<rightarrow> 'e\<^sup>\<Omega>)\<cdot>someSB\<cdot>someSB = (sbConvert::'c\<^sup>\<Omega> \<rightarrow> 'e\<^sup>\<Omega>)\<cdot>someSB"
  by simp

(*TODO: More tests*)

end