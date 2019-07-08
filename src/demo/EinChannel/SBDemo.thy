theory SBDemo

imports bundle.SB sbElemDemo

begin

section \<open>SB examples\<close>
text \<open>This Theory gives a few examples for SB. First we will show how a SB can be defined, later we 
      also test some SB functions. Some of these functions will also use sbElems.\<close>

subsection\<open>sbElem definition\<close>

lift_definition inSB::"inChan\<^sup>\<Omega>"is
"((\<lambda>c. fix\<cdot>(\<Lambda> s. (\<up>1) \<bullet> s)))"
  apply(auto simp add: sb_well_def sValues_def)
  apply(subgoal_tac "Rep c \<in>range (Rep::inChan \<Rightarrow>channel)")
  apply simp
  by blast

text \<open>inSB has a infinite stream of 1s on its channels.\<close>


lift_definition emptySB::"emptychan\<^sup>\<Omega>"is
"((\<lambda>c. \<epsilon>))"
  by(auto simp add: sb_well_def sValues_def)

subsection\<open>SB function tests\<close>

text \<open>First we take a look at the sbECons function, that prepends an sbElem to a SB.\<close>
lemma sbecons_none_test:"sbElemNone \<bullet>\<^sup>\<surd> (emptySB) = emptySB"
  apply(simp add: sbecons_insert sbe2sb_insert sbElemNone.rep_eq emptySB.rep_eq sbgetch_insert2 sbconc_insert)
  by (simp add: Rep_sb_strict emptySB.abs_eq)

text \<open>If we assume that the ctype of all channels is empty, we now that there can only be the None
      sbElem and the empty SB \<open>\<bottom> \<close>. Hence, prepending the None sbElem to a SB results in \<open>\<bottom> \<close>.\<close>
lemma sbecons_none_test2:"sbElemNone \<bullet>\<^sup>\<surd> (emptySB) = \<bottom>"
  apply(simp add: sbecons_insert sbe2sb_insert sbElemNone.rep_eq emptySB.rep_eq sbgetch_insert2 sbconc_insert)
  by (simp add: Rep_sb_inverse)

text \<open>The sbGetCh function retrieves the stream of a channel.\<close>
lemma "(inSB) \<^enum> (c::inChan) = fix\<cdot>(\<Lambda> s. \<up>1 \<bullet> s)"
  by(simp add: sbgetch_insert2 inSB.rep_eq)

text \<open>Now we take a look at the sbUnion function. The result of the union of the same SB is the SB
      itself.\<close>
lemma "sbUnion\<cdot>someSB\<cdot>someSB = someSB"
  by simp

text \<open>But if the union output type is different from the input type, the union of the same SB is
      equivalent to converting the input type to the output type.\<close>

lemma "inSB \<uplus> inSB = (inSB\<star>)"
  by simp

(*TODO: More tests*)