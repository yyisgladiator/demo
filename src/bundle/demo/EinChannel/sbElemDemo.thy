theory sbElemDemo

imports Channeldemo bundle.sbElem
begin
default_sort chan
declare[[show_types]]
section \<open>sbElem examples\<close>
text \<open>This Theory gives a few examples for sbElem. First we will show how sbElems can be defined,
      later we also test some sbElem functions.\<close>

subsection\<open>sbElem definition\<close>

lift_definition insbElem::"inChan\<^sup>\<surd>"is
"(Some(\<lambda>c. 1))"
  apply(auto)
  apply(subgoal_tac "Rep c \<in>range (Rep::inChan \<Rightarrow>channel)")
  using inchan_range
  apply auto[1]
  by (simp add: Rep_inChan_def)

text \<open>insbElem is a sbElem, that has an 1 on its channels.(In this case there is only one channel)\<close>

lift_definition sbElemNone::"emptychan\<^sup>\<surd>"is
"None"
  by simp

text \<open>sbElemNone represents the empty sbElem. 
      It only exists, iff the ctype of all its channels is empty. This is true for the 
      emptychan type.\<close>

subsection\<open>sbElem function tests\<close>

text \<open>Now we will test some functions with out defined sbElems.\<close>

text\<open>First we test the sbegetch function, that obtains the Element on a specific channel of the 
     sbElem. It indeed returns us the Element defined in the somesbElem definition.\<close>

lemma sbegetch_sbelemone:"sbegetch (c::inChan) insbElem = 1"
  by(simp add: sbegetch_def insbElem.rep_eq)

(*TODO: More tests*)


end