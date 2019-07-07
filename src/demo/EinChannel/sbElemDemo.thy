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




lift_definition mych_elem::"nat \<Rightarrow> nat \<Rightarrow> myChan\<^sup>\<surd>"is 
"\<lambda>as ar. Some (\<lambda>c. case c of port_as \<Rightarrow> as | _ \<Rightarrow> ar)"
  apply auto
  by (case_tac "c", auto)


lemma "sbegetch port_as (mych_elem as ar ) = as"
  apply(simp add: sbegetch_def mych_elem.rep_eq)
  by (metis Rep_myChan.simps(1) chan_inj inv_f_eq myChan.simps(3))

end