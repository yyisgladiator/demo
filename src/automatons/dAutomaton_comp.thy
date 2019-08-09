(*<*)(*:maxLineLen=68:*)
theory dAutomaton_comp
  imports dAutomaton_causal (*SPF_comp*)
begin
(*>*)
section \<open>Automaton Composition\<close>

subsection \<open>Composition of strong automatons\<close>

subsubsection \<open>Definition\<close>

(*TODO?:'incomp = ('in1 \<union> 'in2), 'outcomp = ('out1 \<union> 'out2),'buf = ('out1 \<union> 'out2) - ('in1 \<union> 'in2)*)

fun compTransition::"('s1::type \<Rightarrow> 'in1\<^sup>\<surd> \<Rightarrow> ('s1 \<times> 'out1\<^sup>\<surd>)) \<Rightarrow> ('s2::type \<Rightarrow> 'in2\<^sup>\<surd> \<Rightarrow> ('s2 \<times> 'out2\<^sup>\<surd>)) \<Rightarrow> (('s1\<times>'s2 \<times>'buf\<^sup>\<surd>) \<Rightarrow> 'incomp\<^sup>\<surd> \<Rightarrow> (('s1\<times>'s2 \<times>'buf\<^sup>\<surd>) \<times> 'outcomp\<^sup>\<surd>))"where
"compTransition t1 t2 (s1,s2,buf) sbe = (let (s1o,sbe1o) = (t1 s1 (sbeUnion sbe buf));
                                             (s2o,sbe2o) = (t2 s2 (sbeUnion sbe buf))  in
                                        ((s1o,s2o, sbeUnion sbe1o sbe2o), sbeUnion sbe1o sbe2o))"
text\<open>The function @{term compTransition} maps two Transitoinfunctions to there equivalent composed 
     Transitionfunction.\<close>

(*TODO:'incomp = ('in1 \<union> 'in2), 'outcomp = ('out1 \<union> 'out2), 'buf = ('out1 \<union> 'out2) - ('in1 \<union> 'in2)*)
definition daComp::"('s1::type,'in1,'out1)dAutomaton_strong \<Rightarrow> ('s2::type,'in2,'out2)dAutomaton_strong \<Rightarrow> (('s1\<times>'s2\<times>'buf\<^sup>\<surd>),'incomp,'outcomp)dAutomaton_strong" where
"daComp \<equiv> \<lambda>aut1 aut2. (| dawTransition = compTransition (dawTransition aut1) (dawTransition aut2), 
                        dawInitState =((dawInitState aut1),(dawInitState aut2), sbeUnion (dawInitOut aut1)(dawInitOut aut2)),
                        dawInitOut = sbeUnion(dawInitOut aut1) (dawInitOut aut2) |)"
text\<open>@{term daComp} composes two strong automatons. The State of the composed automaton has an 
     \<open>sbElem\<close> as a buffer. The buffer contains all elements on the internal channels of the
     automatons.\<close>

subsubsection\<open>Strong composition lemmas \<close>

lemma final_eval_autcomp:"semantik_strong(daComp aut1 aut2) \<sqsubseteq> spfcomp_s\<cdot>(semantik_strong aut1)\<cdot>(semantik_strong aut2)"
  oops

(*TODO: something else than Rep_spfs_fun\<cdot>(semantik_strong..) *)
lemma final_eval_autcomp_eq:assumes "sbLen sb = \<infinity>"
                            shows"(Rep_spfs_fun\<cdot>(semantik_strong(daComp aut1 aut2)))\<cdot>sb 
                                  = Rep_spfs_fun\<cdot>((spfcomp_s\<cdot>(semantik_strong aut1))\<cdot>(semantik_strong aut2))\<cdot>sb"
  oops

(*<*)
end
(*>*)