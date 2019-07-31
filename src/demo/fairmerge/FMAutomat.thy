theory FMAutomat

imports automaton.ndAutomaton automaton.dAutomaton_causal fmAutomat_inc

begin

setup_lifting type_definition_ndAutomaton

fun dAfm_case::"bool \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat\<times> nat) \<Rightarrow> (S_fm \<times> nat)"where
"dAfm_case True  n [] l2 (nat1,nat2) = (S True  n []          (l2@[nat2]), nat1)"|
"dAfm_case False n l1 [] (nat1,nat2) = (S False n (l1@[nat1]) []         , nat2)"|

"dAfm_case True  n (nhd#l1) l2       (nat1,nat2) = (S True  n (l1@[nat1]) (l2@[nat2]),nhd)"|
"dAfm_case False n l1       (nhd#l2) (nat1,nat2) = (S False n (l1@[nat1]) (l2@[nat2]),nhd)"

(*FM automaton*)
fun dAfm_transition::"S_fm \<Rightarrow> (nat\<times> nat) \<Rightarrow> (S_fm \<times> nat)set"where
"dAfm_transition (S bool 0       buf1 buf2) input = {dAfm_case (\<not>bool) n buf1 buf2 input | n. True} "|
"dAfm_transition (S bool (Suc n) buf1 buf2) input = {dAfm_case bool    n buf1 buf2 input}"

definition fairmergetransition::"(S_fm \<Rightarrow> inFM\<^sup>\<surd> \<Rightarrow> ((S_fm \<times> outFM\<^sup>\<Omega>) set))"where
"fairmergetransition state insbe = ( let Set = (dAfm_transition state (fmInSBE.getter(insbe))) in
                                   (\<lambda>e. (fst e, fmOutSB.setter(\<up>(snd e))))` Set)"

definition fairmergeinit::"(S_fm \<times> outFM\<^sup>\<Omega>) set" where
"fairmergeinit = {(S bool n [] [], \<bottom>) | bool n. True}"

definition FairMerge::"(S_fm,inFM,outFM) ndAutomaton_incomplete" where
"FairMerge = (|ndaiTransition = fairmergetransition, ndaiInitConfig = fairmergeinit|)"

lift_definition FairMergelift::"(S_fm,inFM,outFM) ndAutomaton" is
"(fairmergetransition, fairmergeinit)"
  apply auto
  apply(simp add: fairmergetransition_def)
  apply(case_tac state;case_tac x1;case_tac x2;case_tac x3;case_tac x4,auto)
  apply (metis (mono_tags)old.prod.exhaust)+
  by(simp add: fairmergeinit_def,auto)

end