theory FMAutomat

imports automaton.ndAutomaton automaton.dAutomaton_causal fmAutomat_inc

begin

setup_lifting type_definition_ndAutomaton

fun dAfm_case::"bool \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat\<times> nat) \<Rightarrow> nat \<Rightarrow>(S_fm \<times> nat option)"where
"dAfm_case True  [] l2 (nat1, nat2) = (\<lambda>n. (S True  n []          (l2@[nat2]),Some nat1))"|
"dAfm_case False l1 [] (nat1, nat2) = (\<lambda>n. (S False n (l1@[nat1]) []         ,Some nat2))"|

"dAfm_case True  (nhd#l1) l2       (nat1, nat2) = (\<lambda>n. (S True  n (l1@[nat1]) (l2@[nat2]),Some nhd))"|
"dAfm_case False l1       (nhd#l2) (nat1, nat2) = (\<lambda>n. (S False n (l1@[nat1]) (l2@[nat2]),Some nhd))"


fun dAfm_case_option::"bool \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> (nat option\<times> nat option) \<Rightarrow> nat \<Rightarrow>(S_fm \<times> nat option)" where
"dAfm_case_option bool l1 l2 (Some nat1, Some nat2) = dAfm_case bool l1 l2 (nat1, nat2)"|

"dAfm_case_option bool [] [] (None            , None)      = (\<lambda>n. (S bool  n [] []        ,None     ))"|
"dAfm_case_option bool [] [] (Some nat1       , None)      = (\<lambda>n. (S True  n [] []        ,Some nat1))"|
"dAfm_case_option bool [] [] (None            , Some nat2) = (\<lambda>n. (S False n [] []        ,Some nat2))"|

"dAfm_case_option False (nhd#l1) [] (None     , None)      = (\<lambda>n. (S True  n l1          []          ,Some nhd ))"|
"dAfm_case_option True  (nhd#l1) l2 (None     , None)      = (\<lambda>n. (S True  n l1          l2          ,Some nhd ))"|
"dAfm_case_option False (nhd#l1) [] (Some nat1, None)      = (\<lambda>n. (S True  n (l1@[nat1]) []          ,Some nhd ))"|
"dAfm_case_option True  (nhd#l1) l2 (Some nat1, None)      = (\<lambda>n. (S True  n (l1@[nat1]) l2          ,Some nhd ))"|
"dAfm_case_option True  (nhd#l1) l2 (None     , Some nat2) = (\<lambda>n. (S True  n l1          (l2@[nat2]) ,Some nhd ))"|
"dAfm_case_option False l1       [] (None     , Some nat2) = (\<lambda>n. (S False n l1          []          ,Some nat2))"|

"dAfm_case_option True  [] (nhd#l2) (None     , None)      = (\<lambda>n. (S False n []          l2          ,Some nhd ))"|
"dAfm_case_option False l1 (nhd#l2) (None     , None)      = (\<lambda>n. (S False n l1          l2          ,Some nhd ))"|
"dAfm_case_option False l1 (nhd#l2) (Some nat1, None)      = (\<lambda>n. (S False n (l1@[nat1]) l2          ,Some nhd ))"|
"dAfm_case_option True  []  l2      (Some nat1, None)      = (\<lambda>n. (S True  n []          l2          ,Some nat1))"|
"dAfm_case_option True  [] (nhd#l2) (None     , Some nat2) = (\<lambda>n. (S False n []          (l2@[nat2]) ,Some nhd ))"|
"dAfm_case_option False l1 (nhd#l2) (None     , Some nat2) = (\<lambda>n. (S True  n l1          (l2@[nat2]) ,Some nhd ))"

(*FM automaton*)
fun dAfm_transition::"S_fm \<Rightarrow> (nat option\<times> nat option) \<Rightarrow> (S_fm \<times> nat option )set"where
"dAfm_transition (S bool 0       buf1 buf2) input = {(dAfm_case_option (\<not>bool) buf1 buf2 input) n | n. True} "|
"dAfm_transition (S bool (Suc n) buf1 buf2) input = {(dAfm_case_option bool    buf1 buf2 input) n}"

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