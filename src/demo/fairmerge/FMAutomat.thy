theory FMAutomat

imports automaton.ndAutomaton automaton.dAutomaton_causal fmAutomat_inc

begin

setup_lifting type_definition_ndAutomaton

(*FM automaton*)
fun dAfm_transition::"S_fm \<Rightarrow> (bool\<times> bool) \<Rightarrow> (S_fm \<times> bool)set"where
"dAfm_transition (S True 0 [] buf2) (bool1,bool2) = {((S (False) next [] (buf2@[bool2])),(bool1)) | next. True} "|
"dAfm_transition (S False 0 buf1 []) (bool1,bool2) = {((S (True) next (buf1@[bool1]) []),(bool2)) | next. True} "|
"dAfm_transition (S True 0 buf1 buf2) (bool1,bool2) = {((S (False) next ((tl buf1)@[bool1]) (buf2@[bool2])),(hd buf1)) | next. True} "|
"dAfm_transition (S False 0 buf1 buf2) (bool1,bool2) = {((S (True) next (buf1@[bool1]) ((tl buf2)@[bool2])),(hd buf2)) | next. True} "|
"dAfm_transition (S True n [] buf2) (bool1,bool2) = {((S (True) (n-1)  [] (buf2@[bool2])),(bool1))}"|
"dAfm_transition (S False n buf1 []) (bool1,bool2) = {((S (False) (n-1) (buf1@[bool1]) []),(bool2))}"|
"dAfm_transition (S True n buf1 buf2) (bool1,bool2) = {((S (True) (n-1) ((tl buf1)@[bool1]) (buf2@[bool2])),(hd buf1))}"|
"dAfm_transition (S False n buf1 buf2) (bool1,bool2) = {((S (False) (n-1) ((buf1)@[bool1]) ((tl buf2)@[bool2])),(hd buf2))}"

definition fairmergetransition::"(S_fm \<Rightarrow> inFM\<^sup>\<surd> \<Rightarrow> ((S_fm \<times> outFM\<^sup>\<surd>) set))"where
"fairmergetransition state insbe = ( let Set = (dAfm_transition state (fmInSBE.getter(insbe))) in
                                   (\<lambda>e. (fst e, fmOutSBE.setter(snd e)))` Set)"

definition fairmergeinit::"(S_fm \<times> outFM\<^sup>\<Omega>) set" where
"fairmergeinit = {(S bool n [] [], \<bottom>) | bool n. True}"

lift_definition FairMerge::"(S_fm,inFM,outFM) ndAutomaton" is
"(undefined, fairmergeinit)" (*fairmergetransition works with sbElem instead of sb*)
  sorry

end