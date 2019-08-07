theory FMAutomat

imports automaton.eventAutomat automaton.dAutomaton_causal fmAutomat_inc

begin

section\<open>evenAutomat \<close>

datatype Single = Si bool nat

(*Setter for M_pure? Nondeterminism in last two cases necessary?*)
fun eventMT :: "Single \<Rightarrow> inFM \<Rightarrow> nat  \<Rightarrow> (Single \<times> outFM\<^sup>\<Omega>) set" where
"eventMT (Si True  0      ) FMin1 m  = { (Si False   i, fmOutSB.setter (\<up>(Some m))) | i. True}" |
"eventMT (Si True  (Suc n)) FMin1 m  = { (Si True    n, fmOutSB.setter (\<up>(Some m)))          }" |
"eventMT (Si False 0      ) FMin2 m  = { (Si True    i, fmOutSB.setter (\<up>(Some m))) | i. True}" |
"eventMT (Si False (Suc n)) FMin2 m  = { (Si False   n, fmOutSB.setter (\<up>(Some m)))          }" |
"eventMT (Si True  n      ) FMin2 m  = { (Si False   i, fmOutSB.setter (\<up>(Some m))) | i. True}" |
"eventMT (Si False n      ) FMin1 m  = { (Si True    i, fmOutSB.setter (\<up>(Some m))) | i. True}"


definition "eventMerge = eventAut (\<lambda> s c m_pure. eventMT s c (inv \<N> m_pure)) ({(Si bool n,\<bottom>)| bool n. True})"




section\<open>ugly transition function\<close>
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

section \<open>Broy specification\<close>
text\<open>Assumes that stream domains are disjoint, non-strict if we use timed streams\<close>
definition FM_broy::"('a::countable stream \<rightarrow> 'a stream \<rightarrow> 'a stream) set" where
"FM_broy = {f | f. \<forall>s1 s2. (#s1=\<infinity> \<and> #s2=\<infinity> \<and> (sValues\<cdot>s1 \<inter> sValues\<cdot>s2 = {})) 
            \<longrightarrow> (s1=(sValues\<cdot>s1) \<ominus> (f\<cdot>s1\<cdot>s2) \<and> s2=(sValues\<cdot>s2) \<ominus> (f\<cdot>s1\<cdot>s2))}"

text \<open>Case we want to merge nat and bool stream:\<close>

datatype NB= \<N> nat | \<B> bool

instance NB::countable
  by(countable_datatype)

definition FM_broynb::"(nat stream \<rightarrow> bool stream \<rightarrow> NB stream)set" where
"FM_broynb = {f | f. \<exists>g. \<forall>s1 s2. f\<cdot>s1\<cdot>s2 = g\<cdot>(smap \<N>\<cdot>s1)\<cdot>(smap \<B>\<cdot>s2) \<and> g \<in> FM_broy}"

lemma assumes "f\<in>FM_broynb" and "#s1 = \<infinity>" and "#s2 = \<infinity>" shows "(\<N> `(sValues\<cdot>s1)) \<ominus> (f\<cdot>s1\<cdot>s2) = smap \<N>\<cdot>s1"
  apply(insert assms, simp add: FM_broynb_def FM_broy_def,auto)
  apply(subgoal_tac "sValues\<cdot>(smap NB.\<N>\<cdot>s1)\<inter> sValues\<cdot>(smap NB.\<B>\<cdot>s2) = {}",auto)
  apply (metis slen_smap smap_sValues)
  by(auto simp add: smap_sValues)

lemma assumes "f\<in>FM_broynb" and "#s1 = \<infinity>" and "#s2 = \<infinity>" shows "(\<B> `(sValues\<cdot>s2)) \<ominus> (f\<cdot>s1\<cdot>s2) = smap \<B>\<cdot>s2"
  apply(insert assms, simp add: FM_broynb_def FM_broy_def,auto)
  apply(subgoal_tac "sValues\<cdot>(smap NB.\<N>\<cdot>s1)\<inter> sValues\<cdot>(smap NB.\<B>\<cdot>s2) = {}",auto)
  apply (metis slen_smap smap_sValues)
  by(auto simp add: smap_sValues)


fixrec
smerge :: "'a::countable stream \<rightarrow> 'a stream \<rightarrow> 'a stream"
where
"smerge\<cdot>\<bottom>\<cdot>l2 = \<bottom>"|
"smerge\<cdot>l1\<cdot>\<bottom> = \<bottom>"|
"smerge\<cdot>((up\<cdot>l1)&&ls1)\<cdot>((up\<cdot>l2)&&ls2) = (up\<cdot>l1)&&((up\<cdot>l2)&&(smerge\<cdot>ls1\<cdot>ls2))"

lemma "smerge\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>b \<bullet>bs) = \<up>a \<bullet> \<up>b \<bullet> (smerge\<cdot>as\<cdot>bs)"
  unfolding smerge_def
  sorry

lemma "snth (2*n) (smerge\<cdot>(s1)\<cdot>(s2)) = snth n s1"
  sorry

lemma "snth (2*n +1) (smerge\<cdot>(s1)\<cdot>(s2)) = snth (n+1) s2"
  sorry

lemma smerge_well1:"#s1 = \<infinity> \<Longrightarrow> #s2 = \<infinity> \<Longrightarrow> sValues\<cdot>s1 \<inter> sValues\<cdot>s2 = {} \<Longrightarrow> s1 = sValues\<cdot>s1 \<ominus> smerge\<cdot>s1\<cdot>s2"
  sorry

lemma smerge_well2:"#s1 = \<infinity> \<Longrightarrow> #s2 = \<infinity> \<Longrightarrow> sValues\<cdot>s1 \<inter> sValues\<cdot>s2 = {} \<Longrightarrow> s2 = sValues\<cdot>s2 \<ominus> smerge\<cdot>s1\<cdot>s2"
  sorry

lemma "\<exists>f. f\<in>FM_broy"
  apply(rule_tac x="smerge"in exI)
  by(simp add: FM_broy_def smerge_well1 smerge_well2)

section \<open>Rumpe specification\<close>

primrec Select:: "bool list \<Rightarrow> 'a::countable list \<Rightarrow> 'a list" where
"Select bs [] = []" |
"Select bs (x # xs) = (if hd bs then x # Select (tl bs) xs else Select (tl bs) xs)"

definition merge::"nat list \<times> nat list \<Rightarrow> nat list set"where
"merge \<equiv> \<lambda>(in1,in2). {s  | s. \<exists>org. in1 = Select org s \<and> in2 = Select (map Not org) s}"

datatype S_rum = s

fun Rum_transition::"S_rum \<Rightarrow> (nat list \<times> nat list) \<Rightarrow> (S_rum \<times> nat list)set"where
"Rum_transition s input = {(s,out) | out. out \<in> merge input}"

end