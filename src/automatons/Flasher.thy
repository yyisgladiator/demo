theory Flasher

imports "../bundle/demo/EinChannel/EinChannel"
begin

(*State datatype*)
datatype S = Single

instance S::countable
  by(countable_datatype)


(*And component channel types*)

typedef emptychan="{c3}"
  by simp

instantiation emptychan::"{chan,finite}"
begin
definition "Rep = Rep_emptychan"
instance
  apply(intro_classes)
  apply simp
  using Rep_emptychan_def type_definition.Rep_range type_definition_emptychan apply fastforce
  apply (simp add: Rep_emptychan_def Rep_emptychan_inject inj_on_def)
  sorry
end


typedef inAnd="{cin1,cin2}"
  by auto
typedef outAnd = "{cout}"
  by auto

instantiation inAnd::"{chan,finite}"
begin
definition "Rep = Rep_inAnd"
instance
  apply(standard)
  apply(auto simp add: Rep_inAnd_def)
  apply (metis Rep_inAnd channel.distinct(19) channel.distinct(21) insertE singletonD)
  apply (meson Rep_inAnd_inject injI)
  sorry
end

definition "Andin1 \<equiv> Abs_inAnd cin1"
definition "Andin2 \<equiv> Abs_inAnd cin2"

free_constructors inAnd for "Andin1"  | "Andin2"
   apply auto
  unfolding Andin1_def Andin2_def
  apply (metis Rep_inAnd Rep_inAnd_inverse empty_iff insert_iff)
  by (simp add: Abs_inAnd_inject)

definition "Andout \<equiv> Abs_outAnd cout"


instantiation outAnd::"{chan,finite}"
begin
definition "Rep = Rep_outAnd"
instance
  apply(standard)
  apply(auto simp add: Rep_outAnd_def)
  apply (metis Rep_outAnd singletonD)
   apply (meson Rep_outAnd_inject injI)
  sorry
end

free_constructors outAnd for "Andout"
  unfolding Andout_def
  using Abs_outAnd_cases by auto


(*in Automaton channel types*)
typedef inNot="{cout}"
  by auto

typedef outNot = "{cin2}"
  by auto

instantiation inNot::"{chan,finite}"
begin
definition "Rep = Rep_inNot"
instance
  apply(standard)
  apply(auto simp add: Rep_inNot_def)
  apply (metis Rep_inNot singletonD)
  apply (meson Rep_inNot_inject injI)
  sorry
end

definition "Notin \<equiv> Abs_inNot cout"

free_constructors inNot for "Notin"
  by (metis(full_types) Abs_inNot_cases singletonD)

instantiation outNot::"{chan,finite}"
begin
definition "Rep = Rep_outNot"
instance
  apply(standard)
  apply(auto simp add: Rep_outNot_def)
  apply (metis Rep_outNot singletonD)
  apply (meson Rep_outNot_inject injI)
  sorry
end

definition "Notout \<equiv> Abs_outNot cin2"

free_constructors outNot for "Notout"
  by (metis(full_types) Abs_outNot_cases singletonD)

(*interpretations And*)

fun inAndChan::"('nat::type \<Rightarrow> 'a::type) \<Rightarrow> ('bool::type \<Rightarrow> 'a) \<Rightarrow>('nat\<times>'bool) \<Rightarrow> inAnd \<Rightarrow> 'a" where
"inAndChan Cc1 Cc2 (port_c1, port_c2) Andin1 = Cc1 port_c1" |
"inAndChan Cc1 Cc2 (port_c1, port_c2) Andin2 = Cc2 port_c2"

fun outAndChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outAnd \<Rightarrow> 'a" where
"outAndChan Cc1 bool Andout = Cc1 bool"

abbreviation "buildAndinSBE \<equiv> inAndChan \<B> \<B>" 

abbreviation "buildAndoutSBE \<equiv> outAndChan \<B>" 

interpretation andInSBE: sbeGen "buildAndinSBE"
  sorry

interpretation andOutSBE: sbeGen "buildAndoutSBE"
  sorry


(*interpretations Not*)

fun inNotChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> inNot \<Rightarrow> 'a" where
"inNotChan Cc1 bool Notin = Cc1 bool"

fun outNotChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outNot \<Rightarrow> 'a" where
"outNotChan Cc1 bool Notout = Cc1 bool"


abbreviation "buildNotinSBE \<equiv> inNotChan \<B>" 

abbreviation "buildNotoutSBE \<equiv> outNotChan \<B>" 

interpretation notInSBE: sbeGen "buildNotinSBE"
  sorry

interpretation notOutSBE: sbeGen "buildNotoutSBE"
  sorry


(*And automaton*)
fun dAand_transitionH::"S \<Rightarrow> (bool\<times> bool) \<Rightarrow> (S \<times> bool)"where
"dAand_transitionH S (bool1,bool2) = (S,(bool1 \<and> bool2))"

definition dAnd_transition::"S \<Rightarrow> inAnd\<^sup>\<surd> \<Rightarrow> (S\<times> outAnd\<^sup>\<surd>)"where
"dAnd_transition S insbe = (let (nextState, output) = dAand_transitionH S (sbeGen.getter buildAndinSBE insbe) in
                           (nextState, sbeGen.setter buildAndoutSBE output)) "

definition dAand::"(S, inAnd, outAnd,emptychan) dAutomaton_weak"where
"dAand = (| dawTransition =dAnd_transition,
                 dawInitState = Single , dawInitOut = Abs_sbElem(None) |)"

(*And Sem*)

definition andStep::"(S \<Rightarrow> (inAnd\<^sup>\<Omega> \<rightarrow> outAnd\<^sup>\<Omega>))"where
"andStep = dawStateSem dAand"

definition andSpf::"(inAnd\<^sup>\<Omega> \<rightarrow> outAnd\<^sup>\<Omega>)"where
"andSpf = andStep (dawInitState dAand)"

interpretation and_smap:smapGen "dAand" "buildAndinSBE" "buildAndoutSBE"
  sorry

lemma andingetset_eq:"andInSBE.getterSB\<cdot>(andInSBE.setterSB\<cdot>s) = s"
  using andInSBE.c_empty andInSBE.getset_eq by blast

lemma andoutgetset_eq:"andOutSBE.getterSB\<cdot> (andOutSBE.setterSB\<cdot>s) = s"
  using andOutSBE.c_empty andOutSBE.getset_eq by auto

lemma "andOutSBE.getterSB\<cdot>(andStep state\<cdot>(andInSBE.setterSB\<cdot>input)) = (smap and_smap.smapTransition\<cdot>(input))"
  by(simp add: andStep_def and_smap.daut2smap andingetset_eq andoutgetset_eq)

lemma "andOutSBE.getterSB\<cdot>(andStep Single\<cdot>(andInSBE.setterSB\<cdot>(\<up>(x,y)))) = \<up>(x\<and>y)"
  sorry


(*Not automaton*)
fun dAnot_transitionH::"S \<Rightarrow> (bool) \<Rightarrow> (S \<times> bool)"where
"dAnot_transitionH S (bool) = (S,(\<not>bool))"

definition dNot_transition::"S \<Rightarrow> inNot\<^sup>\<surd> \<Rightarrow> (S\<times> outNot\<^sup>\<surd>)"where
"dNot_transition S insbe = (let (nextState, output) = dAnot_transitionH S (sbeGen.getter buildNotinSBE insbe) in
                           (nextState, sbeGen.setter buildNotoutSBE output)) "

definition dAnot::"(S, inNot, outNot) dAutomaton_strong"where
"dAnot = (| dawTransition =dNot_transition,
                 dawInitState = Single, dawInitOut = sbeGen.setter buildNotoutSBE True|)"


(*And Sem*)
definition notStep::"(S \<Rightarrow> (inNot\<^sup>\<Omega> \<rightarrow> outNot\<^sup>\<Omega>))"where
"notStep = dawStateSem dAnot"

definition notSpf::"(inNot\<^sup>\<Omega> \<rightarrow> outNot\<^sup>\<Omega>)"where
"notSpf = notStep (dawInitState dAnot)"


interpretation not_sscanl:smapGen "dAnot" "buildNotinSBE" "buildNotoutSBE"
  sorry


(*Composition*)

definition flasherComp::"((inAnd\<union>inNot) - (outAnd \<union> outNot))\<^sup>\<Omega> \<rightarrow>(outAnd \<union> outNot)\<^sup>\<Omega>"where
"flasherComp = genComp\<cdot>andSpf\<cdot>notSpf"

lemma flasherhd:"\<exists>rest. flasherComp\<cdot>(sbe \<bullet>\<^sup>\<surd> sb) = sbeConvert(sbeGen.setter buildAndoutSBE (True \<and> sbeGen.getter buildNotinSBE (sbeConvert sbe)))\<bullet>\<^sup>\<surd> rest"
  sorry
end