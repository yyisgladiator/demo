theory dADemo

imports dAutomatonsemv3

begin

section \<open> flasher port chans \<close>

typedef botChan ="{SOME c. c\<in>cEmpty}"
  by simp

typedef flasherPortIn = "{c1}"
  apply auto
  done


typedef flasherPortOut = "{c2}"
  apply auto
  done

instantiation flasherPortIn::chan
begin
definition "Rep = Rep_flasherPortIn"
instance
  apply(standard)
  apply (smt Int_lower1 Rep_flasherPortIn_def inf.orderI subset_singletonD type_definition.Rep_range type_definition_flasherPortIn)
   by (simp add: Rep_flasherPortIn_def Rep_flasherPortIn_inject inj_on_def)
end

instance flasherPortIn::finite
  apply(intro_classes)
  apply (subst UNIV_def)
  by (metis (full_types) Abs_flasherPortIn_cases Collect_const ex_new_if_finite finite.emptyI finite_insert insert_iff singletonD)

instantiation flasherPortOut::chan
begin
definition "Rep = Rep_flasherPortOut"
instance
  apply(standard) 
  apply (smt Int_lower1 Rep_flasherPortOut_def inf_commute subset_singletonD type_definition.Rep_range type_definition_flasherPortOut)
  by (smt Rep_flasherPortOut_def Rep_flasherPortOut_inject injI)
end

instantiation botChan::chan
begin
definition "Rep = Rep_botChan"
instance
  apply(standard)
  apply (smt Int_lower1 Rep_botChan_def inf_commute subset_singletonD type_definition.Rep_range type_definition_botChan)
  by (simp add: Rep_botChan_def Rep_botChan_inject inj_on_def)
end

lift_definition Nonesbe::"botChan sbElem" is (*Does not work for undefined ctype*)
"None"
  apply(simp)
  using Rep_botChan Rep_botChan_def sorry

section \<open>flasher states\<close>

datatype flasherState = S

section \<open>flasher automaton definition\<close>

definition flasherAutomatonw::"(flasherState,flasherPortIn,flasherPortOut,botChan) dAutomaton_weak" where
"flasherAutomatonw =(| dawTransition =(\<lambda>s sbe. (s,Abs_sbElem(Some (\<lambda>c. sbegetch c sbe)))), 
                 dawInitState = S, dawInitOut = Nonesbe |)"

definition flasherAutomatons::"(flasherState,flasherPortIn,flasherPortOut) dAutomaton_strong" where
"flasherAutomatons =(| dawTransition =(\<lambda>s sbe. (s,Abs_sbElem(Some (\<lambda>c. sbegetch c sbe)))), 
                 dawInitState = S, dawInitOut = Abs_sbElem(Some (\<lambda>c. B True)) |)"

section \<open> flasher automat to spf\<close>

definition flasherspfw::"(flasherPortIn,flasherPortOut)spfw"where
"flasherspfw = semantik_weak(flasherAutomatonw)"

definition flasherspfs::"(flasherPortIn,flasherPortOut)spfs"where
"flasherspfs = semantik_strong(flasherAutomatons)"

lemma dawinitout_genaut:"daInitOut (daw2da auts) =  sbe2sb\<cdot>(dawInitOut auts)"
  by(simp add: daw2da_def)

lemma semantik_strong_head:"\<exists>sb. (Rep_spfw (Rep_spfs (semantik_strong auts)))\<cdot>insb = sbe2sb\<cdot>(dawInitOut auts) \<bullet>\<^sup>\<Omega> sb"
  apply(simp add: semantik_strong_def daSem_def dawinitout_genaut)
  sorry

theorem flasherhead:assumes "B True \<in> ctype c2" shows"shd (((Rep_spfw (Rep_spfs flasherspfs))\<cdot>sb) \<^enum> (Abs c2)) = B True"
  apply(simp add: flasherspfs_def)
  apply(insert semantik_strong_head[of flasherAutomatons sb])
  apply(simp add: flasherAutomatons_def)
  apply auto
  oops

end