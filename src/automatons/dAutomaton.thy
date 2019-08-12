(*<*)(*:maxLineLen=68:*)
theory dAutomaton
  imports bundle.SB_fin spf.SPF
begin


(*causes problems in sb.thy*)
lemma prod_contI[cont2cont]: "(\<And>s. cont(\<lambda>f. g (f,s))) 
\<Longrightarrow>(\<And>f. cont (\<lambda>s. g (f,s))) \<Longrightarrow> cont g"
  by (simp add: prod_contI)
(*>*)

section\<open>Automatons \<close>

text\<open>The behaviour of a component can be modeled by a I/O automaton.
This section defines deterministic and non-deterministic automaton 
types, defines their semantic mapping to \Gls{spf} and \Gls{SPS}.
Furthermore, we take a closer look at causal automatons and use
their properties to introduce a local that is capable of
constructing automaton and is also providing lemmas to ease the 
verification process for the input-output behavior.\<close>


subsection \<open>Deterministic Automaton\<close>
default_sort %invisible "chan"

text\<open>A deterministic I/O Automaton consists of states, a transition
function, a initial state and a initial output. The transition
function for deterministic automaton maps from a state with a
@{type sbElem} to another state and a output \gls{sb}. Now we define
deterministic automaton as a tuple.\<close>

record ('state::type, 'in, 'out) dAutomaton  =
  daTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>))"
  daInitState :: "'state"
  daInitOut:: "'out\<^sup>\<Omega>"

text\<open>The type parameter of @{type dAutomaton} show the state set and
the input and output domain. We then introduce two definition to 
obtain the next state or the next output of the transition function.
\<close>

definition daNextState:: 
"('s::type,'in , _) dAutomaton \<Rightarrow> 's \<Rightarrow>  'in\<^sup>\<surd> \<Rightarrow> 's"where 
"daNextState aut s m = fst ((daTransition aut) s m)"

definition daNextOut::
"('s::type, 'in,'out) dAutomaton \<Rightarrow> 's \<Rightarrow>  'in\<^sup>\<surd> \<Rightarrow> 'out\<^sup>\<Omega>" where
"daNextOut aut s m = snd ((daTransition aut) s m)"

subsubsection \<open>Semantic\<close>

definition daStateSem::"('s::type, 'I::{finite,chan},'O) dAutomaton 
\<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"daStateSem da =
 fix\<cdot>(\<Lambda> h. (\<lambda> state. sb_split\<cdot>
        (\<lambda>sbe. \<Lambda> sb.
           let (nextState, output) = daTransition da state sbe in
          output \<bullet>\<^sup>\<Omega> h nextState\<cdot>sb)))"

definition daSem::"('s::type, 'I::{finite,chan},'O) dAutomaton 
\<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"daSem da \<equiv> \<Lambda> sb. daInitOut da \<bullet>\<^sup>\<Omega> daStateSem da(daInitState da)\<cdot>sb"


paragraph\<open>Semantic Properties\<close>

text\<open>\\\\\<close>
text\<open>paragraph test \<close>

theorem dastatesem_unfolding: "(daStateSem automat s) = 
sb_split\<cdot>(\<lambda>sbe. \<Lambda> sb .
           let (nextState, output) = daTransition automat s sbe in
           output \<bullet>\<^sup>\<Omega> ((daStateSem automat) nextState\<cdot>sb))"
  unfolding daStateSem_def
  apply(subst fix_eq)
  apply(subst beta_cfun)
  apply(intro cont2cont; simp)
  by auto

theorem dastatesem_bottom:
  assumes "\<not>sbHdElemWell (sb::('b::{finite,chan})\<^sup>\<Omega>)"
  and "\<not> chDomEmpty TYPE('b)"
  shows "(daStateSem automat s)\<cdot>sb = \<bottom>"
  apply (subst dastatesem_unfolding)
  apply (simp add: sb_split_insert)
  by (metis (no_types, lifting) assms fup1 sbHdElem_h_cont.rep_eq 
      sbHdElem_h_def)

lemma dastatesem_strict:
  assumes "\<not> chDomEmpty TYPE('b::{finite, chan})"
  shows "(daStateSem automat s)\<cdot>(\<bottom>::'b\<^sup>\<Omega>) = \<bottom>"
  by (simp add: assms dastatesem_bottom sbHdElemWell_def)

lemma dastatesem_step: 
  assumes "sbHdElemWell sb"
  shows "(daStateSem da s)\<cdot>sb = snd (daTransition da s (sbHdElem sb)) 
  \<bullet>\<^sup>\<Omega> daStateSem da (fst (daTransition da s (sbHdElem sb)))\<cdot>(sbRt\<cdot>sb)"
  apply (subst dastatesem_unfolding)
  apply (simp add: sb_split_insert Let_def case_prod_unfold)
  apply (cases "sbHdElem_h_cont\<cdot>sb")
  apply (simp_all add: sbHdElem_h_cont.rep_eq sbHdElem_def)
  apply (simp_all split: u.split)
  apply (metis assms inst_up_pcpo sbHdElem_h_def u.simps(3))
  by (simp add: up_def)

lemma dastatesem_final:
  assumes "sbHdElemWell sb"
  shows "(daStateSem automat s)\<cdot>sb =
  daNextOut automat s (sbHdElem sb) \<bullet>\<^sup>\<Omega> 
  daStateSem automat (daNextState automat s (sbHdElem sb))\<cdot>(sbRt\<cdot>sb)"
  by (metis assms daNextOut_def daNextState_def dastatesem_step)

lemma dastatesem_final_h2:
  shows "(daStateSem automat s)\<cdot>(sbECons sbe\<cdot>sb) =
  (daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> 
  ((daStateSem automat (daNextState automat s sbe))\<cdot>sb)"
  apply (cases "chDomEmpty(TYPE('b))")
  apply (subst sbtypeepmpty_sbenone[of sbe],simp)+
  apply (subst sbtypeepmpty_sbbot[of sb],simp)+
  apply (subst dastatesem_unfolding, simp add: sb_split_insert)
  apply (subst case_prod_unfold)
  apply (subgoal_tac "sbHdElem_h_cont\<cdot>\<bottom>=up\<cdot>(Abs_sbElem(None)::'b\<^sup>\<surd>)")
  apply (simp add: daNextOut_def daNextState_def)
  apply (simp add: sbHdElem_h_cont.rep_eq sbHdElem_h_def chDom_def 
          up_def)
  apply (subst dastatesem_step)
  apply (simp add: sbECons_def sbHdElemWell_def)
  using sbgetch_sbe2sb_nempty strictI apply fastforce
  by (simp only: daNextOut_def daNextState_def sbhdelem_sbecons 
      sbrt_sbecons)

theorem dastatesem_stepI:
  assumes "(daNextOut da s sbe) = out"
  and "(daNextState da s sbe) = nextState"
  shows "daStateSem da s\<cdot>(sbe \<bullet>\<^sup>\<surd> sb) = 
         out  \<bullet>\<^sup>\<Omega> daStateSem da nextState\<cdot>sb"
  by (simp add: assms dastatesem_final_h2)

theorem dastatesem_inempty_len:
  fixes automat::"('state, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "\<And>state sbe. sbLen (daNextOut automat state sbe) \<ge> 1"
  and "chDomEmpty TYPE('in)"
  shows "\<forall>s. sbLen (daStateSem automat s\<cdot>\<bottom>) = \<infinity>"
proof(rule contrapos_pp,simp+)
  assume a1: "\<exists>s::'state. sbLen (daStateSem automat s\<cdot>\<bottom>) \<noteq> \<infinity>"
  obtain len_set where len_set_def: 
        "len_set = {sbLen (daStateSem automat s\<cdot>\<bottom>) | s. True }"
    by simp
  hence len_set_least: "\<exists>n \<in> len_set. \<forall>i \<in> len_set. n \<le> i"
    by (metis (mono_tags, lifting) exists_least_iff le_less_linear 
        len_set_def mem_Collect_eq)
  then obtain state where state_def: "sbLen 
    (daStateSem automat state\<cdot>\<bottom>) \<in> len_set" 
    and "\<forall>n \<in> len_set. sbLen (daStateSem automat state\<cdot>\<bottom>) \<le> n"
    using len_set_def by blast
  hence state_least: "\<forall>s. sbLen (daStateSem automat state\<cdot>\<bottom>) \<le> 
                          sbLen (daStateSem automat s\<cdot>\<bottom>)"
    using len_set_def len_set_least by blast
  then obtain k where k_def: "Fin k = 
                              sbLen (daStateSem automat state\<cdot>\<bottom>)"
    by (metis SBv3.lnat.exhaust a1 inf_less_eq)
  hence "Fin k < sbLen (daNextOut automat state (Abs_sbElem None)) + 
         sbLen (daStateSem automat 
         (daNextState automat state (Abs_sbElem None))\<cdot> \<bottom>)"
    by (metis state_least add.commute assms(1) le2lnle leI 
        lessequal_addition lnat_plus_suc notinfI3)
  thus "False"
    by (metis assms(2) dastatesem_final_h2 k_def leD sblen_sbconc 
        sbtypeempty_sbecons_bot)
qed

lemma dastatesem_weak_fin:
  assumes "sbLen sb = Fin n"
    and "\<And>state sbe. 1 \<le> sbLen (daNextOut automat state sbe)"
  shows "sbLen sb \<le> sbLen (daStateSem automat s\<cdot>sb)"
  apply (induction sb arbitrary: s rule: sb_finind)
  apply (simp_all add: assms)
  apply (cases "chDomEmpty TYPE('a)")
  using assms(1) apply auto[1]
  using sbleast2sblenempty apply fastforce
  by (metis (no_types, lifting) dual_order.trans sbECons_def 
      sbecons_len assms(2) dastatesem_final_h2 lessequal_addition 
      lnat_plus_commu lnat_plus_suc sbECons_def sblen_sbconc)

theorem dastatesem_weak:
  fixes automat::"('state, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "\<And>state sbe. 1 \<le> sbLen (daNextOut automat state sbe)"
  shows     "weak_well (daStateSem automat s)"
  apply (cases "chDomEmpty TYPE('in)")
  apply (metis (full_types) assms dastatesem_inempty_len fold_inf 
        less_lnsuc sblen_empty sbtypeepmpty_sbbot weak_well_def)
  by (metis assms spf_weakI2 dastatesem_weak_fin lnat_well_h2)

theorem dastatesem_least:
  assumes"(\<lambda>state. sb_split\<cdot>
          (\<lambda>sbe. \<Lambda> sb. snd (daTransition X state sbe) \<bullet>\<^sup>\<Omega>  
          Z (fst (daTransition X state sbe))\<cdot>sb)) \<sqsubseteq> Z"
  shows"daStateSem X \<sqsubseteq> Z"
  apply (simp add: daStateSem_def)
  apply (rule fix_least_below)
  apply (subst beta_cfun)
  apply (intro cont2cont; simp)
  by (simp add: assms case_prod_unfold)
  
theorem dasem_insert:
  "daSem automat\<cdot>sb = daInitOut automat \<bullet>\<^sup>\<Omega> 
                     daStateSem automat (daInitState automat)\<cdot>sb"
  by (simp add: daSem_def)

theorem dasem_bottom:
  assumes "\<not>chDomEmpty TYPE('in::{chan,finite})"
  shows "daSem automat\<cdot>(\<bottom>::'in\<^sup>\<Omega>) = daInitOut automat"
  by (simp add: daSem_def assms dastatesem_strict)

theorem dasem_strong:
  assumes "weak_well(daStateSem automat (daInitState automat))"
  and     "1 \<le> sbLen (daInitOut automat)"
  shows "strong_well (daSem automat)"
  apply (subst strong_well_def)
  apply (simp add: daSem_def)
proof
  fix sb
  have h1: "sbLen sb <\<^sup>l lnsuc\<cdot>(sbLen 
                      (daStateSem automat (daInitState automat)\<cdot>sb))"
    using assms(1) sblen_mono
    by (simp add: weak_well_def)
  have h4: "lnsuc\<cdot>(sbLen(daStateSem automat(daInitState automat)\<cdot>sb))
             \<le> sbLen (daInitOut automat) + 
               sbLen (daStateSem automat (daInitState automat)\<cdot>sb)"
    by (metis add.commute assms(2) lessequal_addition lnat_plus_suc 
        order_refl)
  have h2: "sbLen (daInitOut automat) + sbLen (daStateSem automat 
       (daInitState automat)\<cdot>sb) \<le> sbLen (daInitOut automat \<bullet>\<^sup>\<Omega>  
        daStateSem automat (daInitState automat)\<cdot>sb)"
    using sblen_sbconc by auto
  have h3: "sbLen sb <\<^sup>l sbLen (daInitOut automat \<bullet>\<^sup>\<Omega> 
            daStateSem automat (daInitState automat)\<cdot>sb)"
    using h1 h2 h4 dual_order.trans by blast
  then show "\<And>sb. sbLen sb <\<^sup>l sbLen (daInitOut automat \<bullet>\<^sup>\<Omega>  
                  daStateSem automat (daInitState automat)\<cdot>sb)"
    by (metis assms(1) assms(2) dual_order.trans lessequal_addition 
        lnat_plus_commu lnat_plus_suc sblen_sbconc weak_well_def)
qed

(*<*)
end
(*>*)
