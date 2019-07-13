(*<*)
theory dAutomaton
  imports bundle.SB_fin
begin
(*>*)

section \<open>automaton cont2cont\<close>

(*causes problems in sb.thy*)
lemma prod_contI[cont2cont]: "(\<And>s. cont(\<lambda>f. g (f,s))) \<Longrightarrow>(\<And>f. cont (\<lambda>s. g (f,s))) \<Longrightarrow> cont g"
  by (simp add: prod_contI)

section \<open>Deterministic Automaton\<close>
default_sort "chan"

subsection \<open>Deterministic Automaton definition \<close>
record ('state::type, 'in::"{chan, finite}", 'out::chan) dAutomaton  =
  daTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<Omega>))"
  daInitState :: "'state"
  daInitOut:: "'out\<^sup>\<Omega>"

subsubsection \<open>Deterministic Automaton general functions\<close>

definition daNextState:: "('s::type,'in::{chan, finite} , _) dAutomaton \<Rightarrow> 's \<Rightarrow>  'in\<^sup>\<surd> \<Rightarrow> 's" where
"daNextState aut s m = fst ((daTransition aut) s m)"

definition daNextOut:: "('s::type, 'in::{chan, finite},'out::chan) dAutomaton \<Rightarrow> 's \<Rightarrow>  'in\<^sup>\<surd> \<Rightarrow> 'out\<^sup>\<Omega>" where
"daNextOut aut s m = snd ((daTransition aut) s m)"

subsection \<open>Semantic for deterministic Automaton \<close>

(*
definition dahelper:: "('s::type \<Rightarrow>'e::cpo \<Rightarrow> ('s \<times> 'O\<^sup>\<Omega>)) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)) \<rightarrow> ('e \<rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"dahelper f s \<equiv> \<Lambda> h. (\<Lambda> e. (\<Lambda> sb. (((snd (f s e)))\<bullet>\<^sup>\<Omega>((h (fst (f s e)))\<cdot>sb))))"
*)

subsubsection \<open>Sematntic\<close>

definition daStateSem :: "('s::type, 'I::{finite,chan},'O) dAutomaton \<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"daStateSem da = fix\<cdot>(\<Lambda> h. (\<lambda> state. sb_case\<cdot>
                        (\<lambda>sbe. \<Lambda> sb.
                          let (nextState, output) = daTransition da state sbe in
                            output \<bullet>\<^sup>\<Omega> h nextState\<cdot>sb)
                      ))"

definition daSem :: "('s::type, 'I::{finite,chan},'O) dAutomaton \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"daSem da = (\<Lambda> sb. (daInitOut da)\<bullet>\<^sup>\<Omega>((daStateSem da (daInitState da))\<cdot>sb))"

subsubsection \<open>Statesematntic lemmas\<close>
(* Die Lemma verwenden noch spfStep *)

lemma dastatesem_unfolding: "(daStateSem automat s) = sb_case\<cdot>(\<lambda>sbe. \<Lambda> sb .
                                                  let (nextState, output) = daTransition automat s sbe in
                            output \<bullet>\<^sup>\<Omega> ((daStateSem automat) nextState\<cdot>sb))"
  unfolding daStateSem_def
  apply(subst fix_eq)
  apply(subst beta_cfun)
  apply(intro cont2cont; simp)
  by auto
  

(* TODO: einheitliche assumption für diesen fall, KEIN rohes exists ! *)
lemma dastatesem_bottom:
  assumes "\<exists>(c::'b::{finite,chan}). (sb::'b\<^sup>\<Omega>)  \<^enum>  c = \<epsilon>"
  and "\<not> chIsEmpty TYPE('b)"
  shows "(daStateSem automat s)\<cdot>sb = \<bottom>"
  apply (subst dastatesem_unfolding)
  apply (simp add: sb_case_insert)
  using assms by (simp add: sbHdElem_h_cont.rep_eq assms sbHdElem_h_def chIsEmpty_def)

lemma dastatesem_strict:
  assumes "\<not> chIsEmpty TYPE('b::{finite, chan})"
  shows "(daStateSem automat s)\<cdot>(\<bottom>::'b\<^sup>\<Omega>) = \<bottom>"
  by (simp add: assms dastatesem_bottom)

lemma type_chnempty: 
  assumes "\<And>c::'a. sb  \<^enum>  c \<noteq> \<epsilon>"
  shows "\<not> chIsEmpty TYPE('a)" and "\<not> range (Rep::'a\<Rightarrow>channel) \<subseteq> cEmpty"
  apply (metis (full_types) assms sbgetch_bot sbtypeepmpty_sbbot)
  by (metis (mono_tags, lifting) Collect_mem_eq Collect_mono_iff UNIV_I assms cEmpty_def dual_order.refl image_subset_iff sbgetch_ctype_notempty)

lemma dastatesem_step: 
  assumes "\<And>c . sb \<^enum> c \<noteq> \<epsilon>"
  shows "(daStateSem da s)\<cdot>sb = snd (daTransition da s (sbHdElem sb)) \<bullet>\<^sup>\<Omega> daStateSem da (fst (daTransition da s (sbHdElem sb)))\<cdot>(sbRt\<cdot>sb)"
  apply (subst dastatesem_unfolding)
  apply (subst sb_case_insert)
  apply (subst case_prod_unfold)
  apply (subst sbHdElem_def)+
  using assms apply (simp add: sbHdElem_h_cont.rep_eq sbHdElem_h_def)
  apply (rule conjI)
  apply (rule impI)
  using assms type_chnempty(2) apply blast
  apply (rule impI)
  apply (subst(asm) type_chnempty(2) [where sb="sb"], simp_all add: assms)
  apply (case_tac "\<exists>sbe. Iup (Abs_sbElem (Some (\<lambda>c::'a. shd (sb  \<^enum>  c)))) = up\<cdot>sbe")
  apply auto
  apply (subst(asm) up_def)
  apply (subst(asm) beta_cfun, simp_all add: up_def)
  by metis

lemma dastatesem_final:
  assumes "\<And>c . sb \<^enum> c \<noteq> \<epsilon>"  (* Todo: einheitliche assumption *)
  shows "(daStateSem automat s)\<cdot>sb =
  (daNextOut automat s (sbHdElem sb)) \<bullet>\<^sup>\<Omega> (((daStateSem automat (daNextState automat s (sbHdElem sb))))\<cdot>(sbRt\<cdot>sb))"
  by (metis assms daNextOut_def daNextState_def dastatesem_step)

lemma iup_bot_nexists: "\<nexists>u. Iup u = \<bottom>"
  by (simp add: inst_up_pcpo)

lemma reprange_cempty_notin: "\<And>(x::'a). range (Rep::'a\<Rightarrow>channel) \<inter> cEmpty = {} \<Longrightarrow> Rep x \<notin> cEmpty"
  by blast

lemma "\<not> range (Rep::'a\<Rightarrow>channel) \<subseteq> cEmpty \<Longrightarrow> (range (Rep::'a\<Rightarrow>channel)) \<inter> cEmpty = {}"
  using chan_botsingle by blast

lemma sbecons_sbgetch_nempty: assumes "\<not>chIsEmpty(TYPE('a))"
  shows "(sbe::'a\<^sup>\<surd>) \<bullet>\<^sup>\<surd> sb  \<^enum>  c \<noteq> \<epsilon>"
  apply (simp add: sbECons_def)
  apply (subgoal_tac "\<exists>f. Rep_sbElem sbe = Some f")
  apply (metis (mono_tags, lifting) option.simps(5) sbe2sb.rep_eq sbgetch_insert2 srcdups_step srcdupsimposs strictI strict_sdropwhile)
  by (simp add: assms)

lemma assumes "\<not>chIsEmpty(TYPE('a))"
  shows "sbHdElem (sbe \<bullet>\<^sup>\<surd> sb) = sbHdElem (sbe2sb sbe)"
  apply (simp add: sbECons_def)
  apply (subgoal_tac "\<exists>f. Rep_sbElem sbe = Some f")
  sorry

lemma sbecons_sbhdelem: "sbHdElem (sbe \<bullet>\<^sup>\<surd> sb) = sbe"
  apply (cases "chIsEmpty(TYPE('a))")
  apply (simp add: sbHdElem_def sbHdElem_h_def)
  apply (subst sbtypeepmpty_sbenone[of sbe], simp)+
  apply simp
  apply (simp add: sbECons_def)
  sorry
  
lemma sbecons_sbrt: "sbRt\<cdot>(sbe \<bullet>\<^sup>\<surd> sb) = sb"
  apply (cases "chIsEmpty(TYPE('a))", simp)
  sorry

lemma dastatesem_final_h2:
  shows "(daStateSem automat s)\<cdot>(sbECons sbe\<cdot>sb) =
  (daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> ((daStateSem automat (daNextState automat s sbe))\<cdot>sb)"
  apply(cases "chIsEmpty(TYPE('b))")
  apply (subst sbtypeepmpty_sbenone[of sbe],simp)+
  apply(subst sbtypeepmpty_sbbot[of sb],simp)+
  apply(subst dastatesem_unfolding, simp add: sb_case_insert)
  apply(subst case_prod_unfold)
  apply(subgoal_tac "sbHdElem_h_cont\<cdot>\<bottom> = up\<cdot>(Abs_sbElem(None)::'b\<^sup>\<surd>)",auto)
  apply(simp add: daNextOut_def daNextState_def)
  apply(simp add: sbHdElem_h_cont.rep_eq sbHdElem_h_def chIsEmpty_def up_def)
  apply (subst dastatesem_step)
  apply (simp add: sbecons_sbgetch_nempty)
  apply (subst daNextOut_def)
  apply (subst daNextState_def)
  by (simp only: sbecons_sbhdelem sbecons_sbrt)

lemma dastatesem_stepI:
  assumes "(daNextOut da s sbe) = out"
      and "(daNextState da s sbe) = nextState"
  shows "(daStateSem da s)\<cdot>(sbECons sbe\<cdot>sb) = out  \<bullet>\<^sup>\<Omega> ((daStateSem da nextState)\<cdot>sb)"
  by (simp add: assms dastatesem_final_h2)


(*
lemma dastatesem_strict[simp]: "spfIsStrict (daStateSem da state)"
  oops
*)

lemma dastatesem_weak:
  assumes "\<And>state sbe. 1 \<le> sbLen (daNextOut automat state sbe)"
  shows     "weak_well (daStateSem automat s)"
  oops

lemma dastatesem_least: assumes"(\<lambda>s. spfStep\<cdot>(dahelper (daTransition X) s\<cdot>Z)) \<sqsubseteq> Z"
                  shows"daStateSem X \<sqsubseteq> Z"
  oops


subsubsection \<open>Sematntic lemmas\<close>

lemma dasem_insert:
  "daSem automat\<cdot>sb = (daInitOut automat) \<bullet>\<^sup>\<Omega> ((daStateSem automat (daInitState automat))\<cdot>sb)"
  by (simp add: daSem_def)

lemma dasem_bottom:
  shows "daSem automat\<cdot>\<bottom> = daInitOut automat"
  oops

lemma dasem_strong:
  assumes "weak_well(daStateSem automat (daInitState automat))"
  and     "1 \<le> sbLen (daInitOut automat)"
  shows "strong_well (daSem automat)"
  oops

(*<*)
end
(*>*)
