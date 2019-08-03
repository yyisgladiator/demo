(*<*)
theory dAutomaton
  imports bundle.SB_fin spf.SPF
begin
(*>*)

section \<open>automaton cont2cont\<close>

(*causes problems in sb.thy*)
lemma prod_contI[cont2cont]: "(\<And>s. cont(\<lambda>f. g (f,s))) \<Longrightarrow>(\<And>f. cont (\<lambda>s. g (f,s))) \<Longrightarrow> cont g"
  by (simp add: prod_contI)

section \<open>Deterministic Automaton\<close>
default_sort "chan"

subsection \<open>Deterministic Automaton definition \<close>
record ('state::type, 'in, 'out::chan) dAutomaton  =
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

lemma dastatesem_step: 
  assumes "sbHdElemWell sb"
  shows "(daStateSem da s)\<cdot>sb = snd (daTransition da s (sbHdElem sb)) \<bullet>\<^sup>\<Omega> daStateSem da (fst (daTransition da s (sbHdElem sb)))\<cdot>(sbRt\<cdot>sb)"
  apply (subst dastatesem_unfolding)
  apply (simp add: sb_case_insert Let_def case_prod_unfold)
  apply (cases "sbHdElem_h_cont\<cdot>sb", simp_all add: sbHdElem_h_cont.rep_eq sbHdElem_def)
  apply (simp_all split: u.split)
  apply (metis sbHdElemWell_def assms inst_up_pcpo sbHdElem_h_def u.simps(3))
  by (simp add: up_def)

lemma dastatesem_final:
  assumes "sbHdElemWell sb"
  shows "(daStateSem automat s)\<cdot>sb =
  (daNextOut automat s (sbHdElem sb)) \<bullet>\<^sup>\<Omega> (((daStateSem automat (daNextState automat s (sbHdElem sb))))\<cdot>(sbRt\<cdot>sb))"
  by (metis assms daNextOut_def daNextState_def dastatesem_step)

lemma dastatesem_final_h2:
  shows "(daStateSem automat s)\<cdot>(sbECons sbe\<cdot>sb) =
  (daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> ((daStateSem automat (daNextState automat s sbe))\<cdot>sb)"
  apply (cases "chIsEmpty(TYPE('b))")
  apply (subst sbtypeepmpty_sbenone[of sbe],simp)+
  apply (subst sbtypeepmpty_sbbot[of sb],simp)+
  apply (subst dastatesem_unfolding, simp add: sb_case_insert)
  apply (subst case_prod_unfold)
  apply (subgoal_tac "sbHdElem_h_cont\<cdot>\<bottom> = up\<cdot>(Abs_sbElem(None)::'b\<^sup>\<surd>)",auto)
  apply (simp add: daNextOut_def daNextState_def)
  apply (simp add: sbHdElem_h_cont.rep_eq sbHdElem_h_def chIsEmpty_def up_def)
  apply (subst dastatesem_step)
  apply (simp add: sbECons_def sbHdElemWell_def)
  using sbgetch_sbe2sb_nempty strictI apply fastforce
  by (simp only: daNextOut_def daNextState_def sbhdelem_sbecons sbrt_sbecons)

lemma dastatesem_stepI:
  assumes "(daNextOut da s sbe) = out"
      and "(daNextState da s sbe) = nextState"
  shows "(daStateSem da s)\<cdot>(sbECons sbe\<cdot>sb) = out  \<bullet>\<^sup>\<Omega> ((daStateSem da nextState)\<cdot>sb)"
  by (simp add: assms dastatesem_final_h2)


(*
lemma dastatesem_strict[simp]: "spfIsStrict (daStateSem da state)"
  oops
*)

lemma up_sbenone: "Iup (Abs_sbElem None) = up\<cdot>(Abs_sbElem None)"
  by (simp add: up_def)

lemma assumes "\<forall>x. P x"
  shows "\<And>x. P x"
  using assms by auto

lemma assumes "\<forall>k. n \<noteq> Fin k"
  shows "n = \<infinity>"
  by (simp add: assms infI)

lemma sblen_slen_fin_eq: assumes "sbLen (sb::'a\<^sup>\<Omega>) = Fin k"
  and "\<not>chIsEmpty TYPE('a)"
  shows "\<exists>c. #(sb \<^enum> c) = Fin k"
  sorry

lemma sbtake_pref: "sbTake i\<cdot>sb \<sqsubseteq> sb"
  by (simp add: sb_belowI)

lemma sbtake_len_fin: 
  assumes "Fin i \<le> sbLen (sb::'a\<^sup>\<Omega>)"
  shows   "sbLen (sbTake i\<cdot>sb) = Fin i"
  apply (simp add: sbtake_insert)
  apply (simp add: sbgetch_insert)
  oops

lemma
  fixes automat::"('state, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "\<And>state sbe. sbLen (daNextOut automat state sbe) \<ge> 1"
  and "chIsEmpty TYPE('in)"
  and "\<not>chIsEmpty TYPE('out)"
shows "\<And>s. sbLen (daStateSem automat s\<cdot>\<bottom>) = \<infinity>"
  apply (rule infI)
  apply (rule allI)
  apply (induct_tac "k")
  defer
  sorry
(*proof (rule ccontr)
  fix s
  assume dastatesem_len: "sbLen (daStateSem automat s\<cdot>\<bottom>) \<noteq> \<infinity>"
  then obtain k where k_len: "sbLen (daStateSem automat s\<cdot>\<bottom>) = Fin k"
    using infI by blast
  have bot_sbecons: "(\<bottom>::'in\<^sup>\<Omega>) = (Abs_sbElem (None)) \<bullet>\<^sup>\<surd> \<bottom>"
    sorry
  obtain next_state where next_state_def: "daNextState automat s (Abs_sbElem (None)) = next_state"
    by simp
  obtain next_out where next_out_def: "daNextOut automat s (Abs_sbElem (None)) = next_out"
    by simp
  hence "daStateSem automat s\<cdot>\<bottom> = next_out \<bullet>\<^sup>\<Omega> ((daStateSem automat next_state)\<cdot>\<bottom>)"
    apply (subst bot_sbecons)
    by (simp add: dastatesem_final_h2 next_state_def)
  hence "sbLen (next_out \<bullet>\<^sup>\<Omega> ((daStateSem automat next_state)\<cdot>\<bottom>)) = Fin k"
    using k_len by auto
  hence "(sbLen next_out) + sbLen ((daStateSem automat next_state)\<cdot>\<bottom>) \<le> Fin k"
    by (metis sblen_sbconc)
  hence "1 + sbLen ((daStateSem automat next_state)\<cdot>\<bottom>) \<le> Fin k"
    using assms(1) dual_order.trans lessequal_addition next_out_def by fastforce
  
  
  hence "\<exists>c. #(daStateSem automat s\<cdot>\<bottom> \<^enum> c) = Fin k"
    using dastatesem_len k_len sblen_min_len_empty sblen_slen_fin_eq by blast
  show False
    sorry
qed*)

lemma fun_weakI_h:
  assumes "\<And>sb s. sbLen sb < \<infinity> \<Longrightarrow> sbLen sb \<le> sbLen (daStateSem automat s\<cdot>sb)"
  shows   "\<And>sb s. sbLen sb = \<infinity> \<Longrightarrow> sbLen sb \<le> sbLen (daStateSem automat s\<cdot>sb)"
proof (rule ccontr)
  fix sb::"'a\<^sup>\<Omega>" and s :: 'b
  assume sb_len: "sbLen sb = \<infinity>"
    and not_weak: "\<not> sbLen sb \<le> sbLen (daStateSem automat s\<cdot>sb)"
  hence out_fin: "sbLen (daStateSem automat s\<cdot>sb) < \<infinity>"
    by (simp add: order.not_eq_order_implies_strict)
  then obtain k where out_len: "sbLen (daStateSem automat s\<cdot>sb) = Fin k"
    using lnat_well_h2 by blast
  have "\<exists>(b::'a\<^sup>\<Omega>). \<not>chIsEmpty TYPE('a) \<longrightarrow> b \<sqsubseteq> sb \<and> sbLen b = Fin (Suc k)"
  proof-
    have "sbTake (Suc k)\<cdot>sb \<sqsubseteq> sb"
      by (simp add: sbtake_pref)
    moreover have "\<not>chIsEmpty TYPE('a) \<longrightarrow> sbLen (sbTake (Suc k)\<cdot>sb) = Fin (Suc k)"
      sorry
    ultimately show ?thesis
      by blast
  qed
  then obtain b::"'a\<^sup>\<Omega>" where b_pref: "b \<sqsubseteq> sb" and b_len: "sbLen b = Fin (Suc k)" and "\<not>chIsEmpty TYPE('a)"
    sorry
  have "(daStateSem automat s\<cdot>b) \<sqsubseteq> (daStateSem automat s\<cdot>sb)"
    by (simp add: b_pref monofun_cfun_arg)
  hence "sbLen (daStateSem automat s\<cdot>b) \<le> sbLen (daStateSem automat s\<cdot>sb)"
    using lnle_def monofun_def sblen_mono by blast
  moreover have "sbLen b \<le> sbLen (daStateSem automat s\<cdot>b)"
    by (metis assms b_len le_less_linear notinfI3)
  thus False
    using Fin_Suc Fin_leq_Suc_leq b_len calculation leD less2eq ln_less out_fin out_len by fastforce
qed

lemma fun_weakI: 
  assumes "\<And>sb s. sbLen sb < \<infinity> \<Longrightarrow> sbLen sb \<le> sbLen (daStateSem automat s\<cdot>sb)"
  shows   "weak_well (daStateSem automat s)"
  apply (simp add: weak_well_def)
  by (meson assms inf_ub less_le fun_weakI_h)

lemma dastatesem_weak_fin:
  assumes "sbLen sb = Fin n"
    and "\<And>state sbe. 1 \<le> sbLen (daNextOut automat state sbe)"
  shows "sbLen sb \<le> sbLen (daStateSem automat s\<cdot>sb)"
proof (induction sb arbitrary: s rule: sb_finind)
case 1
  then show ?case
    by (simp add: assms(1))
next
  case (2 sb)
  then show ?case
    by (metis Fin_neq_inf assms(1) bottomI linear lnle_def lnzero_def sbIsLeast_def sblen_min_len_empty)
next
  case (3 sbe sb)
  hence "sbLen (sbe \<bullet>\<^sup>\<surd> sb) = sbLen (sbe2sb sbe) + sbLen sb"
    sorry
  moreover have "sbLen (sbe2sb sbe) = 1"
    sorry
  moreover have "sbLen (daNextOut automat s sbe) + sbLen (daStateSem automat (daNextState automat s sbe)\<cdot>sb)
  \<le> sbLen ((daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> daStateSem automat (daNextState automat s sbe)\<cdot>sb)"
    by (simp add: sblen_sbconc)
  moreover have "(1 + sbLen sb) \<le> (sbLen (daNextOut automat s sbe)) + sbLen (daStateSem automat (daNextState automat s sbe)\<cdot>sb)"
    sorry
  moreover have "1 + sbLen sb \<le> sbLen ((daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> daStateSem automat (daNextState automat s sbe)\<cdot>sb)"
    using calculation(3) calculation(4) dual_order.trans by blast
  ultimately show ?case 
    by (simp add: dastatesem_final_h2)
qed

lemma dastatesem_weak:
  assumes "\<And>state sbe. 1 \<le> sbLen (daNextOut automat state sbe)"
  shows     "weak_well (daStateSem automat s)"
  apply (rule fun_weakI)
  by (metis assms dastatesem_weak_fin infI less_irrefl)

(*
(da_h automat s) = spfStep (daDom automat) (daRan automat)\<cdot>(da_helper (daTransition automat) s\<cdot>(da_h automat))"
*)
lemma dastatesem_least: assumes"(\<lambda>state::'a.
        sb_case\<cdot>
        (\<lambda>sbe::('b::{chan,finite})\<^sup>\<surd>.
            \<Lambda> (sb::'b\<^sup>\<Omega>).
               snd (daTransition X state sbe) \<bullet>\<^sup>\<Omega> Z (fst (daTransition X state sbe))\<cdot>sb)) \<sqsubseteq>
    Z"
  shows"daStateSem X \<sqsubseteq> Z"
  apply (simp add: daStateSem_def)
  apply (rule fix_least_below)
  apply (subst beta_cfun)
  apply (intro cont2cont; simp)
  by (simp add: assms case_prod_unfold)
  


subsubsection \<open>Sematntic lemmas\<close>

lemma dasem_insert:
  "daSem automat\<cdot>sb = (daInitOut automat) \<bullet>\<^sup>\<Omega> ((daStateSem automat (daInitState automat))\<cdot>sb)"
  by (simp add: daSem_def)

lemma dasem_bottom:
  assumes "\<not> chIsEmpty TYPE('b::{chan, finite})"
  shows "daSem automat\<cdot>(\<bottom>::'b\<^sup>\<Omega>) = daInitOut automat"
  by (simp add: dasem_insert dastatesem_bottom assms)

lemma dasem_strong:
  assumes "weak_well(daStateSem automat (daInitState automat))"
  and     "1 \<le> sbLen (daInitOut automat)"
shows "strong_well (daSem automat)"
  apply (subst strong_well_def)
  apply (simp add: daSem_def)
proof
  fix sb
  have h1: "sbLen sb <\<^sup>l lnsuc\<cdot>(sbLen (daStateSem automat (daInitState automat)\<cdot>sb))"
    using assms(1) sblen_mono
    by (simp add: weak_well_def)
  have h4: "lnsuc\<cdot>(sbLen (daStateSem automat (daInitState automat)\<cdot>sb)) \<le> sbLen (daInitOut automat) + sbLen (daStateSem automat (daInitState automat)\<cdot>sb)"
    using assms(2) lessequal_addition lnat_plus_commu lnat_plus_suc by fastforce 
  have h2: "sbLen (daInitOut automat) + sbLen (daStateSem automat (daInitState automat)\<cdot>sb) \<le> sbLen (daInitOut automat \<bullet>\<^sup>\<Omega>  daStateSem automat (daInitState automat)\<cdot>sb)"
    using sblen_sbconc by auto
  have h3: "sbLen sb <\<^sup>l sbLen (daInitOut automat \<bullet>\<^sup>\<Omega> daStateSem automat (daInitState automat)\<cdot>sb)"
    using h1 h2 h4 dual_order.trans by blast
  then show "\<And>sb. sbLen sb <\<^sup>l sbLen (daInitOut automat \<bullet>\<^sup>\<Omega>  daStateSem automat (daInitState automat)\<cdot>sb)"
    by (metis assms(1) assms(2) dual_order.trans lessequal_addition lnat_plus_commu lnat_plus_suc sblen_sbconc weak_well_def)
qed

(*<*)
end
(*>*)
