(*<*)(*:maxLineLen=68:*)
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

subsubsection \<open>Semantic\<close>

definition daStateSem :: "('s::type, 'I::{finite,chan},'O) dAutomaton \<Rightarrow> ('s \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>))" where
"daStateSem da = fix\<cdot>(\<Lambda> h. (\<lambda> state. sb_case\<cdot>
                        (\<lambda>sbe. \<Lambda> sb.
                          let (nextState, output) = daTransition da state sbe in
                            output \<bullet>\<^sup>\<Omega> h nextState\<cdot>sb)
                      ))"

definition daSem :: "('s::type, 'I::{finite,chan},'O) dAutomaton \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"daSem da = (\<Lambda> sb. (daInitOut da)\<bullet>\<^sup>\<Omega>((daStateSem da (daInitState da))\<cdot>sb))"

subsubsection \<open>Statesemantic lemmas\<close>

theorem dastatesem_unfolding: "(daStateSem automat s) = sb_case\<cdot>(\<lambda>sbe. \<Lambda> sb .
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
  apply (simp add: sb_case_insert)
  by (metis (no_types, lifting) assms fup1 sbHdElemWell_def sbHdElem_h_cont.rep_eq sbHdElem_h_def sbnleast_mex)

lemma dastatesem_strict:
  assumes "\<not> chDomEmpty TYPE('b::{finite, chan})"
  shows "(daStateSem automat s)\<cdot>(\<bottom>::'b\<^sup>\<Omega>) = \<bottom>"
  by (simp add: assms dastatesem_bottom sbHdElemWell_def)

lemma dastatesem_step: 
  assumes "sbHdElemWell sb"
  shows "(daStateSem da s)\<cdot>sb = snd (daTransition da s (sbHdElem sb)) \<bullet>\<^sup>\<Omega> daStateSem da (fst (daTransition da s (sbHdElem sb)))\<cdot>(sbRt\<cdot>sb)"
  apply (subst dastatesem_unfolding)
  apply (simp add: sb_case_insert Let_def case_prod_unfold)
  apply (cases "sbHdElem_h_cont\<cdot>sb", simp_all add: sbHdElem_h_cont.rep_eq sbHdElem_def)
  apply (simp_all split: u.split)
  apply (metis assms inst_up_pcpo sbHdElem_h_def Stream.slen_empty_eq sbHdElemWell_def lnzero_def
         sbIsLeast_def sbgetch_insert2 sblen2slen u.simps(3))
  by (simp add: up_def)

lemma dastatesem_final:
  assumes "sbHdElemWell sb"
  shows "(daStateSem automat s)\<cdot>sb =
  (daNextOut automat s (sbHdElem sb)) \<bullet>\<^sup>\<Omega> (((daStateSem automat (daNextState automat s (sbHdElem sb))))\<cdot>(sbRt\<cdot>sb))"
  by (metis assms daNextOut_def daNextState_def dastatesem_step)

lemma dastatesem_final_h2:
  shows "(daStateSem automat s)\<cdot>(sbECons sbe\<cdot>sb) =
  (daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> ((daStateSem automat (daNextState automat s sbe))\<cdot>sb)"
  apply (cases "chDomEmpty(TYPE('b))")
  apply (subst sbtypeepmpty_sbenone[of sbe],simp)+
  apply (subst sbtypeepmpty_sbbot[of sb],simp)+
  apply (subst dastatesem_unfolding, simp add: sb_case_insert)
  apply (subst case_prod_unfold)
  apply (subgoal_tac "sbHdElem_h_cont\<cdot>\<bottom> = up\<cdot>(Abs_sbElem(None)::'b\<^sup>\<surd>)")
  apply (simp add: daNextOut_def daNextState_def)
  apply (simp add: sbHdElem_h_cont.rep_eq sbHdElem_h_def chDom_def up_def)
  apply (subst dastatesem_step)
  apply (simp add: sbECons_def sbHdElemWell_def)
  using sbgetch_sbe2sb_nempty strictI apply fastforce
  by (simp only: daNextOut_def daNextState_def sbhdelem_sbecons sbrt_sbecons)

theorem dastatesem_stepI:
  assumes "(daNextOut da s sbe) = out"
      and "(daNextState da s sbe) = nextState"
  shows "(daStateSem da s)\<cdot>(sbECons sbe\<cdot>sb) = out  \<bullet>\<^sup>\<Omega> ((daStateSem da nextState)\<cdot>sb)"
  by (simp add: assms dastatesem_final_h2)

lemma dastatesem_inempty_step:
  fixes automat::"('state, 'in::{chan, finite}, 'out) dAutomaton"
  assumes"chDomEmpty TYPE('in)"
  shows "daStateSem automat s\<cdot>\<bottom> = (daNextOut automat s (Abs_sbElem None)) \<bullet>\<^sup>\<Omega> 
         ((daStateSem automat (daNextState automat s (Abs_sbElem None)))\<cdot>\<bottom>)"
  by (metis assms dastatesem_final_h2 sbtypeempty_sbecons_bot)

theorem dastatesem_inempty_len:
  fixes automat::"('state, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "\<And>state sbe. sbLen (daNextOut automat state sbe) \<ge> 1"
  and "chDomEmpty TYPE('in)"
  shows "\<forall>s. sbLen (daStateSem automat s\<cdot>\<bottom>) = \<infinity>"
proof(rule contrapos_pp,simp+)
  assume a1: "\<exists>s::'state. sbLen (daStateSem automat s\<cdot>\<bottom>) \<noteq> \<infinity>"
  obtain len_set where len_set_def: "len_set = { sbLen (daStateSem automat s\<cdot>\<bottom>) | s. True }"
    by simp
  then obtain n where n_def: "n \<in> len_set" and n_least: "\<forall>i. i \<in> len_set \<longrightarrow> n \<le> i"
    by (metis (mono_tags, lifting) exists_least_iff le_less_linear len_set_def mem_Collect_eq)
  then obtain state where state_def: "sbLen (daStateSem automat state\<cdot>\<bottom>) = n"
    using len_set_def by blast
  hence state_least: "\<forall>s. sbLen (daStateSem automat state\<cdot>\<bottom>) \<le> sbLen (daStateSem automat s\<cdot>\<bottom>)"
    using len_set_def n_least by blast
  then obtain k where k_def:"Fin k = sbLen (daStateSem automat state\<cdot>\<bottom>)"
    by (metis SBv3.lnat.exhaust a1 inf_less_eq)
  then have "\<forall>s. Fin k \<le> sbLen (daStateSem automat s\<cdot>\<bottom>)"
    by (simp add: state_least)
  then have "sbLen (daStateSem automat state\<cdot>\<bottom>) > Fin k"
  proof -
    assume "\<forall>s. Fin k \<le> sbLen (daStateSem automat s\<cdot>\<bottom>)"
    then have "Fin k < sbLen (daNextOut automat state (Abs_sbElem None)) + sbLen (daStateSem automat (daNextState automat state (Abs_sbElem None))\<cdot> \<bottom>)"
      by (metis add.commute assms(1) le2lnle leI lessequal_addition lnat_plus_suc notinfI3)
    then show "Fin k < sbLen (daStateSem automat state\<cdot>\<bottom>)"
      by (metis assms(2) dastatesem_inempty_step k_def leD sblen_sbconc)
  qed
  then show "False"
    by (simp add: k_def)
qed

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
    by (metis lnat_plus_commu lnat_plus_suc sbecons_len sbelen_one)
  moreover have "sbLen (sbe2sb sbe) = 1"
    by (simp add: "3.hyps")
  moreover have "sbLen (daNextOut automat s sbe) + sbLen (daStateSem automat (daNextState automat s sbe)\<cdot>sb)
  \<le> sbLen ((daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> daStateSem automat (daNextState automat s sbe)\<cdot>sb)"
    by (simp add: sblen_sbconc)
  moreover have "(1 + sbLen sb) \<le> (sbLen (daNextOut automat s sbe)) + sbLen (daStateSem automat (daNextState automat s sbe)\<cdot>sb)"
    by (simp add: "3.IH" assms(2) lessequal_addition)
  moreover have "1 + sbLen sb \<le> sbLen ((daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> daStateSem automat (daNextState automat s sbe)\<cdot>sb)"
    using calculation(3) calculation(4) dual_order.trans by blast
  ultimately show ?case 
    by (simp add: dastatesem_final_h2)
qed

lemma fun_weakI_h:
  fixes automat::"('state, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "\<not>chDomEmpty TYPE('in)" and "\<And>sb s. sbLen sb < \<infinity> \<Longrightarrow> sbLen sb \<le> sbLen (daStateSem automat s\<cdot>sb)"
  shows   "\<And>sb s. sbLen sb = \<infinity> \<Longrightarrow> sbLen sb \<le> sbLen (daStateSem automat s\<cdot>sb)"
proof (rule ccontr)
  fix sb::"'in\<^sup>\<Omega>" and s :: 'state
  assume sb_len: "sbLen sb = \<infinity>"
    and not_weak: "\<not> sbLen sb \<le> sbLen (daStateSem automat s\<cdot>sb)"
  hence out_fin: "sbLen (daStateSem automat s\<cdot>sb) < \<infinity>"
    by (simp add: order.not_eq_order_implies_strict)
  then obtain k where out_len: "sbLen (daStateSem automat s\<cdot>sb) = Fin k"
    using lnat_well_h2 by blast
  have "\<exists>(b::'in\<^sup>\<Omega>). b \<sqsubseteq> sb \<and> sbLen b = Fin (Suc k)"
  proof-
    have sbtake_fin_ch_ex: "\<exists>c. sbLen (sbTake (Suc k)\<cdot>sb) = #((sbTake (Suc k)\<cdot>sb) \<^enum> c)"
      using sblen2slen assms by blast
    have "sbTake (Suc k)\<cdot>sb \<sqsubseteq> sb"
      by (simp add: sb_belowI)
    moreover have "sbLen (sbTake (Suc k)\<cdot>sb) = Fin (Suc k)"
      by (metis (no_types, lifting) assms(1) dual_order.trans less2lnleD out_fin out_len sb_len sblen_min_len sbtake_fin_ch_ex sbtake_getch slen_stake)
    ultimately show ?thesis
      by blast
  qed
  then obtain b::"'in\<^sup>\<Omega>" where b_pref: "b \<sqsubseteq> sb" and b_len_fin: "sbLen b = Fin (Suc k)"
    by auto
  have "(daStateSem automat s\<cdot>b) \<sqsubseteq> (daStateSem automat s\<cdot>sb)"
    by (simp add: b_pref monofun_cfun_arg)
  hence "sbLen (daStateSem automat s\<cdot>b) \<le> sbLen (daStateSem automat s\<cdot>sb)"
    using lnle_def monofun_def sblen_mono by blast
  moreover have len_leq_nempty: "sbLen b \<le> sbLen (daStateSem automat s\<cdot>b)"
    by (metis assms(2) b_len_fin le_less_linear notinfI3)
  thus False
    using Fin_leq_Suc_leq b_len_fin calculation out_len by fastforce
qed

lemma fun_weakI: 
  fixes automat::"('state, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "\<not>chDomEmpty TYPE('in)"
    and "\<And>sb s. sbLen sb < \<infinity> \<Longrightarrow> sbLen sb \<le> sbLen (daStateSem automat s\<cdot>sb)"
  shows   "weak_well (daStateSem automat s)"
  apply (simp add: weak_well_def)
  by (metis assms inf_ub less_le fun_weakI_h)

theorem dastatesem_weak:
  assumes "\<And>state sbe. 1 \<le> sbLen (daNextOut (automat::('state, 'in::{chan, finite}, 'out) dAutomaton) state sbe)"
  shows     "weak_well (daStateSem automat s)"
  apply (cases "chDomEmpty TYPE('in)")
  apply (metis (full_types) assms dastatesem_inempty_len fold_inf less_lnsuc sblen_min_len_empty sbtypeepmpty_sbbot weak_well_def)
  apply (rule fun_weakI, simp)
  by (metis assms dastatesem_weak_fin infI less_irrefl)

theorem dastatesem_least:
  assumes"(\<lambda>state. sb_case\<cdot>(\<lambda>sbe. \<Lambda> sb. snd (daTransition X state sbe) \<bullet>\<^sup>\<Omega>  
          Z (fst (daTransition X state sbe))\<cdot>sb)) \<sqsubseteq> Z"
  shows"daStateSem X \<sqsubseteq> Z"
  apply (simp add: daStateSem_def)
  apply (rule fix_least_below)
  apply (subst beta_cfun)
  apply (intro cont2cont; simp)
  by (simp add: assms case_prod_unfold)

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
    by (metis lnat_plus_commu lnat_plus_suc sbecons_len sbelen_one)
  moreover have "sbLen (sbe2sb sbe) = 1"
    by (simp add: "3.hyps")
  moreover have "sbLen (daNextOut automat s sbe) + sbLen (daStateSem automat (daNextState automat s sbe)\<cdot>sb)
  \<le> sbLen ((daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> daStateSem automat (daNextState automat s sbe)\<cdot>sb)"
    by (simp add: sblen_sbconc)
  moreover have "(1 + sbLen sb) \<le> (sbLen (daNextOut automat s sbe)) + sbLen (daStateSem automat (daNextState automat s sbe)\<cdot>sb)"
    by (simp add: "3.IH" assms(2) lessequal_addition)
  moreover have "1 + sbLen sb \<le> sbLen ((daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> daStateSem automat (daNextState automat s sbe)\<cdot>sb)"
    using calculation(3) calculation(4) dual_order.trans by blast
  ultimately show ?case 
    by (simp add: dastatesem_final_h2)
qed

lemma dastatesem_weak:
  assumes "\<And>state sbe. 1 \<le> sbLen (daNextOut (automat::('state, 'in::{chan, finite}, 'out) dAutomaton) state sbe)"
  shows     "weak_well (daStateSem automat s)"
  apply (cases "chIsEmpty TYPE('in)")
  apply (metis (full_types) assms dastatesem_inempty_len fold_inf less_lnsuc sblen_min_len_empty sbtypeepmpty_sbbot weak_well_def)
  apply (rule fun_weakI, simp)
  by (metis assms dastatesem_weak_fin infI less_irrefl)
  
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
  
subsubsection \<open>Semantic lemmas\<close>

theorem dasem_insert:
  "daSem automat\<cdot>sb = (daInitOut automat) \<bullet>\<^sup>\<Omega> ((daStateSem automat (daInitState automat))\<cdot>sb)"
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
