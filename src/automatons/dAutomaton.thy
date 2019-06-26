theory dAutomaton

imports bundle.SB_fin spf.SPF
begin

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
                        (\<Lambda> sbe sb. 
                          let (nextState, output) = daTransition da state sbe in
                            output \<bullet>\<^sup>\<Omega> h nextState\<cdot>sb)
                      ))"


lemma "cont (\<lambda> sb. let (nextState, output) = daTransition da state sbe in
                            output \<bullet>\<^sup>\<Omega> h nextState\<cdot>sb)"
  by simp

lemma "cont (\<lambda> sbe. \<Lambda> sb. let (nextState, output) = daTransition da state sbe in
                            output \<bullet>\<^sup>\<Omega> h nextState\<cdot>sb)"
  by simp

lemma dastatesem_cont[simp]:"cont (\<lambda> h. (\<lambda> state. sb_case\<cdot>
                        (\<Lambda> sbe sb. 
                          let (nextState, output) = daTransition da state sbe in
                            output \<bullet>\<^sup>\<Omega> h nextState\<cdot>sb)))" (*verkürzen*)
  apply (simp add: prod.case_eq_if)
  apply(rule Cont.contI2)
  apply(rule monofunI)
   apply(rule fun_belowI)
  apply(rule monofun_cfun,simp)
  apply(rule cfun_belowI,simp)+
   apply (smt case_prod_conv fun_below_iff monofun_cfun_arg monofun_cfun_fun po_eq_conv split_cong)
  apply(simp add: lub_fun)
  apply(subst contlub_cfun_fun)
   apply (simp add: ch2ch_fun)
  apply(subst contlub_cfun_arg)
   apply (simp add: ch2ch_fun)
  apply(rule fun_belowI)
  apply(rule cfun_belowI)
  apply(subst contlub_cfun_fun)
  apply(rule chainI)
  apply(rule monofun_cfun,simp)
  apply(rule cfun_belowI)
  apply(simp)
  apply(rule cfun_belowI)
   apply(simp)
   apply (smt po_class.chainE case_prod_conv fun_below_iff monofun_cfun_arg monofun_cfun_fun po_eq_conv split_cong)
  apply(subgoal_tac "(\<Lambda> (sbe::'b\<^sup>\<surd>) (sb::'b\<^sup>\<Omega>). \<Squnion>i::nat. snd (daTransition da x sbe) \<bullet>\<^sup>\<Omega> Y i (fst (daTransition da x sbe))\<cdot>sb)
                      = (\<Squnion>i::nat.(\<Lambda> (sbe::'b\<^sup>\<surd>) (sb::'b\<^sup>\<Omega>). snd (daTransition da x sbe) \<bullet>\<^sup>\<Omega> Y i (fst (daTransition da x sbe))\<cdot>sb))")
   apply simp
   apply(subst contlub_cfun_arg)
  apply(rule chainI)
  apply(rule cfun_belowI)
  apply(simp)
  apply(rule cfun_belowI)
   apply(simp)
    apply (smt po_class.chainE case_prod_conv fun_below_iff monofun_cfun_arg monofun_cfun_fun po_eq_conv split_cong)
   apply(subst contlub_cfun_fun)
    apply(rule chainI)
    apply(rule monofun_cfun,simp)
  apply(rule cfun_belowI)
  apply(simp)
  apply(rule cfun_belowI)
    apply(simp)
    apply (metis (no_types, hide_lams) cfun_below_iff fun_belowD monofun_cfun_arg po_class.chainE)
   apply simp
  apply(subst lub_cfun,simp)
   apply(rule chainI)
  apply(rule cfun_belowI)
  apply(simp)
  apply(rule cfun_belowI)
    apply(simp)
   apply (metis (no_types, hide_lams) cfun_below_iff fun_belowD monofun_cfun_arg po_class.chainE)
  apply(subst lub_cfun,simp)
   apply(rule chainI)
  apply(rule cfun_belowI)
  apply(simp)
   apply (metis (no_types, hide_lams) cfun_below_iff fun_belowD monofun_cfun_arg po_class.chainE)
  by simp

definition daSem :: "('s::type, 'I::{finite,chan},'O) dAutomaton \<Rightarrow> ('I\<^sup>\<Omega> \<rightarrow> 'O\<^sup>\<Omega>)" where
"daSem da = (\<Lambda> sb. (daInitOut da)\<bullet>\<^sup>\<Omega>((daStateSem da (daInitState da))\<cdot>sb))"

subsubsection \<open>Statesematntic lemmas\<close>
(* Die Lemma verwenden noch spfStep *)

lemma dastatesem_unfolding: "(daStateSem automat s) = sb_case\<cdot>(\<Lambda> sbe sb.
                                                  let (nextState, output) = daTransition automat s sbe in
                            output \<bullet>\<^sup>\<Omega> ((daStateSem automat) nextState\<cdot>sb))"
  unfolding daStateSem_def
  apply(subst fix_eq)
  apply(subst beta_cfun)
  using dastatesem_cont apply blast
  by auto

lemma dastatesem_bottom:assumes "\<exists>(c::'b::{finite,chan}). (sb::'b\<^sup>\<Omega>)  \<^enum>  c = \<epsilon>"
  shows "(daStateSem automat s)\<cdot>sb = \<bottom>"
  oops

lemma dastatesem_strict:
  shows "(daStateSem automat s)\<cdot>\<bottom> = \<bottom>"
  oops

lemma dastatesem_step: assumes "\<forall>(c::'b::{finite,chan}). (sb::'b\<^sup>\<Omega>)  \<^enum>  c \<noteq> \<epsilon>"
  shows "(daStateSem automat s)\<cdot>sb = snd (daTransition da state (sbHdElem sb)) \<bullet>\<^sup>\<Omega> h (fst (daTransition da state (sbHdElem sb)))\<cdot>(sbRt\<cdot>sb)"
  oops

lemma dastatesem_final:assumes "\<forall>(c::'b::{finite,chan}). (sb::'b\<^sup>\<Omega>)  \<^enum>  c \<noteq> \<epsilon>"
  shows "(daStateSem automat s)\<cdot>sb =
  (daNextOut automat s (sbHdElem sb)) \<bullet>\<^sup>\<Omega> (((daStateSem automat (daNextState automat s (sbHdElem sb))))\<cdot>(sbRt\<cdot>sb))"
  oops

lemma dastatesem_final_h2:
  shows "(daStateSem automat s)\<cdot>(sbECons\<cdot>sbe\<cdot>sb) =
  (daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> ((daStateSem automat (daNextState automat s sbe))\<cdot>sb)"
  oops

lemma dastatesem_stepI:
  assumes "(daNextOut da s sbe) = out"
      and "(daNextState da s sbe) = nextState"
  shows "(daStateSem da s)\<cdot>(sbECons\<cdot>sbe\<cdot>sb) = out  \<bullet>\<^sup>\<Omega> ((daStateSem da nextState)\<cdot>sb)"
  oops


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

subsection \<open>Deterministic Weak Automata definition\<close>

record ('state::type, 'in::"{chan,finite}", 'out, 'initOut) dAutomaton_weak  =
  dawTransition :: "('state \<Rightarrow> 'in\<^sup>\<surd> \<Rightarrow> ('state \<times> 'out\<^sup>\<surd>))"
  dawInitState :: "'state"
  dawInitOut:: "'initOut\<^sup>\<surd>"

definition daw2da::"('state::type, 'in::{chan,finite}, 'out,'initOut) dAutomaton_weak \<Rightarrow> ('state::type, 'in, 'out) dAutomaton" where
"daw2da \<equiv> \<lambda>aut. (| daTransition =(\<lambda>s sbe. (fst(dawTransition aut s sbe),sbe2sb\<cdot>(snd(dawTransition aut s sbe)))), 
                 daInitState = dawInitState(aut), daInitOut = (sbe2sb\<cdot>(dawInitOut aut)\<star>) |)"


subsection \<open>Weak Automaton Semantic options\<close>

subsubsection \<open>Deterministic Automaton Semantic\<close>

definition semantik_weak::"('state::type, 'in::{chan,finite}, 'out::chan, 'initOut) dAutomaton_weak \<Rightarrow> ('in,'out)spfw"where
"semantik_weak autw = Abs_spfw(daSem(daw2da autw))"


subsubsection \<open>Rum96 Automaton Semantic\<close>

function Rum_tap::"('s::type, 'in::{chan,finite},'out,'initOut) dAutomaton_weak \<Rightarrow> ('s \<Rightarrow> ('in,'out) spfw) set" where
"Rum_tap aut = {h | h. \<forall>m s. \<exists>t out . ((snd(dawTransition aut s m)) = out) \<and> 
                    (\<exists>h2\<in> (Rum_tap aut). \<forall>i .
          (Rep_spfw(h s))\<cdot>(m \<bullet>\<^sup>\<surd> i) = out \<bullet>\<^sup>\<surd> ((Rep_spfw(h2 t))\<cdot>i))}"
  by(simp)+

(*Termination for Rum_tap necessary?*)

fun Rum_ta::"('s::type, 'in::{chan,finite},'out,'initOut) dAutomaton_weak \<Rightarrow> (('in,'out) spfw) set"where
"Rum_ta aut = {g | g. \<exists>h\<in>(Rum_tap aut). \<exists> s (out::'initOut\<^sup>\<surd>). \<forall>i. 
              (Rep_spfw g)\<cdot>i = ((sbe2sb\<cdot>out)\<star>)\<bullet>\<^sup>\<Omega>((Rep_spfw(h s))\<cdot>i)}"

subsection \<open>Strong Deterministic Automaton Definition \<close>

type_synonym ('s,'in,'out)dAutomaton_strong = "('s,'in,'out,'out)dAutomaton_weak"


subsection \<open>Strong Automaton Semantic options \<close>

subsubsection \<open>Deterministic Automaton Semantic\<close>

definition semantik_strong::"('s::type, 'in::{finite,chan}, 'out) dAutomaton_strong \<Rightarrow> ('in,'out)spfs"where
"semantik_strong auts = Abs_spfs(semantik_weak auts)"

subsection \<open>Rum96 Automaton Semantic \<close>

fun Rum_ta_strong::"('s::type, 'in::{chan,finite},'out) dAutomaton_strong \<Rightarrow> (('in,'out) spfs) set"where
"Rum_ta_strong aut = Abs_spfs `(Rum_ta aut)"

end