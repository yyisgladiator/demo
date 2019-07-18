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
lemma dastatesem_bottom:assumes "\<exists>(c::'b::{finite,chan}). (sb::'b\<^sup>\<Omega>)  \<^enum>  c = \<epsilon>"
  shows "(daStateSem automat s)\<cdot>sb = \<bottom>"
  sorry

lemma dastatesem_strict:
  shows "(daStateSem automat s)\<cdot>\<bottom> = \<bottom>"
  oops  (* gilt nicht für cEmpty-Bündel *)

lemma dastatesem_step: assumes "\<And>c . sb \<^enum> c \<noteq> \<epsilon>"
  shows "(daStateSem automat s)\<cdot>sb = snd (daTransition da state (sbHdElem sb)) \<bullet>\<^sup>\<Omega> h (fst (daTransition da state (sbHdElem sb)))\<cdot>(sbRt\<cdot>sb)"
  oops

lemma dastatesem_final:assumes "\<And>c . sb \<^enum> c \<noteq> \<epsilon>"  (* Todo: einheitliche assumption *)
  shows "(daStateSem automat s)\<cdot>sb =
  (daNextOut automat s (sbHdElem sb)) \<bullet>\<^sup>\<Omega> (((daStateSem automat (daNextState automat s (sbHdElem sb))))\<cdot>(sbRt\<cdot>sb))"
  oops

lemma dastatesem_final_h2:
  shows "(daStateSem automat s)\<cdot>(sbECons sbe\<cdot>sb) =
  (daNextOut automat s sbe) \<bullet>\<^sup>\<Omega> ((daStateSem automat (daNextState automat s sbe))\<cdot>sb)"
  oops (* Das soll gehen mit "by(simp add: dastatesem_step)". Wenn nicht, mehr in den simplifier packen *)

lemma dastatesem_stepI:
  assumes "(daNextOut da s sbe) = out"
      and "(daNextState da s sbe) = nextState"
  shows "(daStateSem da s)\<cdot>(sbECons sbe\<cdot>sb) = out  \<bullet>\<^sup>\<Omega> ((daStateSem da nextState)\<cdot>sb)"
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
  by (simp add: daSem_def  dastatesem_bottom)

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
