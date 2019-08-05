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

lemma iup_up: "Iup a = up\<cdot>a"
  by (simp add: up_def cont_Iup)

lemma dastatesem_bot_step:
  assumes "chIsEmpty TYPE('b::{chan,finite})"
  shows "daStateSem da s\<cdot>(\<bottom>::'b\<^sup>\<Omega>) = (daNextOut da s (Abs_sbElem None)) \<bullet>\<^sup>\<Omega> (daStateSem da (daNextState da s (Abs_sbElem None))\<cdot>\<bottom>)"
  apply (subst dastatesem_unfolding)
  apply (simp add: sb_case_insert)
  apply (simp add: sbHdElem_h_cont.rep_eq sbHdElem_h_def)
  apply (rule conjI)
  apply (rule impI)
  apply (simp add: iup_up)
  apply (simp add: case_prod_unfold)
  apply (simp add: daNextOut_def daNextState_def)
  using assms by (simp add: chIsEmpty_def)



lemma assumes "\<forall>x. P x"
  shows "\<And>x. P x"
  using assms by auto

lemma assumes "\<forall>k. n \<noteq> Fin k"
  shows "n = \<infinity>"
  by (simp add: assms infI)

lemma sblen_slen_fin_eq: 
  assumes "sbLen (sb::'a\<^sup>\<Omega>) = Fin k"
  shows "\<exists>c. #(sb \<^enum> c) = Fin k"
  by (metis SBv3.lnat.distinct(2) assms sblen2slen sblen_min_len_empty)

lemma sbtake_pref: "sbTake i\<cdot>sb \<sqsubseteq> sb"
  by (simp add: sb_belowI)

lemma sbtake_len_fin: 
  assumes "Fin i \<le> sbLen (sb::'a\<^sup>\<Omega>)"
  shows   "sbLen (sbTake i\<cdot>sb) = Fin i"
  apply (simp add: sbtake_insert)
  apply (simp add: sbgetch_insert)
  oops

lemma sblen_sbhdelemwell:
  fixes sb :: "'b\<^sup>\<Omega>"
  assumes "sbLen sb \<ge> 1"
    and "\<not>chIsEmpty TYPE('b)"
  shows "sbHdElemWell sb"
  by (metis Stream.slen_empty_eq add.left_neutral assms fold_inf inf_ub leD ln_less lnat.con_rews lnat_plus_suc lnzero_def order.not_eq_order_implies_strict order.trans sbHdElemWell_def sblen_min_len)

lemma sbhdelemwell_type_nempty: assumes "sbHdElemWell (sb::'b\<^sup>\<Omega>)"
  shows "\<not>chIsEmpty TYPE('b)" 
  apply (rule ccontr, simp)
  using assms
  by (simp add: sbHdElemWell_def)

lemma nempty_slen: assumes "s \<noteq> \<epsilon>"
  shows "#s \<ge> 1"
  apply (rule ccontr)
  apply (subgoal_tac "s = \<epsilon>")
  using assms apply simp
  by (metis add.commute add.right_neutral assms lnat_plus_suc lnle_conv lnzero_def minimal monofun_cfun_arg srt_decrements_length)


lemma assumes "sbHdElemWell sb"
  shows "sbLen sb \<ge> 1"
  apply (cases "chIsEmpty TYPE('a)")
  apply (simp add: sbhdelemwell_type_nempty assms)  
  apply (simp add: sbLen_def)
  apply (subgoal_tac "\<And>c. #(sb  \<^enum>  c) \<ge> 1")
  apply (rule LeastI2_ex)
  apply blast
  using inf_ub apply blast
  using assms
  by (simp add: nempty_slen sbHdElemWell_def)

lemma sbhdelemwell_sbconc: assumes "sbHdElemWell (sb1::'b\<^sup>\<Omega>)"
  shows "sbHdElemWell (sb1 \<bullet>\<^sup>\<Omega> sb2)"
  by (metis assms sbHdElemWell_def sbconc_getch sconc_snd_empty strictI)

lemma sblen_fin_chisnempty: assumes "\<exists>k. sbLen (sb::('a::{chan})\<^sup>\<Omega>) = Fin k"
  shows "\<not>chIsEmpty TYPE('a)"
  using assms by auto

lemma funcomp_abs_sb:
  assumes "sb_well (\<lambda>c::'a. g\<cdot>(sb  \<^enum>  c))"
  shows "Abs_sb (\<lambda>c::'a. f\<cdot>(Abs_sb (\<lambda>c::'a. g\<cdot>(sb  \<^enum>  c))  \<^enum>  c)) = Abs_sb (\<lambda>c::'a. f\<cdot>(g\<cdot>(sb \<^enum> c)))"
  apply (simp add: sbgetch_insert)
  apply (subst Abs_sb_inverse)
  apply (metis assms mem_Collect_eq sb_well_def sbgetch_insert2)
  using assms by blast

lemma sbdrop_sbrt: "sbDrop (Suc k)\<cdot>sb = sbRt\<cdot>(sbDrop k\<cdot>sb)"
proof (induction k)
  case 0
  have "sbDrop 0\<cdot>sb = sb"
    apply (simp add: sbdrop_insert)
    by (metis sbconv_eq sbconvert_insert)
  then show ?case
    by simp
next
  case (Suc k)
  have srt_sdrop: "\<And>s. srt\<cdot>s = sdrop 1\<cdot>s"
    by (simp add: sdrop_forw_rt)
  then show ?case
    apply (simp add: sbdrop_insert)
    apply (subst sdrop_back_rt)
    by (simp add: srt_sdrop funcomp_abs_sb)
qed

lemma sblen_sbdrop_zero: assumes "sbLen sb = 0"
  shows "sbLen (sbDrop k\<cdot>sb) = 0"
  apply (induction k)
  apply (simp add: sbdrop_insert)
  apply (metis (mono_tags) assms sbconv_eq sbconvert_insert)
  by (metis (mono_tags, lifting) Abs_sb_inverse Fin_02bot  Stream.slen_empty_eq assms bottomI 
      lnle_def lnzero_def mem_Collect_eq sbDrop.rep_eq sbdrop_bot sbdrop_well sbgetch_bot
      sbgetch_insert2 sblen_min_len sblen_min_len_empty sblen_slen_fin_eq strict_slen)

lemma assumes "sbLen sb = 0"
  shows "sbLen (sbRt\<cdot>sb) = 0"
  oops
    

lemma
  assumes "sbLen sb = Fin k"
  shows "sbLen (sbDrop k\<cdot>sb) = 0"
  using assms
  apply (induction k)
  apply (simp add: sbdrop_insert)
  apply (metis sbconv_eq sbconvert_insert)
  apply (subst sbdrop_sbrt)
  apply (simp add: sblen_sbdrop_zero)
  oops

lemma helper:"chIsEmpty TYPE('cs) \<Longrightarrow> \<bottom> = (Abs_sbElem None) \<bullet>\<^sup>\<surd> (\<bottom>::'cs\<^sup>\<Omega>)"
  by simp

lemma dastatesem_inempty_step:fixes automat::"('state, 'in::{chan, finite}, 'out) dAutomaton"
  assumes"chIsEmpty TYPE('in)"
  shows "daStateSem automat s\<cdot>\<bottom> = (daNextOut automat s (Abs_sbElem None)) \<bullet>\<^sup>\<Omega> 
         ((daStateSem automat (daNextState automat s (Abs_sbElem None)))\<cdot>\<bottom>)"
  apply(subst helper,simp add: assms)
  apply(subst dastatesem_final_h2)
  using assms by simp

lemma test:"y \<noteq> 0 \<Longrightarrow> x = x +y \<Longrightarrow> x = \<infinity>"
  using leI plus_unique_r by fastforce

lemma sblen_inempty:
  fixes automat::"('state, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "\<And>state sbe c. #((daNextOut automat state sbe) \<^enum> c) = 1"
  and "chIsEmpty TYPE('in)"
shows "sbLen (daStateSem automat s\<cdot>\<bottom>) = \<infinity>"
apply (rule infI)
apply (rule allI)
proof -
  fix k::nat
  show "sbLen (daStateSem automat s\<cdot>\<bottom>) \<noteq> Fin k"
    apply(induction k arbitrary: s,simp)
    apply(subst dastatesem_inempty_step,simp add: assms) 
    apply (metis Fin_02bot lnat.con_rews lnat_plus_commu assms(1) lnat_plus_suc lnzero_def sbconc_chan_len sblen_slen_fin_eq)
  proof(auto)
    fix s::'state and k::nat
    assume sblen:"(\<And>s::'state. sbLen (daStateSem automat s\<cdot>\<bottom>) \<noteq> Fin k)"
    assume sblen2:"sbLen (daStateSem automat s\<cdot>\<bottom>) = Fin (Suc k)"
    then have h0:"sbLen (daStateSem automat s\<cdot>\<bottom>) = sbLen ((daNextOut automat s (Abs_sbElem None)) \<bullet>\<^sup>\<Omega> 
           ((daStateSem automat (daNextState automat s (Abs_sbElem None)))\<cdot>\<bottom>))"
      by (metis assms(2) dastatesem_inempty_step)
    have h2:"sbLen ((daStateSem automat (daNextState automat s (Abs_sbElem None)))\<cdot>\<bottom>) \<noteq> Fin k"
      by (simp add: sblen)
    then have "sbLen ((daNextOut automat s (Abs_sbElem None)) \<bullet>\<^sup>\<Omega> 
           ((daStateSem automat (daNextState automat s (Abs_sbElem None)))\<cdot>\<bottom>)) = sbLen ((daStateSem automat (daNextState automat s (Abs_sbElem None)))\<cdot>\<bottom>) + 1"
      using sblen_sbconc_eq assms by blast
    then show "False"
      by (metis Fin_Suc h0 inject_lnsuc lnat_plus_suc local.h2 sblen2)
  qed
qed

lemma
  fixes automat::"('state, 'in::{chan, finite}, 'out) dAutomaton"
  assumes "\<And>state sbe. sbLen (daNextOut automat state sbe) \<ge> 1"
  and "chIsEmpty TYPE('in)"
shows "sbLen (daStateSem automat s\<cdot>\<bottom>) = \<infinity>"
proof-
  obtain lnat where lnat_def:"lnat = sbLen (daStateSem automat s\<cdot>\<bottom>)"
    by simp
  then have hlen:"lnat = sbLen ((daNextOut automat s (Abs_sbElem None)) \<bullet>\<^sup>\<Omega> 
         ((daStateSem automat (daNextState automat s (Abs_sbElem None)))\<cdot>\<bottom>))"
    by(simp add: lnat_def,subst  dastatesem_inempty_step, simp_all add: assms)
  have "\<And>state sbe. lnsuc\<cdot>(lnat) \<le> sbLen (daNextOut automat state sbe \<bullet>\<^sup>\<Omega> daStateSem automat s\<cdot>\<bottom>)"
    using sblen_sbconc assms lnat_def
    by (metis dual_order.trans lessequal_addition lnat_plus_commu lnat_plus_suc order_refl)
  then have "sbLen ((daStateSem automat (daNextState automat s (Abs_sbElem None)))\<cdot>\<bottom>) \<le>lnat"
    sorry
  then show "sbLen (daStateSem automat s\<cdot>\<bottom>) = \<infinity>"
    oops
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
