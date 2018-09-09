(*  Title:        Medium.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for Medium Definitions and Lemmata.
*)

chapter {* Theory for Medium Definitions and Lemmata *}

theory Medium
imports Components "../../../untimed/SPS"

begin

(* deletes the Rule "1 = Suc 0" *)
 declare One_nat_def[simp del]

(* ----------------------------------------------------------------------- *)
  section {* Medium Definition for Verification *}
(* ----------------------------------------------------------------------- *)

text{* @{term tsynMed}: Lossy medium on time-synchronous streams that gets messages and an oracle
       and will transmit the k-th message if the k-th element in the oracle is True, otherwise the 
       message will be discarded. *}
definition tsynMed :: "(nat \<times> bool) tsyn stream \<rightarrow> bool stream \<rightarrow> (nat \<times> bool) tsyn stream" where
  "tsynMed \<equiv> \<Lambda> msg ora. tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora))"

text {* @{term tsynbMed}: Lossy medium function on time-synchonous stream bundles. *}
definition tsynbMed :: "bool stream \<Rightarrow> 
  abpMessage tsyn stream ubundle \<rightarrow> abpMessage tsyn stream ubundle option" where
  "tsynbMed ora \<equiv> \<Lambda> sb. (ubDom\<cdot>sb = {\<C> ''ds''}) \<leadsto> Abs_ubundle [
                      \<C> ''dr'' \<mapsto> natbool2abp\<cdot>(tsynMed\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''ds''))\<cdot>ora)]"

text {* @{term MedSPF}: Lossy medium function for the Alternating Bit Protocol. *}
definition MedSPF :: "bool stream \<Rightarrow> abpMessage tsyn SPF" where
  "MedSPF ora \<equiv> Abs_ufun (tsynbMed ora)"

text{* @{term oraFun}: Function to create ora streams with True at position n.*}
definition oraFun :: "nat \<Rightarrow> bool stream set" where
  "oraFun n = {ora. (#({True} \<ominus> ora) = \<infinity> \<and> snth n ora \<and> (\<forall>k<n. \<not>snth k ora))}"

text {* @{term MedSPS}: Lossy medium function set for the Alternating Bit Protocol. *}
definition MedSPS :: "nat \<Rightarrow> abpMessage tsyn SPS" where 
  "MedSPS n = Abs_uspec (Rev {(MedSPF ora) | ora. ora \<in> (oraFun n)}, Discr {\<C> ''ds''}, 
  Discr {\<C> ''dr''})"


(* ----------------------------------------------------------------------- *)
section {* Basic Properties *}
(* ----------------------------------------------------------------------- *)

text {* Induction rule for infinite time-synchronous bool streams and admissable predicates. *}
lemma ora_ind [case_names adm bot msg_t msg_f]:
  assumes adm: "adm P"
    and bot: "P \<epsilon>"
    and msg_t: "\<And>s. P s \<Longrightarrow> P (\<up>True \<bullet> s)"
    and msg_f: "\<And>s. P s \<Longrightarrow> P (\<up>False \<bullet> s)"
  shows "P (x:: bool stream)"
  apply (induction x rule: ind)
  apply (simp_all add: adm bot)
  apply (rename_tac x y)
  apply (case_tac x)
  by (simp_all add: msg_t msg_f)

text {* If a predicate P holds for empty streams, true and false predicates, 
        it holds for all ora-streams. *}
lemma oracases [case_names bot true false]:
  assumes bot: "s = \<epsilon> \<Longrightarrow> P s"
    and true: "\<And>as. s = (\<up>True \<bullet> as) \<Longrightarrow> P s"
    and false: "\<And>as. s = (\<up>False \<bullet> as) \<Longrightarrow> P s"
  shows "P s"
  by (metis (full_types) bot false scases true)

(* ----------------------------------------------------------------------- *)
subsection {* Basic Properties of tsynMed *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynMed} insertion lemma. *}
lemma tsynmed_insert: "tsynMed\<cdot>msg\<cdot>ora = tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora))"
  by (simp add: tsynMed_def)

text {* @{term tsynMed} is strict for both arguments. *}
lemma tsynmed_strict [simp]: 
  "tsynMed\<cdot>\<epsilon>\<cdot>\<epsilon> = \<epsilon>"
  "tsynMed\<cdot>msg\<cdot>\<epsilon> = \<epsilon>"
  "tsynMed\<cdot>\<epsilon>\<cdot>ora = \<epsilon>"
  by (simp add: tsynMed_def)+

text{* If the first element in the oracle is True then the current message will be transmitted. *}
lemma tsynmed_sconc_msg_t: "tsynMed\<cdot>(\<up>(Msg m) \<bullet> msg)\<cdot>(\<up>True \<bullet> ora) = \<up>(Msg m) \<bullet> (tsynMed\<cdot>msg\<cdot>ora)"
  by (simp add: tsynmed_insert tsynzip_sconc_msg tsynfilter_sconc_msg_in tsynfilter_sconc_null 
                tsynprojfst_sconc_null tsynprojfst_sconc_msg)

text{* If the first element in the oracle is False then the current message will not be
       transmitted. *}
lemma tsynmed_sconc_msg_f: "tsynMed\<cdot>(\<up>(Msg m) \<bullet> msg)\<cdot>(\<up>False \<bullet> ora) = \<up>- \<bullet> tsynMed\<cdot>msg\<cdot>ora"
  by (simp add: tsynmed_insert tsynzip_sconc_msg tsynfilter_sconc_msg_nin tsynprojfst_sconc_null)

text{* If the first element in the stream is null the oracle will not change. *}
lemma tsynmed_sconc_null:
  assumes "ora \<noteq> \<epsilon>"
  shows "tsynMed\<cdot>(\<up>- \<bullet> msg)\<cdot>ora = \<up>- \<bullet> tsynMed\<cdot>msg\<cdot>ora"
  by (simp add: assms tsynmed_insert tsynfilter_sconc_null tsynprojfst_sconc_null 
      tsynzip_sconc_null)

text {* If the first element in the oracle is True, the only message will be transmitted. *}
lemma tsynmed_sconc_singleton_msg_t: "tsynMed\<cdot>(\<up>(\<M> m))\<cdot>(\<up>True \<bullet> ora) = \<up>(\<M> m)"
  by (metis lscons_conv sup'_def tsynmed_sconc_msg_t tsynmed_strict(3))

text {* If the first element in the oracle is False, the only message will not be transmitted. *}
lemma tsynmed_sconc_singleton_msg_f: "tsynMed\<cdot>(\<up>(\<M> m))\<cdot>(\<up>False \<bullet> ora) = \<up>-"
  by (metis lscons_conv sup'_def tsynmed_sconc_msg_f tsynmed_strict(3))

text {* If the stream only contains null and the oracle is not empty, no message will be 
        transmitted. *}
lemma tsynmed_sconc_singleton_msg_null: assumes "ora \<noteq> \<epsilon>" shows "tsynMed\<cdot>(\<up>-)\<cdot>ora = \<up>-"
  by (metis assms lscons_conv sup'_def tsynmed_sconc_null tsynmed_strict(3))

text {* If the ora stream has infinite length, the output of @{term tsynMed} has the same length as 
        the msg stream. *}
lemma tsynmed_slen: assumes "#ora = \<infinity>" shows "#(tsynMed\<cdot>msg\<cdot>ora) = #msg"
  by (simp add: assms tsynfilter_slen tsynmed_insert tsynprojfst_slen tsynzip_slen)

text {* Not every message will be transmitted. *}    
lemma tsynmed_tsynlen: 
  assumes "#ora = \<infinity>" 
  shows "tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>ora) \<le> tsynLen\<cdot>msg"
  using assms
  proof-
    assume ora_inf: "#ora = \<infinity>"
    hence "tsynLen\<cdot>(tsynProjFst\<cdot>(tsynFilter (Collect snd)\<cdot>(tsynZip\<cdot>msg\<cdot>ora))) \<le> tsynLen\<cdot>msg"
      by (metis tsynfilter_tsynlen tsynprojfst_tsynlen tsynzip_tsynlen)
    thus ?thesis
      by (simp add: tsynmed_insert)
  qed

text{* The transmitted messages are a subset of the messages that are provided for transmission. *}
lemma tsynmed_tsyndom: "tsynDom\<cdot>(tsynMed\<cdot>msg\<cdot>ora) \<subseteq> tsynDom\<cdot>msg"
  proof (induction msg arbitrary: ora rule: tsyn_ind)
    case adm
    then show ?case 
      by (simp add: adm_def contlub_cfun_arg contlub_cfun_fun lub_eq_Union SUP_subset_mono)
  next
    case bot
    then show ?case 
      by simp
  next
    case (msg m s)
    then show ?case 
      proof (cases rule: oracases [of ora])
        case bot
        then show ?thesis 
            by (simp add: tsyndom_strict)
      next
        case (true as)
        then show ?thesis
          by (simp add: true tsynmed_sconc_msg_t tsyndom_sconc le_supI2 msg.IH)
      next 
        case (false as)
        then show ?thesis
          by (metis (no_types, hide_lams) dual_order.trans msg.IH order_refl tsyndom_sconc_msg_sub 
              tsyndom_sconc_null tsynmed_sconc_msg_f)
       qed
  next
    case (null s)
    then show ?case
      by (metis tsyndom_sconc_null tsynmed_sconc_null tsynmed_strict(2))
  qed

text {* If msg starts with k ticks, the output of @{term tsynMed} will do as well. *}
lemma tsynmed_sntimes_null: 
  assumes "ora \<noteq> \<epsilon>"
  shows "tsynMed\<cdot>((k \<star> \<up>null) \<bullet> msg)\<cdot>ora = (k \<star> \<up>null) \<bullet> tsynMed\<cdot>msg\<cdot>ora"
  using assms
  apply (induction k, simp_all)
  apply (cases rule: oracases [of ora])
  by (simp_all add: tsynmed_sconc_null)

(* Move to tsynStream. *)
text {* @{term tsynLen} will consume leading ticks. *}
lemma tsynlen_sntimes_null: "tsynLen\<cdot>((k \<star> \<up>null) \<bullet> s) = tsynLen\<cdot>s"
  apply (induction k)
  by (simp_all add: tsynlen_sconc_null)

(* Reviewed until here *)

(* Move to tsynStream. *)
text {* If @{term tsynLen} is not 0, it cannot contain infinitely many ticks. *}
lemma stakewhile_null_slen_fin: 
  assumes "0 < tsynLen\<cdot>as" 
  shows "#(stakewhile (\<lambda>x. x = null)\<cdot>as) < \<infinity>"
  proof -
    obtain k where "snth k as \<noteq> null"
      using assms
      by (metis (full_types) empty_is_shortest ex_snth_in_sfilter_nempty linorder_neq_iff 
          mem_Collect_eq tsynabs_insert tsynlen_insert tsynlen_strict)
    then show ?thesis
      by (metis (full_types) inf_ub neq_iff not_le notinfI3 stakewhile_slen)
  qed

text {* If @{term tsynLen} is not 0, we can extract the number of leading ticks. *}
lemma split_leading_null:
  assumes "0 < tsynLen\<cdot>as"
  obtains n where "as = (sntimes n (\<up>null)) \<bullet> sdropwhile (\<lambda>x. x = null)\<cdot>as"
  proof -
    obtain k where k_def: "#(stakewhile (\<lambda>x. x = null)\<cdot>as) = Fin k"
      by (metis assms inf_ub lncases not_le stakewhile_null_slen_fin)
    then have "(sntimes k (\<up>null)) = (stakewhile (\<lambda>x. x = null)\<cdot>as)"
      proof (induction as arbitrary: k rule: tsyn_ind)
        case adm
        then show ?case 
          proof (rule admI)
            fix Y :: "nat \<Rightarrow> 'a tsyn stream"
            assume chain_Y: "chain Y" 
            assume adm_hyp: "\<forall> i x. #(stakewhile (\<lambda>x. x = -)\<cdot>(Y i)) = Fin x
                                      \<longrightarrow> x\<star>\<up>- = stakewhile (\<lambda>x::'a tsyn. x = -)\<cdot>(Y i)"
            thus "\<forall>x. #(stakewhile (\<lambda>x. x = -)\<cdot>(\<Squnion>i. Y i)) = Fin x 
                        \<longrightarrow> x\<star>\<up>- = stakewhile (\<lambda>x. x = -)\<cdot>(\<Squnion>i. Y i)"
            by (metis (no_types, lifting) ch2ch_Rep_cfunR chain_Y contlub_cfun_arg finChainapprox)
          qed
      next
        case bot
        then show ?case
          by simp
      next
        case (msg m s)
        then show ?case 
          by simp
      next
        case (null s)
        then show ?case
          using infI slen_sconc_snd_inf slen_scons sntimes.simps(2) by fastforce
      qed
    then show ?thesis
      by (metis stakewhileDropwhile that)
  qed

text{* The number of transmitted messages equals the number of True in ora. *}
lemma tsynmed_tsynlen_ora:
  assumes msg_inf: "tsynLen\<cdot>msg = \<infinity>"
  shows "tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>ora) = #({True} \<ominus> ora)"
  using assms
  proof (induction ora arbitrary: msg rule: ind)
    case 1
    then show ?case 
      by (simp add: adm_def contlub_cfun_arg contlub_cfun_fun)
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    have tsynlen_nzero: "0 < tsynLen\<cdot>msg"
      using Zero_lnless_infty "3.prems" by auto
    then obtain n where msg_def: "msg = (sntimes n (\<up>null)) \<bullet> sdropwhile (\<lambda>x. x = null)\<cdot>msg"
      using split_leading_null by blast
    have sdropwhile_null_nbot: "sdropwhile (\<lambda>x. x = null)\<cdot>msg \<noteq> \<epsilon>"
      by (metis Inf'_neq_0 msg_def "3.prems" tsynlen_sntimes_null tsynlen_strict)
    from sdropwhile_null_nbot obtain m where m_def: "shd (sdropwhile (\<lambda>x. x = null)\<cdot>msg) = Msg m"
      by (metis (full_types) scases sdropwhile_resup shd1 tsynSnd.cases)
    have tsynlen_srt_sdropwhile_null_inf: "tsynLen\<cdot>(srt\<cdot>(sdropwhile (\<lambda>x. x = null)\<cdot>msg)) = \<infinity>"
      by (metis m_def fold_inf lnat.sel_rews(2) msg_def "3.prems" sdropwhile_null_nbot surj_scons 
          tsynlen_sconc_msg tsynlen_sntimes_null)
    have tsynmed_consume_tick:
      "tsynLen\<cdot>(tsynMed\<cdot>((sntimes n (\<up>null)) \<bullet> sdropwhile (\<lambda>x. x = null)\<cdot>msg)\<cdot>(\<up>a \<bullet> s))
         = tsynLen\<cdot>(tsynMed\<cdot>(sdropwhile (\<lambda>x. x = null)\<cdot>msg)\<cdot>(\<up>a \<bullet> s))"
      by (simp add: tsynmed_sntimes_null tsynlen_sntimes_null)
    show ?case
      proof -
        have thesis_msg: "tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>(\<up>a \<bullet> s)) 
          = tsynLen\<cdot>(tsynMed\<cdot>((sntimes n (\<up>null)) \<bullet> (sdropwhile (\<lambda>x. x = null))\<cdot>msg)\<cdot>(\<up>a \<bullet> s))"
          using msg_def by simp
        then show ?thesis
          proof (cases a)
            case True
            have sdropwhile_true: 
              "#\<^sub>-(tsynMed\<cdot>msg\<cdot>(\<up>True \<bullet> s)) = #\<^sub>-(tsynMed\<cdot>(sdropwhile (\<lambda>x. x = null)\<cdot>msg)\<cdot>(\<up>True \<bullet> s))"
              using True thesis_msg tsynmed_consume_tick by auto
            then have snth_tick: 
              "#\<^sub>-(tsynMed\<cdot>(sdropwhile (\<lambda>x. x = -)\<cdot>msg)\<cdot>(\<up>True \<bullet> s)) 
                 = #\<^sub>-(tsynMed\<cdot>(n\<star>\<up>- \<bullet> sdropwhile (\<lambda>x. x = null)\<cdot>msg)\<cdot>(\<up>True \<bullet> s))"
              using msg_def by auto
            then have tsynmed_snth_tick: 
              "#\<^sub>-(tsynMed\<cdot>(n\<star>\<up>- \<bullet> sdropwhile (\<lambda>x. x = null)\<cdot>msg)\<cdot>(\<up>True \<bullet> s)) = lnsuc\<cdot>(#({True} \<ominus> s))"
              by (metis "3.IH" m_def sdropwhile_null_nbot surj_scons tsynlen_sconc_msg 
                  tsynlen_srt_sdropwhile_null_inf tsynmed_sconc_msg_t)
            then show ?thesis
              using True msg_def by auto
          next
            case False
            have sdropwhile_false: 
              "#\<^sub>-(tsynMed\<cdot>msg\<cdot>(\<up>False \<bullet> s)) = #\<^sub>-(tsynMed\<cdot>(sdropwhile (\<lambda>x. x = -)\<cdot>msg)\<cdot>(\<up>False \<bullet> s))"
              using False thesis_msg tsynmed_consume_tick by auto
            have snth_tick: "#\<^sub>-(tsynMed\<cdot>(sdropwhile (\<lambda>x. x = -)\<cdot>msg)\<cdot>(\<up>False \<bullet> s)) =
              #\<^sub>-(tsynMed\<cdot>(n\<star>\<up>- \<bullet> sdropwhile (\<lambda>x. x = -)\<cdot>msg)\<cdot>(\<up>False \<bullet> s))"
              using False tsynmed_consume_tick by auto
            have tsynmed_snth_tick: 
              "#\<^sub>-(tsynMed\<cdot>(n\<star>\<up>- \<bullet> sdropwhile (\<lambda>x. x = -)\<cdot>msg)\<cdot>(\<up>False \<bullet> s)) = #({True} \<ominus> s)"
              by (metis "3.IH" m_def msg_def sdropwhile_false sdropwhile_null_nbot surj_scons 
                  tsynlen_sconc_null tsynlen_srt_sdropwhile_null_inf tsynmed_sconc_msg_f)
            then show ?thesis
              using False thesis_msg by auto
          qed
      qed
   qed

text{* If infinitely many messages are sent, infinitely many messages will be transmitted. *}
lemma tsynmed_tsynlen_inf:
  assumes "#({True} \<ominus> ora) = \<infinity>" 
    and "tsynLen\<cdot>msg = \<infinity>"
  shows "tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>ora) = \<infinity>"
  using assms by (simp add: tsynmed_tsynlen_ora)

text {* @{term tsynMed} test on finite stream with ticks. *}
lemma tsynmed_test_finstream_null:
  "tsynMed\<cdot>(<[null, null, Msg (2,False), Msg (1, True), Msg (3, True)]>)\<cdot>(<[True, False, True]>) 
    = <[null, null, Msg (2,False), null, Msg (3, True)]>"
  sorry

text {* @{term tsynMed} test on infinite stream. *}
lemma tsynrec_test_infstream:
  "tsynMed\<cdot>((<[Msg(3, False), null, Msg(2, True),Msg(1, False)]>)\<infinity>)\<cdot>((<[True, False, True]>)\<infinity>)
    =(<[Msg(3, False), null, null, Msg(1, False)]>)\<infinity>"
  sorry

(* ----------------------------------------------------------------------- *)
subsection {* basic properties of tsynbMed *}
(* ----------------------------------------------------------------------- *)

text{* The output bundle of @{term tsynbMed} is well-formed. *}
lemma tsynbmed_ubwell [simp]: 
  "ubWell [\<C> ''dr'' \<mapsto> natbool2abp\<cdot>(tsynMed\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''ds''))\<cdot>ora)]"
  apply (simp add: ubWell_def usclOkay_stream_def natbool2abp_def abp2natbool_def ctype_tsyn_def
          tsynmap_insert smap_sdom image_subset_iff)
  by (metis image_eqI range_eqI tsynApplyElem.elims)

text{* The domain of the output bundle of @{term tsynbMed}. *}
lemma tsynbmed_ubundle_ubdom: "ubDom\<cdot>(Abs_ubundle 
  [\<C> ''dr'' \<mapsto> natbool2abp\<cdot>(tsynMed\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''ds''))\<cdot>ora)]) = {\<C> ''dr''}"
  by (simp add: ubdom_insert)

text{* @{term tsynbMed} is monotonous. *}
lemma tsynbmed_mono [simp]:
  "monofun (\<lambda> sb. (ubDom\<cdot>sb = {\<C> ''ds''}) \<leadsto> Abs_ubundle [
                      \<C> ''dr'' \<mapsto> natbool2abp\<cdot>(tsynMed\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''ds''))\<cdot>ora)])"
  apply (fold ubclDom_ubundle_def)
  apply (rule ufun_monoI3)
  apply (rule monofunI)
  apply (simp add: below_ubundle_def)
  by (simp add: below_ubundle_def cont_pref_eq1I fun_below_iff monofun_cfun_fun some_below)

text{* Chain on the output bundle of @{term tsynbMed}. *}
lemma tsynbmed_chain: "chain Y \<Longrightarrow> 
      chain (\<lambda>i::nat.[\<C> ''dr'' \<mapsto> natbool2abp\<cdot>(tsynMed\<cdot>(abp2natbool\<cdot>(Y i  .  \<C> ''ds''))\<cdot>ora)])"
  by (simp add: chain_def fun_below_iff monofun_cfun_arg monofun_cfun_fun po_class.chainE 
                some_below)

text{* @{term tsynbMed} is continuous. *}
lemma tsynbmed_cont [simp]:
  "cont (\<lambda> sb. (ubDom\<cdot>sb = {\<C> ''ds''}) \<leadsto> Abs_ubundle [
                      \<C> ''dr'' \<mapsto> natbool2abp\<cdot>(tsynMed\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''ds''))\<cdot>ora)])"
  apply (fold ubclDom_ubundle_def)
  apply (rule ufun_contI2)
  apply (rule cont_Abs_UB)
  apply (rule contI2)
  apply (rule monofunI, simp_all)
  apply (simp add: fun_belowI monofun_cfun_arg monofun_cfun_fun some_below)
  using tsynbmed_chain 
  by (simp add: contlub_cfun_arg contlub_cfun_fun fun_below_iff some_lub_chain_eq lub_fun)

text{* @{term tsynbMed} insertion lemma. *}
lemma tsynbmed_insert: "tsynbMed ora\<cdot>sb = (ubDom\<cdot>sb = {\<C> ''ds''}) \<leadsto> Abs_ubundle [
                      \<C> ''dr'' \<mapsto> natbool2abp\<cdot>(tsynMed\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''ds''))\<cdot>ora)]"
  by (simp add: tsynbMed_def ubclDom_ubundle_def)

text{* @{term tsynbMed} is well-formed. *}
lemma tsynbmed_ufwell [simp]: "ufWell (tsynbMed ora)"
  apply (rule ufun_wellI [of "tsynbMed ora" "{\<C> ''ds''}" "{\<C> ''dr''}"])
  apply (simp_all add: ubclDom_ubundle_def domIff tsynbmed_insert)
  apply (meson option.distinct(1))
  by (metis option.distinct(1) tsynbmed_ubundle_ubdom)

text {* The output stream of @{term tsynbMed}} on channel dr. *}
lemma tsynbmed_getch_dr:
  assumes "ubDom\<cdot>sb = {\<C> ''ds''}"
  shows "((Rep_cfun (tsynbMed ora)) \<rightharpoonup> sb) . \<C> ''dr'' 
    =  natbool2abp\<cdot>(tsynMed\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''ds''))\<cdot>ora)"
  by (simp add: tsynbmed_insert assms ubgetch_ubrep_eq)

(* ----------------------------------------------------------------------- *)
subsection {* basic properties of MedSPF *}
(* ----------------------------------------------------------------------- *)

text{* @{term MedSPF} insertion lemma. *}
lemma medspf_insert: "(MedSPF ora) \<rightleftharpoons> sb = (Abs_ufun (tsynbMed ora)) \<rightleftharpoons> sb"
  by (simp add: MedSPF_def)

text{* The domain of @{term MedSPF}. *}
lemma medspf_ufdom: "ufDom\<cdot>(MedSPF ora) = {\<C> ''ds''}"
  apply (simp add: ufDom_def)
  apply (simp add: ubclDom_ubundle_def MedSPF_def tsynbMed_def)
  apply (subst rep_abs_cufun2)
  using tsynbMed_def tsynbmed_ufwell apply simp
  apply (simp add: domIff)
  by (meson someI tsynbnull_ubdom)

text{* The range of @{term MedSPF}. *}
lemma medspf_ufran: "ufRan\<cdot>(MedSPF ora) = {\<C> ''dr''}"
  apply (simp add: ufran_least)
  apply (simp add: ubclLeast_ubundle_def medspf_ufdom ubclDom_ubundle_def)
  apply (simp add: MedSPF_def tsynbmed_insert tsynbmed_ubundle_ubdom)
  apply (simp add: ubdom_insert)
  apply (subst ubrep_ubabs, simp_all)
  by (simp add: ubWell_def usclOkay_stream_def natbool2abp_def abp2natbool_def)

text{* The domain of the output bundle of @{term MedSPF}. *}
lemma medspf_ubdom:
  assumes "ubDom\<cdot>sb = ufDom\<cdot>(MedSPF ora)"
  shows "ubDom\<cdot>((MedSPF ora) \<rightleftharpoons> sb) = {\<C> ''dr''}"
  by (simp add: assms medspf_ufran spf_ubDom)

text{* @{term MedSPF} is strict. *}
lemma medspf_strict: "(MedSPF ora) \<rightleftharpoons> ubLeast{\<C> ''ds''} = ubLeast{\<C> ''dr''}"
  proof -
    have eq_empty: "natbool2abp\<cdot>(tsynMed\<cdot>(abp2natbool\<cdot>(ubLeast {\<C> ''ds''} . 
        \<C> ''ds''))\<cdot>ora) =  \<bottom>" 
      by (simp add: abp2natbool_def natbool2abp_def)
    have partial_eq:" [\<C> ''dr'' \<mapsto> \<bottom>] =  (\<lambda>a. (a \<in> {\<C> ''dr''}) \<leadsto> \<bottom>)" 
      by (simp add: fun_upd_def)
    hence "Abs_ubundle [\<C> ''dr'' \<mapsto> \<bottom>] = ubLeast {\<C> ''dr''}" 
      by (simp add: partial_eq ubLeast_def)
    hence "Rep_cfun (tsynbMed ora) \<rightharpoonup> ubLeast {\<C> ''ds''} = ubLeast {\<C> ''dr''}" 
      using tsynbMed_def eq_empty by simp 
    thus ?thesis by (simp add: medspf_insert)
  qed

(* ----------------------------------------------------------------------- *)
subsection {* MedSPF step lemmata *}
(* ----------------------------------------------------------------------- *)

(*lemma copied can be deleted *)
lemma spfConcIn_step[simp]:
  assumes  "ubDom\<cdot>sb = ufDom\<cdot>spf"
  shows "(spfConcIn sb1\<cdot>spf) \<rightleftharpoons> sb = spf \<rightleftharpoons> (ubConcEq sb1\<cdot>sb)" 
  by (simp_all add: assms spfConcIn_def ubclDom_ubundle_def Int_absorb1)

lemma orafun_snth: "ora \<in> oraFun n \<Longrightarrow> snth n ora"
  by (simp add: oraFun_def)

lemma orafun_nbot: "ora \<in> oraFun n \<Longrightarrow> ora \<noteq> \<epsilon>"
  using oraFun_def by force

lemma orafun_nempty: "oraFun n \<noteq> {}"
  proof -
  obtain ora where ora_def: "ora = ((n \<star> \<up>False) \<bullet> ((\<up>True)\<infinity>))"
    by simp
  have ora_fair: "#({True} \<ominus> ora) = \<infinity>"
    using insert_not_empty ora_def by simp
  have sdrop_empty: "sdrop n\<cdot>(n\<star>\<up>False) = \<bottom>"
    by (simp add: sdropostake sntimes_stake)
  then have sdrop_empty: "sdrop n\<cdot>ora = \<up>True\<infinity>"
    by (simp add: ora_def sdropl6)
  then have snth_true: "snth n ora"
    by (simp add: snth_def)
  have sdrop_k: "\<And>k. k<n \<Longrightarrow> sdrop k\<cdot>(n\<star>\<up>False) = (n-k)\<star>\<up>False"
    by (metis (no_types, lifting) add_diff_inverse_nat less_Suc_eq not_less_eq sdropl6 sdrops_sinf 
      sntimes_len sntimes_stake stake_add)
  then have snth_false: "\<forall>k<n. \<not> snth k ora"
    by (metis less2nat linorder_not_le ora_def shd_sntime slen_snth_prefix snth_def sntimes_len 
    zero_less_diff)
  have "ora \<in> oraFun n"
    by (simp add: oraFun_def ora_fair snth_false snth_true)
  then show ?thesis
    by blast
  qed

lemma medspf_spfconc_null: assumes "ora \<in> oraFun n"  
  shows "spfConcIn (tsynbNull(\<C> ''ds''))\<cdot>(MedSPF ora) = spfConcOut (tsynbNull(\<C> ''dr''))\<cdot>(MedSPF ora)"
  apply (rule spf_eq)
  apply (simp add: medspf_ufdom)+
  apply (subst medspf_ubdom)
  apply (simp add: medspf_ufdom)
  apply (rule ub_eq)
  apply (simp add: medspf_ubdom medspf_ufdom)+
  using assms
  by (simp add: medspf_insert tsynbmed_getch_dr usclConc_stream_def abp2natbool_def natbool2abp_def
  tsynmap_sconc_null orafun_nbot tsynmed_sconc_null)

lemma createdsbundle_ubdom: "ubDom\<cdot>(createDsBundle a)= {\<C> ''ds''}"
  by (simp add: ubDom_def createDsBundle.rep_eq)

lemma createdsbundle_ubgetch: "createDsBundle m . \<C> ''ds'' = \<up> (\<M> (Pair_nat_bool m))"
  by (simp add: ubgetch_insert createDsBundle.rep_eq)

lemma medspf_spfconc_msg_nzero: assumes "ora1 \<in> oraFun (Suc n)" obtains ora2 where "ora2 \<in> oraFun n"
  and "spfConcIn (createDsBundle m)\<cdot>(MedSPF ora1) = spfConcOut (tsynbNull(\<C> ''dr''))\<cdot>(MedSPF ora2)"
  using assms
  proof -
    have ora1_shd_f: "\<not>(snth 0 ora1)"
      by (metis (no_types, lifting) CollectD assms oraFun_def zero_less_Suc)
    obtain ora2 where ora2def: "ora1 = \<up>False \<bullet> ora2"
      by (metis (full_types) ora1_shd_f assms orafun_nbot snth_shd surj_scons)
    have ora2_fair: "#({True} \<ominus> ora2) = \<infinity>"
      using assms ora2def oraFun_def by simp
    have ora2_snth: "snth n ora2"
      using assms ora2def orafun_snth snth_scons by blast
    have ora2_f: "(\<forall>k<n. \<not> snth k ora2)"
      by (metis (no_types, lifting) CollectD Suc_less_eq assms ora2def oraFun_def snth_scons)
    have ora2_orafun: "ora2 \<in> oraFun n"
      by (simp add: ora2_f ora2_fair ora2_snth oraFun_def)
    have "spfConcIn (createDsBundle m)\<cdot>(MedSPF ora1) = spfConcOut (tsynbNull(\<C> ''dr''))\<cdot>(MedSPF ora2)"
      apply (rule spf_eq)
      apply (simp add: medspf_ufdom)+
      apply (subst medspf_ubdom)
      apply (simp add: medspf_ufdom)
      apply (rule ub_eq)
      apply (simp add: medspf_ubdom medspf_ufdom)+
      using assms
      by (simp add: medspf_insert tsynbmed_getch_dr usclConc_stream_def abp2natbool_def 
        natbool2abp_def ora2def createdsbundle_ubdom createdsbundle_ubgetch tsynmap_sconc_msg 
        tsynmed_sconc_msg_f tsynmap_sconc_null)
   then show ?thesis
     using ora2_orafun that by simp
  qed           

lemma medspf_spfconc_msg_zero: assumes "ora1 \<in> oraFun 0" obtains ora2 where "ora2 \<in> oraFun n"
  and "spfConcIn (createDsBundle m)\<cdot>(MedSPF ora1) = spfConcOut (createDrBundle m)\<cdot>(MedSPF ora2)"
  using assms
  proof -
    obtain ora2 where ora2def: "ora2 \<in> oraFun n"
      by (meson orafun_nempty subsetI subset_empty)
oops

(* ----------------------------------------------------------------------- *)
subsection {* Basic Properties of MedSPSspec *}
(* ----------------------------------------------------------------------- *)

text{* @{term MedSPS} is well-formed. *}
lemma medsps_uspecwell [simp]: 
  "uspecWell (Rev {(MedSPF ora) | ora. (#({True} \<ominus> ora) = \<infinity> \<and> snth n ora
   \<and> (\<forall>k<n. \<not>snth k ora))}) (Discr {\<C> ''ds''}) (Discr {\<C> ''dr''})"
  apply (rule uspec_wellI)
  apply (simp add: ufclDom_ufun_def)
  using medspf_ufdom apply blast
  apply (simp add: ufclRan_ufun_def)
  using medspf_ufran by blast

text{* The domain of @{term MedSPS}. *}
lemma medsps_uspecdom: "uspecDom\<cdot>(MedSPS n) = {\<C> ''ds''}"
  using medsps_uspecwell
  by (simp add: MedSPS_def uspecdom_insert oraFun_def)

text{* The range of @{term MedSPS}. *}
lemma medsps_uspecran: "uspecRan\<cdot>(MedSPS n) = {\<C> ''dr''}"
  using medsps_uspecwell 
  by (simp add: MedSPS_def uspecran_insert oraFun_def)

(* ----------------------------------------------------------------------- *)
subsection {* Medium State Lemmata *}
(* ----------------------------------------------------------------------- *)

text{* The nth element of ora will be true. *}
lemma snth_ora_true: assumes "#({True} \<ominus> ora) = \<infinity>" obtains n where "snth n ora = True"
  by (metis Inf'_neq_0_rev assms ex_snth_in_sfilter_nempty singleton_iff slen_empty_eq)

lemma slen_createbundle_getch: "#(createBundle (\<M> m) c  .  c) < \<infinity>"
  apply (simp add: ubgetch_insert createBundle_def)
  by (metis Fin_02bot Fin_Suc Fin_neq_inf bot_is_0 createBundle.rep_eq fun_upd_same inf_ub 
    lscons_conv option.sel order_less_le slen_scons strict_slen sup'_def ubabs_ubrep)

lemma medsps_0_uspecwell: 
  "uspecWell (Rev{MedSPF ora |ora::bool stream. #({True} \<ominus> ora) = \<infinity> \<and> shd ora}) (Discr{\<C> ''ds''}) 
  (Discr{\<C> ''dr''})"
  using medsps_uspecwell
  proof -
    have "{MedSPF ora |ora::bool stream. #({True} \<ominus> ora) = \<infinity> \<and> shd ora} 
      = {(MedSPF ora) | ora. (#({True} \<ominus> ora) = \<infinity> \<and> snth 0 ora \<and> (\<forall>k<0. \<not>snth k ora))}"
    by simp
    then show ?thesis
    using medsps_uspecwell by presburger
  qed

(* If a "null" comes in, send it out and stay in the same state. *)
lemma "spsConcIn (tsynbNull(\<C> ''ds'')) (MedSPS n) = spsConcOut (tsynbNull (\<C> ''dr''))\<cdot>(MedSPS n)"
  apply (subst spsconcin_insert)
  apply (case_tac "c=(\<C> ''dr'')", simp_all)
  apply (subst spsconcout_insert, simp)
  apply (simp add: spfConcIn_def spfConcOut_def)
  apply (simp add: uspecImage_def medsps_uspecran medsps_uspecdom ufclDom_ufun_def ufclRan_ufun_def)
sorry

lemma "spsConcIn (createBundle (Msg m) (\<C> ''ds'')) (MedSPS (Suc n))
  = spsConcOut (tsynbNull(\<C> ''dr''))\<cdot>(MedSPS n)"
  apply (subst spsconcin_insert)
  apply (case_tac "c=(\<C> ''dr'')", simp_all)
  apply (simp add: slen_createbundle_getch)
  apply (subst spsconcout_insert, simp)
  apply (simp add: uspecImage_def medsps_uspecdom medsps_uspecran ufclDom_ufun_def ufclRan_ufun_def)
  apply (simp add: spfConcIn_def spfConcOut_def)
  apply (simp add: uspecrevset_insert MedSPS_def)
  using medsps_uspecwell
  apply (simp add: setrevImage_def inv_rev_rev)
  apply (simp add: MedSPF_def)
sorry

lemma "\<And>x::(abpMessage tsyn stream\<^sup>\<Omega>) ufun.
       (x \<in> Rep_cfun (spfConcIn (createBundle (\<M> m) (\<C> ''ds''))) ` Rep_rev_uspec (MedSPS (0::nat))) =
       (x \<in> Rep_cfun (spfConcOut (createBundle (\<M> m) (\<C> ''dr''))) ` Rep_rev_uspec (MedSPS n))"
  apply (simp add: image_def spfConcIn_def spfConcOut_def)
  apply (simp add: MedSPS_def)
  apply (subst rep_abs_rev_simp)
  apply (smt CollectD medspf_ufdom medspf_ufran ufclDom_ufun_def ufclRan_ufun_def uspec_wellI)
  apply (subst rep_abs_rev_simp)
  apply (smt CollectD medspf_ufdom medspf_ufran ufclDom_ufun_def ufclRan_ufun_def uspec_wellI)
  proof -
    obtain xa where "xa \<in> {MedSPF ora |ora. #({True} \<ominus> ora) = \<infinity> \<and> shd ora}"    
  oops

lemma "spsConcIn (createBundle (Msg m) (\<C> ''ds'')) (MedSPS 0) 
  = spsConcOut (createBundle (Msg m) (\<C> ''dr''))\<cdot>(MedSPS n)"
  apply (subst spsconcin_insert)
  apply (simp add: slen_createbundle_getch)
  apply (subst spsconcout_insert)
  apply (simp add: slen_createbundle_getch)
  apply (simp add: uspecImage_def medsps_uspecdom medsps_uspecran ufclDom_ufun_def ufclRan_ufun_def)
  apply (rule uspec_eqI)
  defer
  apply (smt medsps_uspecdom medsps_uspecran spfConcIn_dom spfConcIn_ran spfConcOut_dom 
    spfConcOut_ran ufclDom_ufun_def ufclRan_ufun_def uspecImage_def uspecimage_useful_dom)
  apply (smt medsps_uspecdom medsps_uspecran spfConcIn_dom spfConcIn_ran spfConcOut_dom 
    spfConcOut_ran ufclDom_ufun_def ufclRan_ufun_def uspecImage_def uspecimage_useful_ran)
  apply (simp add: uspecrevset_insert)
  apply (rule setrev_eqI)
  apply (simp add: setrevImage_def inv_rev_rev)
  apply (subst rep_abs_rev_simp)
  defer
  apply (subst rep_abs_rev_simp)
  defer
  apply (simp add: set_eq_iff)
sorry

(*
apply (rule set_eq_iff)

(* If a "null" comes in send it out and stay in the same state *) 
lemma "spsConcIn (makeNull (\<C> ''ds'')) (h_MED state) = spsConcOut (makeNull (\<C> ''dr''))\<cdot>(h_MED state)"
  oops

(* counter not null, drop every message and count one down *)
lemma "spsConcIn (makeInput m) (h_MED (State TheOne (Suc n))) = spsConcOut (makeNull (\<C> ''dr''))\<cdot>(h_MED (State TheOne n))"
  oops

(* Counter hit zero, so pass the message and reset the countdown to a random value *)
lemma "spsConcIn (makeInput m) (h_MED (State TheOne 0)) = spsConcOut (makeOutput m)\<cdot>(spsFlatten {h_MED (State TheOne n) |  n. True})"
  oops
*)
end