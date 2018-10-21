(*  Title:        Medium.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for Medium Definitions and Lemmata.
*)

chapter {* Theory for Medium Definitions and Lemmata *}

theory Medium

imports stream.tsynStream

begin

default_sort countable

(* ----------------------------------------------------------------------- *)
  section {* Medium Definition for Verification *}
(* ----------------------------------------------------------------------- *)

text{* @{term tsynMed}: Lossy medium on time-synchronous streams that gets messages and an oracle
       and will transmit the k-th message if the k-th element in the oracle is True, otherwise the 
       message will be discarded. *}
definition tsynMed :: "'a tsyn stream \<rightarrow> bool stream \<rightarrow> 'a tsyn stream" where
  "tsynMed \<equiv> \<Lambda> msg ora. tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora))"

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
            by simp
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
      by (metis (full_types) scases sdropwhile_resup shd1 tsyn.exhaust)
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
  assumes "#({True} \<ominus> ora) = \<infinity>" and "tsynLen\<cdot>msg = \<infinity>"
  shows "tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>ora) = \<infinity>"
  using assms by (simp add: tsynmed_tsynlen_ora)

text {* @{term tsynMed} test on finite stream with ticks. *}
lemma tsynmed_test_finstream_null: (* SWS: use mediumIn_list_ar *)
  "tsynMed\<cdot>(<[null, null, Msg (2,False), Msg (1, True), Msg (3, True)]>)\<cdot>(<[True, False, True]>) 
    = <[null, null, Msg (2,False), null, Msg (3, True)]>"
  oops

text {* @{term tsynMed} test on infinite stream. *}
lemma tsynmed_test_infstream: (* SWS: use mediumIn_list_ar *)
  "tsynMed\<cdot>((<[Msg(3, False), null, Msg(2, True),Msg(1, False)]>)\<infinity>)\<cdot>((<[True, False, True]>)\<infinity>)
    =(<[Msg(3, False), null, null, Msg(1, False)]>)\<infinity>"
  oops

end