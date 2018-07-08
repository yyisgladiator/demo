(*  Title:        Medium.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for Medium Lemmata.
*)

chapter {* Theory for Medium Lemmata *}

theory Medium
imports "../../tsynStream" 

begin

(* ----------------------------------------------------------------------- *)
  section {* Medium SPF Definition for Verification *}
(* ----------------------------------------------------------------------- *)

text{* Time synchronous medium, that loses messages. *}
definition tsynMed :: "'a tsyn stream \<rightarrow> bool stream \<rightarrow> 'a tsyn stream" where
  "tsynMed \<equiv> \<Lambda> msg ora. tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora))"

(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

text {* Induction rule for infinite time-synchronous streams and admissable predicates. *}
lemma ora_ind [case_names adm bot msg_t msg_f]:
  assumes adm: "adm P"
    and bot: "P \<epsilon>"
    and msg_t: "\<And>s. P s \<Longrightarrow> P (\<up>True \<bullet> s)"
    and msg_f: "\<And>s. P s \<Longrightarrow> P (\<up>False \<bullet> s)"
  shows "P (x:: bool stream)"
  apply (induction x rule: ind)
  apply (simp add: adm)
  apply (simp add: bot)
  apply (case_tac a)
  apply (simp add: msg_t)
  by (simp add: msg_f)

lemma oracases [case_names bot true false]:
  assumes bot: "s=\<epsilon> \<Longrightarrow> P s"
    and true: "\<And>as. s= (\<up>True \<bullet> as) \<Longrightarrow> P s"
    and false: "\<And>as. s=(\<up>False \<bullet> as) \<Longrightarrow> P s"
  shows "P s"
  by (metis (full_types) bot false scases true)

(* ----------------------------------------------------------------------- *)
subsection {* basic properties of tsMed *}
(* ----------------------------------------------------------------------- *)

text{* "Lossy" medium that gets messages and an oracle and will transmit the k-th message if
       the k-th element in the oracle is True, otherwise the message will be discarded. *}
lemma tsynmed_insert: "tsynMed\<cdot>msg\<cdot>ora = tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora))"
  by (simp add: tsynMed_def)

lemma tsynmed_strict [simp]: 
  "tsynMed\<cdot>\<epsilon>\<cdot>\<epsilon> = \<epsilon>"
  "tsynMed\<cdot>msg\<cdot>\<epsilon> = \<epsilon>"
  "tsynMed\<cdot>\<epsilon>\<cdot>ora = \<epsilon>"
  by (simp add: tsynMed_def)+

text{* If the first element in the oracle is True then the current message will be transmitted. *}
lemma tsynmed_sconc_msg_t:
  assumes "msg \<noteq> \<epsilon>"
  shows "tsynMed\<cdot>(\<up>(Msg m) \<bullet> msg)\<cdot>(\<up>True \<bullet> ora) = \<up>(Msg m) \<bullet> (tsynMed\<cdot>msg\<cdot>ora)"
  proof -
    have thesis_simple:
      "tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>(\<up>(Msg m) \<bullet> msg)\<cdot>(\<up>True \<bullet> ora)))
        = \<up>(Msg m) \<bullet> tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora))"
        by (simp add: tsynzip_sconc_msg tsynfilter_sconc_msg_in tsynfilter_sconc_null 
          tsynprojfst_sconc_null tsynprojfst_sconc_msg)
    then show ?thesis
      by (simp add: tsynmed_insert)
  qed

text{* If the first element in the oracle is False then the current message will not be transmitted. *}
lemma tsynmed_sconc_msg_f:
  assumes "msg \<noteq> \<epsilon>" 
  shows "tsynMed\<cdot>(\<up>(Msg m) \<bullet> msg)\<cdot>(\<up>False \<bullet> ora) = \<up>- \<bullet> tsynMed\<cdot>msg\<cdot>ora"
  sorry

text{* If the first element in the stream is null the oracle will not change. *}
lemma tsynmed_sconc_null:
  assumes "msg \<noteq> \<epsilon>" 
  shows "tsynMed\<cdot>(\<up>- \<bullet> msg)\<cdot>ora = \<up>- \<bullet> tsynMed\<cdot>msg\<cdot>ora"
  sorry

(* ToDo: general sconc lemma possible? *)

(* ToDo: singleton lemma *)

lemma tsynmed_slen: assumes "#ora=\<infinity>" shows "#(tsynMed\<cdot>msg\<cdot>ora) = #msg"
  by (simp add: assms tsynfilter_slen tsynmed_insert tsynprojfst_slen tsynzip_slen)

text {* Not every message will be transmitted forcibly. *}    
lemma tsynmed_tsynlen: 
  assumes "#ora=\<infinity>" 
  shows "tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>ora) \<le> tsynLen\<cdot>msg"
  using assms
  proof-
    assume ora_inf: "#ora = \<infinity>" 
    hence modified_lemma: "#(tsynAbs\<cdot>(tsynFilter (Collect snd)\<cdot>(tsynZip\<cdot>msg\<cdot>ora))) \<le> #(tsynAbs\<cdot>msg)"
      by (metis tsynfilter_tsynlen tsynlen_insert tsynzip_tsynlen)
    thus ?thesis
      by (metis tsynlen_insert tsynmed_insert tsynprojfst_tsynlen)
  qed

text{* The transmitted messages are a subset of the messages that are meant to be transmitted. *}
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
          by (metis (mono_tags, hide_lams) inject_scons msg.IH sconc_fst_empty sconc_snd_empty 
              tsynmed_sconc_null tsynmed_strict(2))
      next
        case (true as)
        then show ?thesis 
          proof (cases rule: scases [of s])
            case bottom
            have tsynfilter_simp: "tsynFilter {x::'a \<times> bool. snd x}\<cdot>(\<up>(Msg (m, True))) = (\<up>(Msg (m, True)))"
              by (metis mem_Collect_eq sconc_snd_empty snd_conv tsynfilter_sconc_msg_in tsynfilter_strict)
            then show ?thesis 
              by (metis bottom order_refl true tsynfilter_sconc tsynmed_insert tsynmed_strict(3) 
                  tsynprojfst_sconc_msg tsynzip_sconc_msg)
          next
            case (scons a t)
            then show ?thesis 
              by (metis (mono_tags, hide_lams) inject_scons msg.IH sconc_fst_empty sconc_snd_empty 
                  tsynmed_sconc_null tsynmed_strict(2))
          qed
      next
        case (false as)
        then show ?thesis
          proof (cases rule: scases [of s])
            case bottom
            have tsynfilter_simp: "tsynFilter {x::'a \<times> bool. snd x}\<cdot>(\<up>(Msg (m, False))) = \<up>null"
              by (metis (full_types) mem_Collect_eq sconc_snd_empty snd_conv 
                  tsynfilter_sconc_msg_nin tsynfilter_strict)
            then show ?thesis 
              by (metis (no_types, hide_lams) bottom false order_refl sconc_snd_empty 
                  tsynZip.simps(1) tsyndom_sconc_msg_sub tsyndom_sconc_null tsynfilter_strict 
                  tsynmed_insert tsynmed_strict(3) tsynprojfst_sconc_null tsynzip_sconc_msg)
          next
            case (scons a t)
            then show ?thesis
              by (metis (mono_tags, hide_lams) inject_scons msg.IH sconc_fst_empty sconc_snd_empty 
                  tsynmed_sconc_null tsynmed_strict(2))
          qed
      qed
  next
    case (null s)
    have tsynmed_null: "tsynMed\<cdot>(\<up>- \<bullet> s)\<cdot>ora = \<up>- \<bullet> tsynMed\<cdot>s\<cdot>ora"
      proof (cases rule: scases [of s])
        case bottom
        then show ?thesis 
          by (metis tsynmed_sconc_null tsynmed_strict(2) tsynmed_strict(3))
      next
        case (scons a s)
        then show ?thesis 
        by (simp add: null.prems tsynmed_sconc_null)
      qed
    then show ?case
      by (simp add: null.IH null.prems tsyndom_sconc_null)
  qed

lemma tsynmed_tsynlen_inf: 
  assumes msg_inf: "tsynLen\<cdot>msg = \<infinity>"
  shows "tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>ora) = #({True} \<ominus> ora)"
  using assms
  proof (induction ora arbitrary: msg rule: ora_ind)
        case adm
        then show ?case 
          by (simp add: adm_def contlub_cfun_arg contlub_cfun_fun)
      next
        case bot
        then show ?case 
          by simp
      next
        case (msg_t s)
        then show ?case 
          proof (cases rule: tsyn_cases_inf [of msg])
            case inf
            then show ?case
              by (simp add: msg_t.prems)
          next
            case (msg a as)
            have as_inf: "msg = \<up>(Msg a) \<bullet> as \<Longrightarrow> tsynLen\<cdot>as = \<infinity>"
              by (metis fold_inf lnat.sel_rews(2) msg msg_t.prems tsynlen_sconc_msg)
            have as_nbot: "msg = \<up>(Msg a) \<bullet> as \<Longrightarrow> as \<noteq> \<epsilon>"
              by (simp add: as_inf tsynlen_inf_nbot)
            have tsynmed_lnsuc: "as \<noteq> \<epsilon> \<Longrightarrow> tsynLen\<cdot>(tsynMed\<cdot>(\<up>(Msg a) \<bullet> as)\<cdot>(\<up>True \<bullet> s)) = lnsuc\<cdot>(tsynLen\<cdot>(tsynMed\<cdot>as\<cdot>s))"
              by (simp add: tsynmed_sconc_msg_t tsynlen_sconc_msg)
            then show ?thesis 
              by (simp add: as_inf as_nbot msg msg_t.IH tsynmed_lnsuc)
          next
            case (null as)
            then show ?thesis 
              by (metis (no_types, lifting) assoc_sconc inject_scons sconc_snd_empty srcdupsimposs 
                  tsynmed_sconc_null tsynmed_strict(2))
          qed
      next
        case (msg_f s)
        then show ?case
          by (metis bot_is_0 lnat.con_rews slen_scons strict_slen tsynmed_sconc_null tsynmed_strict(2))
      oops

text{* If infinitely many messages are sent, infinitely many messages will be transmitted. *}
lemma tsynmed_tsynlen_inf:
  assumes "#({True} \<ominus> ora) = \<infinity>" 
    and "tsynLen\<cdot>msg = \<infinity>"
  shows "tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>ora) = \<infinity>"
  using assms
  proof (induction msg arbitrary: ora rule: tsyn_ind)
    case adm
    then show ?case 
      apply (rule adm_all)+
      apply (rule admI)
      apply (rule)+
      apply (simp add: contlub_cfun_fun contlub_cfun_arg)
sorry
  next
    case bot
    then show ?case sorry
  next
    case (msg m s)
    then show ?case sorry
  next
    case (null s)
    then show ?case sorry
  qed

(* ToDo: Tests *)

end