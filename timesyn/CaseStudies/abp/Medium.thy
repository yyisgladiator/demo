(*  Title:        Medium.thy
    Author:       Annika Savelsberg
    E-Mail:       annika.savelsberg@rwth-aachen.de

    Description:  Theory for Medium Lemmata.
*)

chapter {* Theory for Medium Lemmata *}

theory Medium
imports Components

begin

(* ----------------------------------------------------------------------- *)
  section {* Medium SPF Definition for Verification *}
(* ----------------------------------------------------------------------- *)

text{* Time synchronous medium, that loses messages. *}
definition tsynMed :: "(nat \<times> bool) tsyn stream \<rightarrow> bool stream \<rightarrow> (nat \<times> bool) tsyn stream" where
  "tsynMed \<equiv> \<Lambda> msg ora. tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora))"

text {* @{term tsynbMed}: Medium function for Alternating Bit Protocol on stream bundles. *}
definition tsynbMed :: "bool stream \<Rightarrow> 
  abpMessage tsyn stream ubundle \<rightarrow> abpMessage tsyn stream ubundle option" where
  "tsynbMed ora \<equiv> \<Lambda> sb. (ubclDom\<cdot>sb = {\<C> ''ds''}) \<leadsto> Abs_ubundle [
                      \<C> ''dr'' \<mapsto> natbool2abp\<cdot>(tsynMed\<cdot>(abp2natbool\<cdot>(sb  .  \<C> ''ds''))\<cdot>ora)]"

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
lemma tsynmed_sconc_msg_t: "tsynMed\<cdot>(\<up>(Msg m) \<bullet> msg)\<cdot>(\<up>True \<bullet> ora) = \<up>(Msg m) \<bullet> (tsynMed\<cdot>msg\<cdot>ora)"
  by (simp add: tsynmed_insert tsynzip_sconc_msg tsynfilter_sconc_msg_in tsynfilter_sconc_null 
                tsynprojfst_sconc_null tsynprojfst_sconc_msg)

text{* If the first element in the oracle is False then the current message will not be transmitted. *}
lemma tsynmed_sconc_msg_f: "tsynMed\<cdot>(\<up>(Msg m) \<bullet> msg)\<cdot>(\<up>False \<bullet> ora) = \<up>- \<bullet> tsynMed\<cdot>msg\<cdot>ora"
  sorry

text{* If the first element in the stream is null the oracle will not change. *}
lemma tsynmed_sconc_null:
  assumes "ora \<noteq> \<epsilon>"
  shows "tsynMed\<cdot>(\<up>- \<bullet> msg)\<cdot>ora = \<up>- \<bullet> tsynMed\<cdot>msg\<cdot>ora"
  sorry

(* singleton lemmata *)
lemma tsynmed_sconc_singleton_msg_t: "tsynMed\<cdot>(\<up>(\<M> m))\<cdot>(\<up>True \<bullet> ora) = \<up>(\<M> m)"
  sorry

lemma tsynmed_sconc_singleton_msg_f: "tsynMed\<cdot>(\<up>(\<M> m))\<cdot>(\<up>False \<bullet> ora) = \<up>-"
  sorry

lemma tsynmed_sconc_singleton_msg_null: assumes "ora \<noteq> \<epsilon>" shows "tsynMed\<cdot>(\<up>-)\<cdot>ora = \<up>-"
  sorry

(* ToDo: general sconc lemma possible? *)

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
            by (simp add: tsyndom_strict)
      next
        case (true as)
        then show ?thesis
          by (simp add: true tsynmed_sconc_msg_t tsyndom_sconc le_supI2 msg.IH)
      next 
        case (false as)
        then show ?thesis
          apply (simp add: false tsynmed_sconc_msg_f tsyndom_sconc)
          by (metis lscons_conv msg.IH sup'_def sup.coboundedI2 tsyndom_sconc_null tsynmed_strict(2))
       qed
  next
    case (null s)
    then show ?case
      by (metis tsyndom_sconc_null tsynmed_sconc_null tsynmed_strict(2))
  qed

lemma tsynmed_tsynlen_ora_t:
  assumes msg_inf: "tsynLen\<cdot>msg = \<infinity>"
  shows "tsynLen\<cdot>(tsynMed\<cdot>(\<up>null \<bullet> msg)\<cdot>(\<up>True \<bullet> ora)) = #({True} \<ominus> (\<up>True \<bullet> ora))"
  using assms
  proof (induction msg arbitrary: ora rule: tsyn_ind)
    case adm
    then show ?case 
      apply (rule admI)
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

lemma tsynmed_tsynlen_ora_f: 
  assumes msg_inf: "tsynLen\<cdot>msg = \<infinity>"
  shows "tsynLen\<cdot>(tsynMed\<cdot>(\<up>null \<bullet> msg)\<cdot>(\<up>False \<bullet> ora)) = #({True} \<ominus> (\<up>False \<bullet> ora))"
  sorry

lemma tsynmed_tsynlen_ora: 
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
        then show ?thesis
          by (metis msg_t.prems tsynlen_sconc_null tsynmed_sconc_null tsynmed_strict(2) tsynmed_tsynlen_ora_t)
      next
        case (null as)
        then show ?thesis 
          by (metis msg_t.prems tsynlen_sconc_null tsynmed_tsynlen_ora_t)
      qed
  next
    case (msg_f s)
    then show ?case
      proof (cases rule: tsyn_cases_inf [of msg])
        case inf
        then show ?case
          by (simp add: msg_f.prems)
      next
        case (msg a as)
        then show ?thesis
          by (metis msg_f.prems tsynlen_sconc_null tsynmed_sconc_null tsynmed_strict(2) tsynmed_tsynlen_ora_f)
      next
        case (null as)
        then show ?thesis 
          by (metis msg_f.prems tsynlen_sconc_null tsynmed_tsynlen_ora_f)
      qed
  oops

text{* If infinitely many messages are sent, infinitely many messages will be transmitted. *}
lemma tsynmed_tsynlen_inf:
  assumes "#({True} \<ominus> ora) = \<infinity>" 
    and "tsynLen\<cdot>msg = \<infinity>"
  shows "tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>ora) = \<infinity>"
  using assms
  (*by (simp add: tsynmed_tsynlen_ora)*)
  sorry

(* ToDo: Tests *)

end