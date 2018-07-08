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
  assumes bot: "ts=\<epsilon> \<Longrightarrow> P ts"
    and true: "\<And>as. ts= (\<up>True \<bullet> as) \<Longrightarrow> P ts"
    and false: "\<And>as. ts=(\<up>False \<bullet> as) \<Longrightarrow> P ts"
  shows "P ts"
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
    and " #ora = \<infinity>"
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
    and " #ora = \<infinity>" 
  shows "tsynMed\<cdot>(\<up>(Msg m) \<bullet> msg)\<cdot>(\<up>False \<bullet> ora) = \<up>- \<bullet> tsynMed\<cdot>msg\<cdot>ora"
sorry

text{* If the first element in the stream is null the oracle will not change. *}
lemma tsynmed_sconc_null:
  assumes "msg \<noteq> \<epsilon>" 
    and " #ora = \<infinity>" 
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
lemma tsynmed_tsyndom: assumes ora_inf:"#ora=\<infinity>" shows "tsynDom\<cdot>(tsynMed\<cdot>msg\<cdot>ora) \<subseteq> tsynDom\<cdot>msg"
  using assms
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
          using msg.prems by simp
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
            have s_not_empty: "s \<noteq> \<epsilon>"
              by (simp add: scons)
            have as_inf: "#as = \<infinity>"
              using msg.prems true by simp
            then show ?thesis 
              by (simp add: s_not_empty true as_inf tsynmed_sconc_msg_t tsyndom_sconc_msg msg.IH 
                  subset_insertI2)
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
            have s_not_empty: "s \<noteq> \<epsilon>"
              by (simp add: scons)
            have as_inf: "#as = \<infinity>"
              using msg.prems false by simp
            then show ?thesis
              by (metis (no_types, lifting) dual_order.trans false msg.IH s_not_empty set_eq_subset 
                  tsyndom_sconc_msg_sub tsyndom_sconc_null tsynmed_sconc_msg_f)
          qed
      qed
  next
    case (null s)
    have tsynmed_null: "tsynMed\<cdot>(\<up>- \<bullet> s)\<cdot>ora = \<up>- \<bullet> tsynMed\<cdot>s\<cdot>ora"
      proof (cases rule: scases [of s])
        case bottom
        then show ?thesis 
          by (metis (no_types, hide_lams) Inf'_neq_0 null.prems sconc_snd_empty strict_slen 
              tsynZip.simps(1) tsynfilter_sconc_null tsynmed_insert tsynprojfst_sconc_null 
              tsynzip_sconc_null)
      next
        case (scons a s)
        then show ?thesis 
        by (simp add: null.prems tsynmed_sconc_null)
      qed
    then show ?case
      by (simp add: null.IH null.prems tsyndom_sconc_null)
  qed

lemma smed_slen_inf [simp]: 
  assumes msg_inf: "tsynLen\<cdot>msg = \<infinity>"
  shows "tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>ora) = #({True} \<ominus> ora)"
  using assms
  sorry
(*  proof (induction ora arbitrary: msg rule: ora_ind)
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
          proof (cases rule: tsyn_cases [of _ msg])
              case bot
              have msg_nbot: "msg \<noteq> \<epsilon>"
                using msg_t.prems by auto
              then show "(\<And>msg::'a tsyn stream. tsynLen\<cdot>msg = \<infinity> \<Longrightarrow> tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>s) = #({True} \<ominus> s)) \<Longrightarrow>
    tsynLen\<cdot>msg = \<infinity> \<Longrightarrow> tsynLen\<cdot>(tsynMed\<cdot>\<epsilon>\<cdot>(\<up>True \<bullet> s)) = #({True} \<ominus> \<up>True \<bullet> s)"  sorry
            next
              case (msg m s)
              then show ?thesis sorry
            next
              case (null s)
              then show ?thesis sorry
            qed
sorry
      next
        case (msg_f s)
        then show ?case sorry
      qed*)

(*proof (induction ora arbitrary: msg rule: ind)
      case 1
      then show ?case 
        by (simp add: adm_def contlub_cfun_arg contlub_cfun_fun)
    next
      case 2
      then show ?case 
        by (simp add: tsynmed_strict(2))
    next
      case (3 a s)
      then show ?case 
        proof (cases "a=True")
          assume msg_inf: "tsynLen\<cdot>msg = \<infinity>"
          case True
          then show ?thesis
            proof (cases rule: tsyn_cases [of _ msg])                
                case 1                                
                have msg_nbot: "msg \<noteq> \<epsilon>"
                  using msg_inf by auto
                have case_simp: "msg = \<epsilon> \<Longrightarrow> tsynLen\<cdot>(tsynMed\<cdot>msg\<cdot>(\<up>a \<bullet> s)) = #({True} \<ominus> \<up>a \<bullet> s)"
                  by (simp add: msg_nbot)
                show "tsynLen\<cdot>(tsynMed\<cdot>\<epsilon>\<cdot>(\<up>a \<bullet> s)) = #({True} \<ominus> \<up>a \<bullet> s)"
                  
 sorry
              next
                case (msg m s)
                then show ?thesis sorry
              next
                case (null s)
                then show ?thesis sorry
              qed

            
sorry
next
  case False
  then show ?thesis sorry
qed
sorry
    qed*)

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