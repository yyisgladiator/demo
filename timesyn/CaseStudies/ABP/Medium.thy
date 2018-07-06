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

lemma tsynfilter_tsynabs_slen: "#(tsynAbs\<cdot>(tsynFilter A\<cdot>s)) \<le> #(tsynAbs\<cdot>s)"
  sorry

lemma tsynzip_tsynabs_slen: "#xs = \<infinity> \<Longrightarrow> #(tsynAbs\<cdot>(tsynZip\<cdot>s\<cdot>xs)) = #(tsynAbs\<cdot>s)"
  sorry

text {* Not every message will be transmitted forcibly. *}    
lemma tsynmed_tsynabs_slen: 
  assumes "#ora=\<infinity>" 
  shows " #(tsynAbs\<cdot>(tsynMed\<cdot>msg\<cdot>ora)) \<le> #(tsynAbs\<cdot>msg)"
  using assms
  proof-
    assume ora_inf: "#ora = \<infinity>" 
    hence "#(tsynAbs\<cdot>(tsynFilter (Collect snd)\<cdot>(tsynZip\<cdot>msg\<cdot>ora))) \<le> #(tsynAbs\<cdot>msg)"
      by (metis tsynfilter_tsynabs_slen tsynzip_tsynabs_slen)
    have "#(tsynAbs\<cdot>(tsynFilter (Collect snd)\<cdot>(tsynZip\<cdot>msg\<cdot>ora))) = #(tsynAbs\<cdot>(tsynProjFst\<cdot>(tsynFilter (Collect snd)\<cdot>(tsynZip\<cdot>msg\<cdot>ora))))"
      sorry
    have "tsynFilter (Collect snd)\<cdot>(tsynZip\<cdot>msg\<cdot>ora) = tsynProjFst\<cdot>(tsynFilter {x::'a \<times> bool. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora))"
      sorry
    thus ?thesis
      apply (simp add: tsynmed_insert)
      sorry

    have tsynmed_tsynfilter_slen: "#(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora)) = #(tsynZip\<cdot>msg\<cdot>ora)"
      by (simp add: tsynfilter_slen)
    have tsynmed_slen: "#(tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora))) = #(tsynZip\<cdot>msg\<cdot>ora)"
      by (simp add: tsynmed_tsynfilter_slen tsynprojfst_slen)
    have tsynabs: "#(tsynAbs\<cdot>(tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora)))) = #(tsynAbs\<cdot>(tsynZip\<cdot>msg\<cdot>ora))" 
      sorry
    have tsynabs_tsynzip: "#(tsynAbs\<cdot>(tsynZip\<cdot>msg\<cdot>ora)) \<le> #(tsynAbs\<cdot>msg)"
      by (simp add: ora_inf tsynzip_tsynabs_slen)
    have "#(tsynAbs\<cdot>(tsynProjFst\<cdot>(tsynFilter {x. snd x}\<cdot>(tsynZip\<cdot>msg\<cdot>ora)))) \<le> #(tsynAbs\<cdot>msg)"
      sorry
    show ?thesis
      sorry
  qed

end