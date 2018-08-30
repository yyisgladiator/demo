theory issue241

imports tsynStream

begin

(*tsynDom*)

lemma tsynabs_sdom: "sdom\<cdot>(tsynAbs\<cdot>s) = tsynDom\<cdot>s"
  apply (induction rule: tsyn_ind, simp_all)
  apply (simp add: tsyndom_strict)
  apply (simp add: tsynabs_sconc_msg tsyndom_sconc_msg)
  by (simp add: tsynabs_sconc_null tsyndom_sconc_null)

lemma tsynmap_sdom: "sdom\<cdot>(tsynMap f\<cdot>s) = (tsynApplyElem f) ` (sdom\<cdot>s)"
  apply (induction s arbitrary: f rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sdom tsynmap_insert)+

lemma tsynProjFst_sdom: "sdom\<cdot>(tsynProjFst\<cdot>s) = tsynFst ` (sdom\<cdot>s)"
  apply (induction rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sdom tsynprojfst_insert)+

lemma tsynProjSnd_sdom: "sdom\<cdot>(tsynProjSnd\<cdot>s) = tsynSnd ` (sdom\<cdot>s)"
  apply (induction rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sdom tsynprojsnd_insert)+

lemma tsynremdups_h_sdom: "sdom\<cdot>((sscanlA tsynRemDups_h state)\<cdot>s) = sdom\<cdot>s"
  apply (induction s arbitrary: state rule: tsyn_ind)
  sorry

lemma tsynremdups_sdom: "sdom\<cdot>(tsynRemDups\<cdot>s) = sdom\<cdot>s"
  by (simp add: tsynremdups_insert tsynremdups_h_sdom)

(*lemma tsynFilter_sdom: "sdom\<cdot>((tsynFilter A)\<cdot>s) \<subseteq> sdom\<cdot>s"
  proof (induction s rule: tsyn_ind)
    case adm
    then show ?case 
      by simp
  next
    case bot
    then show ?case 
      by simp
  next
    case (msg m s)
    have h2: "m \<notin> A \<Longrightarrow> sdom\<cdot>(A \<ominus>\<^sub>- \<up>(\<M> m) \<bullet> s) = sdom\<cdot>(\<up>null \<bullet> s)"
      sledgehammer
      by tsynfilter_sconc_msg_nin
      sorry
    then show ?case
      by (metis (no_types, lifting) insert_mono msg.IH srcdups_dom srcdups_dom_h tsynfilter_sconc_msg_in)
      using h1 by blast
  next
    case (null s)
    then show ?case
      by (metis (no_types, hide_lams) insert_mono srcdups_dom srcdups_dom_h tsynfilter_sconc_null)
  qed
  *)

(*lemma tsynScanlExt_sdom: "sdom\<cdot>(tsynScanlExt f i\<cdot>s) = (sscanlA (tsynScalExt_h f) i)\<cdot>(sdom\<cdot>s)"
  apply (induction s arbitrary: f i rule: tsyn_ind, simp_all)
    apply (rule admI)
*)


(*tsynScanl*)

(*tsynDropWhile*)

(*lemma tsynZip_sdom: "sdom\<cdot>(tsynZip\<cdot>as\<cdot>bs) = sdom\<cdot>(szip\<cdot>(tsynAbs\<cdot>as)\<cdot>(tsynAbs\<cdot>bs))"*)

end

