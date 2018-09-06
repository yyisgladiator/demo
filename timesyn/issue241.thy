theory issue241

imports tsynStream

begin

lemma tsyndom_sdom: "tsynDom\<cdot>s = inverseMsg ` (sdom\<cdot>s - {null})"
  apply (simp add: tsyndom_insert image_def set_eq_iff)
  by (metis DiffE DiffI empty_iff insert_iff inverseMsg.simps(2) tsyn.exhaust tsyn.simps(3))

lemma tsynabs_sdom: "sdom\<cdot>(tsynAbs\<cdot>s) = tsynDom\<cdot>s"
  apply (induction rule: tsyn_ind, simp_all)
  apply (simp add: tsyndom_strict)
  apply (simp add: tsynabs_sconc_msg tsyndom_sconc_msg)
  by (simp add: tsynabs_sconc_null tsyndom_sconc_null)

lemma tsynmap_sdom: "sdom\<cdot>(tsynMap f\<cdot>s) = tsynApplyElem f ` sdom\<cdot>s"
  apply (induction s arbitrary: f rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sdom tsynmap_insert)+

lemma tsynprojfst_sdom: "sdom\<cdot>(tsynProjFst\<cdot>s) = tsynFst ` sdom\<cdot>s"
  apply (induction rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sdom tsynprojfst_insert)+

lemma tsynprojsnd_sdom: "sdom\<cdot>(tsynProjSnd\<cdot>s) = tsynSnd ` sdom\<cdot>s"
  apply (induction rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sdom tsynprojsnd_insert)+

lemma tsynremdups_sdom_h: "sdom\<cdot>(sscanlA tsynRemDups_h (\<M> m)\<cdot>s) \<subseteq> sdom\<cdot>s \<union> {null}"
  apply (induction s arbitrary: m rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_eq_Union)
  by blast+

lemma tsynremdups_sdom: "sdom\<cdot>(tsynRemDups\<cdot>s) \<subseteq> sdom\<cdot>s \<union> {null}"
  apply (induction rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_eq_Union, blast)
  apply (metis (no_types, hide_lams) Un_commute Un_insert_left insert_mono sdom2un 
         sup_bot.left_neutral tsynremdups_sconc_msg tsynremdups_sdom_h)
  by (simp add: tsynremdups_sconc_null)

lemma tsynfilter_sdom: "sdom\<cdot>(tsynFilter A\<cdot>s) = tsynFilterElem A ` sdom\<cdot>s"
  apply (induction s arbitrary: A rule: tsyn_ind, simp_all)
  apply (rule admI)
  by (simp add: smap_sdom tsynfilter_insert)+

lemma tsyndropwhile_sdom: "sdom\<cdot>(tsynDropWhile f\<cdot>s) \<subseteq> sdom\<cdot>s \<union> {null}"
  apply (induction s arbitrary: f rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_eq_Union, blast)
  apply (metis (no_types, hide_lams) insert_commute insert_is_Un insert_subset sdom2un 
         subset_insertI2 subset_refl tsyndropwhile_sconc_msg_f tsyndropwhile_sconc_msg_t)
  by (simp add: tsyndropwhile_sconc_null)

(* I think with null it should work. *)
lemma tsynzip_sdom: "sdom\<cdot>(tsynZip\<cdot>as\<cdot>bs) \<subseteq> Msg ` (tsynDom\<cdot>as \<times> sdom\<cdot>bs) \<union> {null}"
  apply (induction as arbitrary: bs rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: contlub_cfun_arg contlub_cfun_fun lub_eq_Union, blast)
  oops

(* Skip tsynScanl, tsynScanlExt for now. *)

end

