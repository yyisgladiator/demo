theory issue241

imports tsynStream

begin

lemma tsyndom_sdom: "tsynDom\<cdot>s = inverseMsg ` ((sdom\<cdot>s) - {null})"
  apply (simp add: tsyndom_insert)
  apply (simp add: image_def)
  apply (simp add: set_eq_iff)
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

lemma tsynremdups_sdom2: "sdom\<cdot>(sscanlA tsynRemDups_h (\<M> m)\<cdot>s) \<subseteq> sdom\<cdot>s \<union> {null}"
  apply (induction s arbitrary: m rule: tsyn_ind, simp_all)
   apply (rule admI)
  using dual_order.trans insert_mono l44 sdom_chain2lub contlub_cfun_arg
  sorry


(* What happens if no null is contained in the stream? *)
lemma tsynremdups_sdom: "sdom\<cdot>(tsynRemDups\<cdot>s) \<subseteq> sdom\<cdot>s \<union> {null}"
  apply (induction rule: tsyn_ind, simp_all)
    apply (rule admI)

    apply (smt ch2ch_Rep_cfunR contlub_cfun_arg insert_mono l44 order_subst1 sdom_chain2lub)
   defer
   apply (simp add: tsynremdups_sconc_null)
  
  oops

lemma tsynfilter_sdom: "sdom\<cdot>(tsynFilter A\<cdot>s) \<subseteq> tsynFilterElem A ` sdom\<cdot>s"
  apply (simp add: tsynfilter_insert)
  apply (induction s arbitrary: A rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (simp add: smap_sdom)
  apply (simp add: smap_sdom subset_insertI)
  by (simp add: subset_insertI2)

(* Try to prove something like that. *)
lemma tsyndropwhile_sdom: "sdom\<cdot>(tsynDropWhile f\<cdot>s) \<subseteq> sdom\<cdot>s \<union> {null}"
  apply (induction s arbitrary: f rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (smt ch2ch_Rep_cfunR contlub_cfun_arg insert_mono l44 order_subst1 sdom_chain2lub)
  using tsyndropwhile_sconc_msg_f tsyndropwhile_sconc_msg_t
  apply (metis (no_types, lifting) insert_absorb2 insert_commute insert_is_Un insert_mono sdom2un set_eq_subset subset_insertI2)
  by (simp add: tsyndropwhile_sconc_null)

(* Try to prove something like that. *)
lemma tsynzip_sdom: "sdom\<cdot>(tsynZip\<cdot>as\<cdot>bs) = Msg ` (tsynDom\<cdot>as \<times> sdom\<cdot>bs)"
  apply (induction as arbitrary: bs rule: tsyn_ind, simp_all)
     apply (rule admI)
  oops
(* Skip tsynScanl, tsynScanlExt for now. *)

end

