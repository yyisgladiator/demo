theory issue241

imports tsynStream

begin

(* Try to use set equality after using tsyndom and image definition. *)
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

(* What happens if no null is contained in the stream? *)
lemma tsynremdups_sdom: "sdom\<cdot>(tsynRemDups\<cdot>s) \<subseteq> sdom\<cdot>s \<union> {null}"
  apply (induction rule: tsyn_ind, simp_all)
    apply (rule admI)
    apply (smt ch2ch_Rep_cfunR contlub_cfun_arg insert_mono l44 order_subst1 sdom_chain2lub)
  
  oops

(* What happens if all elements are not in the set and no null is contained in the stream? *)
lemma tsynfilter_sdom: "sdom\<cdot>(tsynFilter A\<cdot>s) \<subseteq> sdom\<cdot>s \<union> {null}"
  apply (induction s arbitrary: A rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (smt ch2ch_Rep_cfunR contlub_cfun_arg insert_mono l44 order_subst1 sdom_chain2lub)
  using tsynfilter_sconc_msg_in tsynfilter_sconc_msg_nin
  apply (smt insertI1 insert_commute insert_mono order_subst1 sfilterEq2sdom_h sfilter_in sfilter_sdoml3 subset_insertI)
  by (simp add: tsynfilter_sconc_null)

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
  oops

(* Skip tsynScanl, tsynScanlExt for now. *)

end

