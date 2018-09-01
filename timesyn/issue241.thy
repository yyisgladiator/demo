theory issue241

imports tsynStream

begin

(* Try to use set equality after using tsyndom and image definition. *)
lemma tsyndom_sdom: "tsynDom\<cdot>s = inverseMsg ` (sdom\<cdot>s)"
  oops

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
lemma tsynremdups_sdom: "sdom\<cdot>(tsynRemDups\<cdot>s) = sdom\<cdot>s"
  oops

(* What happens if all elements are not in the set and no null is contained in the stream? *)
lemma tsynfilter_sdom: "sdom\<cdot>(tsynFilter A\<cdot>s) \<subseteq> sdom\<cdot>s"
  oops

(* Try to prove something like that. *)
lemma tsyndropwhile_sdom: "sdom\<cdot>(tsynDropWhile f\<cdot>s) \<subseteq> sdom\<cdot>s"
  oops

(* Try to prove something like that. *)
lemma tsynzip_sdom: "sdom\<cdot>(tsynZip\<cdot>as\<cdot>bs) = Msg ` (tsynDom\<cdot>as \<times> sdom\<cdot>bs)"
  oops

(* Skip tsynScanl, tsynScanlExt for now. *)

end

