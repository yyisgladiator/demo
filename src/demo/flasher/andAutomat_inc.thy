theory andAutomat_inc

imports inAndData outAndData bundle.SB_fin emptychanData
begin

(*State datatype*)
datatype S_and = Single

instance S_and::countable
  by(countable_datatype)
(*interpretations And*)

interpretation andInSBE: sbeGen "buildAndinSBE"
  apply(unfold_locales)
  apply(simp add: buildandin_ctype)
  apply (simp add: buildandin_inj)
  apply (simp add: buildandin_surj)
  by simp

interpretation andInSB: sbGen "buildAndinSB"
  apply(unfold_locales)
  sorry

interpretation andOutSBE: sbeGen "buildAndoutSBE"
  apply(unfold_locales)
  apply(simp add: buildandout_ctype)
  apply (simp add: buildandout_inj)
  apply (simp add: buildandout_surj)
  by simp

interpretation andOutSB: sbGen "buildAndoutSB"
  apply(unfold_locales)
  sorry


end