theory notAutomat_inc

imports inNotData outNotData bundle.SB_fin
begin

(*State datatype*)
datatype S_not = Single

instance S_not::countable
  by(countable_datatype)
(*interpretations And*)

interpretation notInSBE: sbeGen "buildNotinSBE"
  apply(unfold_locales)
  apply(simp add: buildnotin_ctype)
  apply (simp add: buildnotin_inj)
  apply (simp add: buildnotin_surj)
  by simp

interpretation notInSB: sbGen "buildNotinSB"
  apply(unfold_locales)
  using buildnotoutsb_ctype sValues_def apply auto[1]
  apply (simp add: buildnotoutsb_inj)
  by (simp add: buildnotoutsb_surj)

interpretation notOutSBE: sbeGen "buildNotoutSBE"
  apply(unfold_locales)
  apply(simp add: buildnotout_ctype)
  apply (simp add: buildnotout_inj)
  apply (simp add: buildnotout_surj)
  by simp


interpretation notOutSB: sbGen "buildNotoutSB"
  apply(unfold_locales)
  apply (simp add: buildnotinsb_ctype sValues_def)
  apply (simp add: buildnotinsb_inj)
  by (simp add: buildnotinsb_surj)

end