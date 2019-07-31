theory fmAutomat_inc

imports inFM outFM bundle.SB_fin
begin

(*State datatype*)
datatype S_fm = S bool nat "nat list"  "nat list"

instance S_fm::countable
  by(countable_datatype)
(*interpretations FM*)

interpretation fmInSBE: sbeGen "buildFMinSBE"
  apply(unfold_locales)
  apply(simp add: buildfmin_ctype)
  apply (simp add: buildfmin_inj)
  apply (simp add: buildfmin_surj)
  by simp

interpretation fmInSB: sbGen "buildFMinSB"
  apply(unfold_locales)
  sorry

interpretation fmOutSBE: sbeGen "buildFMoutSBE"
  apply(unfold_locales)
  apply(simp add: buildfmout_ctype)
  apply (simp add: buildfmout_inj)
  apply (simp add: buildfmout_surj)
  by simp

interpretation fmOutSB: sbGen "buildFMoutSB"
  apply(unfold_locales)
  sorry


end