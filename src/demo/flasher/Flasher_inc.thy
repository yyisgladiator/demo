theory Flasher_inc

imports inFlashData outFlashData bundle.SB_fin
begin

interpretation flashInSBE: sbeGen "buildFlashinSBE"
  apply(unfold_locales)
  apply(simp add: buildflashin_ctype)
  apply (simp add: buildflashin_inj)
  apply (simp add: buildflashin_surj)
  by simp

interpretation flashInSB: sbGen "buildFlashinSB"
  apply(unfold_locales)
  using buildflashoutsb_ctype sValues_def apply auto[1]
  apply (simp add: buildflashoutsb_inj)
  by (simp add: buildflashoutsb_surj)

interpretation flashOutSBE: sbeGen "buildFlashoutSBE"
  apply(unfold_locales)
  apply(simp add: buildflashout_ctype)
  apply (simp add: buildflashout_inj)
  apply (simp add: buildflashout_surj)
  by simp

interpretation flashOutSB: sbGen "buildFlashoutSB"
  apply(unfold_locales)
  apply (simp add: buildflashinsb_ctype)
  apply (simp add: buildflashinsb_inj)
  by (simp add: buildflashinsb_surj)

end