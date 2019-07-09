theory Flasher_inc

imports inFlashData outFlashData bundle.SB_fin
begin

interpretation flashInSBE: sbeGen "buildFlashinSBE"
  apply(unfold_locales)
  apply(simp add: buildflashin_ctype)
  apply (simp add: buildflashin_inj)
  apply (simp add: buildflashin_surj)
  by simp

interpretation flashOutSBE: sbeGen "buildFlashoutSBE"
  apply(unfold_locales)
  apply(simp add: buildflashout_ctype)
  apply (simp add: buildflashout_inj)
  apply (simp add: buildflashout_surj)
  by simp

end