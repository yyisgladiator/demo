theory SB
  imports "../UBundle" Streams
begin

type_synonym 'm SB = "'m stream ubundle"

instance stream :: (countable) uscl
  sorry

instance stream :: (countable) uscl_pcpo
  sorry

default_sort message

definition sbRt :: "'m SB \<rightarrow> 'm SB" where
"sbRt \<equiv> \<Lambda> sb. ubMapStream (Rep_cfun srt) sb"

section \<open>Lemma\<close>

subsection \<open>sbRt\<close>
(* Does not work now, because the instantiation of stream is only a sorry *)
lemma sbrt_okay: "usOkay c s \<Longrightarrow> usOkay c (srt\<cdot>s)"
  sorry

lemma sbrt_cont [simp]: "cont (ubMapStream (Rep_cfun srt))"
  by (simp add: sbrt_okay ubMapStream_contI2)



end