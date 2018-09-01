(* Dummy for KnasterTarski proof over cpo/pcpo *)

theory KnasterTarski

imports HOLCF

begin

(* This is going to be problematic, we cannot use pcpo (because uspec is no pcpo) *)
default_sort cpo

(* ToDo: add LEAST condition *)
definition lfp:: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
"lfp f = (SOME x. f x = x)"

lemma knaster_tarski: fixes f :: "'a \<Rightarrow>'a"
  assumes "monofun f"
  obtains x where "f x = x"
  sorry

lemma lfp_condition: assumes "monofun f"
  shows "f (lfp f) = lfp f"
  apply(simp add: lfp_def)
  by (meson assms knaster_tarski someI)

(* We are going to use this for refinement. Does not hold like this, the input might not be monofun *)
lemma lfp_monofun: "monofun lfp"
  oops

end