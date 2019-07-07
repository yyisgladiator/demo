theory inAndData

imports inc.Channel
begin

typedef inAnd="{cin1,cin2}"
  by auto

instantiation inAnd::"{somechan,finite}"
begin
definition "Rep = Rep_inAnd"
instance
  apply(standard)
  apply(auto simp add: Rep_inAnd_def cEmpty_def)
  using ctype.elims
  apply (metis Rep_inAnd ctype.simps(4) ctype.simps(5) ctype.simps(6) ex_in_conv insertE insert_iff insert_not_empty sup_eq_bot_iff)
  apply (meson Rep_inAnd_inject injI)
  sorry
end

definition "Andin1 \<equiv> Abs_inAnd cin1"
definition "Andin2 \<equiv> Abs_inAnd cin2"

free_constructors inAnd for "Andin1"  | "Andin2"
   apply auto
  unfolding Andin1_def Andin2_def
  apply (metis Rep_inAnd Rep_inAnd_inverse empty_iff insert_iff)
  by (simp add: Abs_inAnd_inject)

fun inAndChan::"('nat::type \<Rightarrow> 'a::type) \<Rightarrow> ('bool::type \<Rightarrow> 'a) \<Rightarrow>('nat\<times>'bool) \<Rightarrow> inAnd \<Rightarrow> 'a" where
"inAndChan Cc1 Cc2 (port_c1, port_c2) Andin1 = Cc1 port_c1" |
"inAndChan Cc1 Cc2 (port_c1, port_c2) Andin2 = Cc2 port_c2"

abbreviation "buildAndinSBE \<equiv> inAndChan \<B> \<B>" 

end