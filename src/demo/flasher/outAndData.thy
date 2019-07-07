theory outAndData

imports inc.Channel
  begin

typedef outAnd = "{cout}"
  by auto

definition "Andout \<equiv> Abs_outAnd cout"


instantiation outAnd::"{somechan,finite}"
begin
definition "Rep = Rep_outAnd"
instance
  apply(standard)
  apply(auto simp add: Rep_outAnd_def)
  apply (metis Rep_outAnd singletonD)
   apply (meson Rep_outAnd_inject injI)
  sorry
end

free_constructors outAnd for "Andout"
  unfolding Andout_def
  using Abs_outAnd_cases by auto

fun outAndChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outAnd \<Rightarrow> 'a" where
"outAndChan Cc1 bool Andout = Cc1 bool"

abbreviation "buildAndoutSBE \<equiv> outAndChan \<B>" 


end