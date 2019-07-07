theory outNotData

imports inc.Channel
  begin

typedef outNot = "{cin2}"
  by auto

instantiation outNot::"{somechan,finite}"
begin
definition "Rep = Rep_outNot"
instance
  apply(standard)
  apply(auto simp add: Rep_outNot_def)
  apply (metis Rep_outNot singletonD)
  apply (meson Rep_outNot_inject injI)
  sorry
end

definition "Notout \<equiv> Abs_outNot cin2"

free_constructors outNot for "Notout"
  by (metis(full_types) Abs_outNot_cases singletonD)

fun outNotChan::"('bool::type \<Rightarrow> 'a::type) \<Rightarrow> 'bool \<Rightarrow> outNot \<Rightarrow> 'a" where
"outNotChan Cc1 bool Notout = Cc1 bool"

abbreviation "buildNotoutSBE \<equiv> outNotChan \<B>" 

end