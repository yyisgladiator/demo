theory IntroCaseStudy_SB_MW
imports  "../SB"  "../TSB"  "../SPF" StreamCase_Study  "../SPF"
begin

datatype M = Nat nat ("\<N> _" )

instance M :: countable
by countable_datatype

instantiation M::message
begin
  fun ctype_M :: "channel \<Rightarrow> M set" where 
  "ctype_M c1 = range Nat" |
  "ctype_M c2 = range Nat"

  instance
  by(intro_classes)
end

instantiation nat :: message
begin
  definition ctype_nat :: "channel \<Rightarrow> nat set" where "ctype_nat c = range nat"
 
  instance ..
end
setup_lifting datatype_definition_M
(* SB *)
lift_definition SB1 :: "M SB" is "([c1\<mapsto><[\<N> 1,\<N> 3,\<N> 5,\<N> 7,\<N> 9]>, c2\<mapsto><[\<N> 0,\<N> 2,\<N> 4,\<N> 6,\<N> 8]>])"
by(simp add: sb_well_def)

(* TSB *)
lift_definition TSB1 :: "nat TSB" is "([c1\<mapsto>tsInfTick])"
by(simp add: tsb_well_def)

end