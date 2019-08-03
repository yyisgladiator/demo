theory emptychanData

imports bundle.Channel
  begin

typedef emptychan="{c3}"
  by simp

instantiation emptychan::"{finite,emptychan}"
begin
definition "Rep = Rep_emptychan"
instance
  apply(intro_classes)
  apply simp
  using Rep_emptychan_def type_definition.Rep_range type_definition_emptychan
  using Rep_emptychan apply auto[1]
  apply (simp add: Rep_emptychan_def Rep_emptychan_inject inj_on_def)
  sorry
end

end