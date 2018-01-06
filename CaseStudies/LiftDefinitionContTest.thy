theory LiftDefinitionContTest
  imports StreamCase_Study
begin

setup_lifting type_definition_cfun    


lift_definition f1 :: "nat stream \<rightarrow> nat stream \<Rightarrow> nat stream" is "\<lambda> s1 s2. s2 \<bullet> \<up>1 \<bullet> s1"
  apply(simp add: cfun_def)
  done


lift_definition f2 :: "nat stream \<Rightarrow> nat stream \<rightarrow> nat stream" is "\<lambda> s1 s2. s1 \<bullet> \<up>1 \<bullet> s2"
  apply(simp add: cfun_def)
  done

    
lift_definition f3 :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" is "\<lambda> s1 s2. \<up>1" 
sorry


end
  