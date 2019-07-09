theory Flasher

imports AndAutomat NotAutomat
begin

(*Composition of And and Not SPFs*)

definition flasherComp::"((inAnd\<union>inNot) - (outAnd \<union> outNot))\<^sup>\<Omega> \<rightarrow>(outAnd \<union> outNot)\<^sup>\<Omega>"where
"flasherComp = andSpf \<otimes> notSpf"

lemma flasherinsb:"(andInSBE.setterSB\<cdot>(s1))\<uplus>\<^sub>\<star>(notInSBE.setterSB\<cdot>(s2)) = 
                   (sbConvert::inAnd\<^sup>\<Omega> \<rightarrow> ((inAnd\<union>inNot) - (outAnd \<union> outNot))\<^sup>\<Omega>)\<cdot>(andInSBE.setterSB\<cdot>(s1))"
  apply(induction s1 rule: ind,auto)
  apply(simp add: sbunion_insert)
  apply(rule sb_eqI)
  apply(subgoal_tac "Rep c \<in> range (Rep::inAnd \<Rightarrow> channel)")
  defer
  sorry
  
lemma flasherhd:"andOutSBE.getterSB\<cdot>((flasherComp\<cdot>((andInSBE.setterSB\<cdot>(\<up>a\<bullet>s1))\<uplus>\<^sub>\<star>(notInSBE.setterSB\<cdot>(\<up>b\<bullet> s2))))\<star>)
                 = \<up>True \<bullet> andOutSBE.getterSB\<cdot>((flasherComp\<cdot>((andInSBE.setterSB\<cdot>(s1))\<uplus>\<^sub>\<star> (notInSBE.setterSB\<cdot>(s2))))\<star>)"
  apply(subst flasherinsb)+
  apply(simp add: flasherComp_def)
  apply(subst andInSBE.settersb_unfold)
  apply(simp add: andSpf_def notSpf_def)
  oops

end