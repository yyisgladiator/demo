theory Flasher

imports AndAutomat NotAutomat
begin

(*Composition of And and Not SPFs*)

definition flasherComp::"((inAnd\<union>inNot) - (outAnd \<union> outNot))\<^sup>\<Omega> \<rightarrow>(outAnd \<union> outNot)\<^sup>\<Omega>"where
"flasherComp = andSpf \<otimes> notSpf"

lemma flasherhd:"\<exists>rest. flasherComp\<cdot>(sbe \<bullet>\<^sup>\<surd> sb) = sbeConvert(sbeGen.setter buildAndoutSBE (True \<and> sbeGen.getter buildNotinSBE (sbeConvert sbe)))\<bullet>\<^sup>\<surd> rest"

  sorry


end