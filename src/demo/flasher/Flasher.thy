theory Flasher

imports AndAutomat NotAutomat Flasher_inc
begin                             

(*Composition of And and Not SPFs*)

definition flasherComp::"((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega> \<rightarrow> (outAnd \<union> outNot)\<^sup>\<Omega>"where
"flasherComp = (andSpf \<otimes> notSpf)"

definition convflasherComp::"(inFlash)\<^sup>\<Omega> \<rightarrow>(outFlash)\<^sup>\<Omega>"where
"convflasherComp = spfConvert\<cdot>flasherComp"

lemma rangeinunion:"range(Rep::(inAnd \<union> inNot) \<Rightarrow> channel) = {cin1,cin2,cout}"
  sorry

lemma rangeoutunion:"range(Rep::outAnd \<union> outNot \<Rightarrow> channel) = {cout,cin2}"
  sorry

lemma rangecompin:"range(Rep::(inAnd \<union> inNot) - outAnd \<union> outNot \<Rightarrow> channel) = {cin1}"
  sorry

lemma compin2flashin:"range(Rep::(inAnd \<union> inNot) - outAnd \<union> outNot \<Rightarrow> channel) = range(Rep::inFlash\<Rightarrow> channel)"
  apply(simp add: rangecompin)
  apply(simp add: Rep_inFlash_def)
  using type_definition.Rep_range type_definition_inFlash by blast

lemma compout2flashout:"range(Rep::outAnd \<union> outNot \<Rightarrow> channel) = range(Rep::outFlash\<Rightarrow> channel)"
  apply(simp add: rangeoutunion)
  apply(simp add: Rep_outFlash_def)
  using type_definition.Rep_range type_definition_outFlash oops

lemma sbconvert_sbeq:assumes"range (Rep::'a::chan\<Rightarrow>channel) = range(Rep::'b::chan\<Rightarrow>channel)"
      and "\<And>c d. Rep c = Rep d \<Longrightarrow> (Rep_sb sb1) c = (Rep_sb sb2) d"
    shows"sbConvert\<cdot>(sb2::'b\<^sup>\<Omega>) = (sb1::'a\<^sup>\<Omega>) "
  sorry


lemma assumes "\<And>c. input1 \<^enum>\<^sub>\<star> c = input2 \<^enum>\<^sub>\<star> c" 
  shows"\<And>c. flasherComp\<cdot>input1 \<^enum>\<^sub>\<star> c= convflasherComp\<cdot>input2 \<^enum>\<^sub>\<star> c"
  oops(*
  apply(simp add: sbgetch_insert convflasherComp_def spfConvert_def,auto)
  apply(subst sbconvert_sbeq,simp_all)
  apply (metis (mono_tags, hide_lams) Abs_inFlash_cases Flashin1_rep Rep_inFlash_def UNIV_eq_I image_insert image_is_empty insertI1 rangecompin singletonD)
  apply(insert assms)
  apply(simp add:  sbgetch_insert)
  apply(subgoal_tac "\<And>c::inFlash. Rep c \<in> range (Rep::(inAnd \<union> inNot) - outAnd \<union> outNot \<Rightarrow> channel)",simp_all)
  apply (metis chan_inj inv_f_f)
  by (simp add: compin2flashin)
*)

(* use SB-setter! not sbeGen *)
lemma assumes "convflasherComp\<cdot>(flashInSB.setter (port_i)) = flasherSetterout (port_i, port_intern, port_o)"
  shows "andSpf\<cdot>(andSetterin (port_i, port_intern)) = andSetterout port_o"
    and "notSpf\<cdot>(notSetterin(port_intern)) = notSetterout port_i"
  oops

lemma  spfcomp_eq:fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
        and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
      assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('gOut)) = {}"
fixes out::"('fOut \<union> 'gOut)\<^sup>\<Omega>"
assumes "f\<cdot>(sb \<uplus>\<^sub>\<star> out) = out\<star>"
    and "g\<cdot>(sb \<uplus>\<^sub>\<star> out) = out\<star>"
    and "\<And>z::('fOut \<union> 'gOut)\<^sup>\<Omega>. f\<cdot>(sb \<uplus>\<^sub>\<star> z) \<uplus> g\<cdot>(sb \<uplus>\<^sub>\<star> z) = z \<Longrightarrow> out \<sqsubseteq> z"
      shows "((f\<otimes>g)\<cdot>sb) = out"
  apply(subst genComp_def)
  apply(simp add: spfConvert_def)
  apply(rule fix_eqI)
  by (simp_all add: assms)
(* ? ? ?
lemma  spfcomp_magiceq:fixes f::"'fIn\<^sup>\<Omega> \<rightarrow> 'fOut\<^sup>\<Omega>"
        and g::"'gIn\<^sup>\<Omega> \<rightarrow> 'gOut\<^sup>\<Omega>"
      assumes "chDom (TYPE ('fOut)) \<inter> chDom (TYPE ('gOut)) = {}"
      fixes out::"('fOut)\<^sup>\<Omega>"
assumes "f\<cdot>(sb \<uplus>\<^sub>\<star> out) = out\<star>"
    and "g\<cdot>(sb \<uplus>\<^sub>\<star> out) = out\<star>"
      shows "((f\<otimes>g)\<cdot>sb)\<star> = out"
  apply(subst genComp_def)
  apply(simp add: spfConvert_def sbConvert_def)
  apply(rule fix_eqI)
  by (simp_all add: assms)
*)
lemma [simp]:"chDom TYPE(outAnd) = {cout}"
  sorry
lemma [simp]:"chDom TYPE(outNot) = {cin1}"  
  sorry

lemma flash2andin[simp]:"(flashInSB.setter port_i\<star> \<uplus>\<^sub>\<star> (flashOutSB.setter (port_o, port_intern)\<star>)) = (andInSB.setter (port_i, port_intern))"
  sorry

lemma flash2andout[simp]:"flashOutSB.setter (port_o, port_intern)\<star>\<star> = andOutSB.setter port_o"
  sorry

lemma flash2notin[simp]:"flashInSB.setter port_i\<star> \<uplus>\<^sub>\<star> (flashOutSB.setter (port_o, port_intern)\<star>) = notInSB.setter(port_o)"
  sorry

lemma flash2notout[simp]:"flashOutSB.setter (port_o, port_intern)\<star>\<star> = notOutSB.setter port_intern "
  sorry

(* DEUTLICH WICHTIGER! *)
lemma assumes "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
    and "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "(flasherComp\<cdot>(flashInSB.setter (port_i)\<star>)) = flashOutSB.setter (port_o,port_intern)\<star>"
  apply(simp add: flasherComp_def convflasherComp_def spfConvert_def)
  apply(rule spfcomp_eq,simp)
    apply (simp add: assms)
   apply(simp add: assms)
  oops
  

 (*nicht anwendbar wenn kanäle versteckt werden*)

datatype S = State S_and S_not bool

instance S::countable
  by(countable_datatype)

fun flashertransition::"S \<Rightarrow> bool \<Rightarrow> S \<times> bool"where
"flashertransition (State sand snot inputcin1) inputcin2 = 
  (let (nextand,andout) = dAand_transition sand (inputcin1, inputcin2);
                                             (nextnot, notout) = dAnot_transition snot andout in
                                                   ((State nextand nextnot notout), andout))"

lemma "flashertransition (State sand snot inputcin1) inputcin2 = (State sand snot (inputcin1 \<longrightarrow> \<not> inputcin2), inputcin1 \<and> inputcin2)"
  by(simp)

definition flashersscanl::"bool stream \<rightarrow> bool stream"where
"flashersscanl = sscanlAsnd flashertransition (State S_and.Single S_not.Single True)"

end