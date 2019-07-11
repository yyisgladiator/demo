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
  using type_definition.Rep_range type_definition_outFlash by blast

lemma sbconvert_sbeq:assumes"range (Rep::'a::chan\<Rightarrow>channel) = range(Rep::'b::chan\<Rightarrow>channel)"
      and "\<And>c d. Rep c = Rep d \<Longrightarrow> (Rep_sb sb1) c = (Rep_sb sb2) d"
    shows"sbConvert\<cdot>(sb2::'b\<^sup>\<Omega>) = (sb1::'a\<^sup>\<Omega>) "
  sorry


lemma assumes "\<And>c::inFlash. input1 \<^enum>\<^sub>\<star> c = input2 \<^enum>\<^sub>\<star> c" 
  shows"\<And>c. flasherComp\<cdot>input1 \<^enum>\<^sub>\<star> c= convflasherComp\<cdot>input2 \<^enum> c"
  oops
  apply(simp add: sbgetch_insert convflasherComp_def spfConvert_def,auto)
  apply(subst sbconvert_sbeq,simp_all)
  apply (metis (mono_tags, hide_lams) Abs_inFlash_cases Flashin1_rep Rep_inFlash_def UNIV_eq_I image_insert image_is_empty insertI1 rangecompin singletonD)
  apply(insert assms)
  apply(simp add:  sbgetch_insert)
  apply(subgoal_tac "\<And>c::inFlash. Rep c \<in> range (Rep::(inAnd \<union> inNot) - outAnd \<union> outNot \<Rightarrow> channel)",simp_all)
  apply (metis chan_inj inv_f_f)
  apply (simp add: compin2flashin)
  using compout2flashout
  by blast

(* use SB-setter! not sbeGen *)
lemma assumes "flasherComp\<cdot>(flasherSetterin (port_i)) = flasherSetterout (port_i, port_intern, port_o)"
  shows "andSpf\<cdot>(andSetterin (port_i, port_intern)) = andSetterout port_o"
    and "notSpf\<cdot>(notSetterin(port_intern)) = notSetterout port_i"
  oops

(* DEUTLICH WICHTIGER! *)
lemma assumes "andSpf\<cdot>(andSetterin (port_i, port_intern)) = andSetterout port_o"
    and "notSpf\<cdot>(notSetterin(port_intern)) = notSetterout port_i"
  shows "flasherComp\<cdot>(flasherSetterin (port_i)) = flasherSetterout (port_o)"
  oops

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