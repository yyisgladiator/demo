theory Flasher

imports AndAutomat NotAutomat Flasher_inc
begin                             


(* Es fehlen noch die Wrapper um die sub-componenten. Aber erstmal das so fertig haben *)


(*Composition of And and Not SPFs*)
definition flasherComp::"((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega> \<rightarrow> (outAnd \<union> outNot)\<^sup>\<Omega>"where
"flasherComp = (andSpf \<otimes> notSpf)"

definition convflasherComp::"(inFlash)\<^sup>\<Omega> \<rightarrow>(outFlash)\<^sup>\<Omega>"where
"convflasherComp = spfConvert\<cdot>flasherComp"

(* TODO: verwende "chDom" *)
lemma rangeinunion:"range(Rep::(inAnd \<union> inNot) \<Rightarrow> channel) = {cin1,cin2,cout}"
  sorry

(* TODO: verwende "chDom" *)
lemma rangeoutunion:"range(Rep::outAnd \<union> outNot \<Rightarrow> channel) = {cout,cin2}"
  sorry

(* TODO: verwende "chDom" *)
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

(* TODO: verwende "chDom" *)
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
assumes "f\<cdot>(sb \<uplus>\<^sub>\<star> out) = (out\<star>)"
    and "g\<cdot>(sb \<uplus>\<^sub>\<star> out) = (out\<star>)"
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

lemma chtype_empty: "ctype ch = {} \<Longrightarrow> ch = c3"
  by(cases ch; simp add: ctype_empty_iff)

(* Das soll weiter nach vorne. geht nicht in "Datatypes", da dort "cEmpty" nich existiert...
    Vllt eine art "prelude" vor den generierten sachen? *)
lemma chEmpty[simp]:"cEmpty = {c3}"
  by(auto simp add: cEmpty_def chtype_empty ctype_empty_iff)


lemma inand_dom[simp]: "chDom TYPE(inAnd) = {cin1,cin2}"
  unfolding chDom_def Rep_inAnd_def
  by (metis Diff_triv Rep_inAnd_def chan_notempty type_definition.Rep_range type_definition_inAnd)

lemma [simp]:"chDom TYPE(outAnd) = {cout}"
  apply(simp add: chDom_def Rep_outAnd_def)
  using type_definition.Rep_range type_definition_outAnd by fastforce

lemma [simp]:"chDom TYPE(inNot) = {cout}"
  apply(simp add: chDom_def Rep_inNot_def)
  using type_definition.Rep_range type_definition_inNot by fastforce

lemma [simp]:"chDom TYPE(outNot) = {cin2}"
  apply(simp add: chDom_def Rep_outNot_def)
  using type_definition.Rep_range type_definition_outNot by fastforce


(* SWS: Gilt das? ich glaube "port_intern" wird versteck, also ist nach "sbConvert" nichtmehr da *)
lemma flash2andin[simp]:"(((sbConvert::inFlash\<^sup>\<Omega> \<rightarrow> ((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>)\<cdot>(flashInSB.setter port_i)) 
                         \<uplus>\<^sub>\<star> ((sbConvert::outFlash\<^sup>\<Omega> \<rightarrow> (outAnd \<union> outNot)\<^sup>\<Omega>)\<cdot>(flashOutSB.setter (port_o, port_intern)))) 
                          = (andInSB.setter (port_i, port_intern))"
  apply(simp add: sbconvert_insert)
  apply(rule sb_eqI,auto)  
  sorry

lemma flash2andout[simp]:"flashOutSB.setter (port_o, port_intern)\<star>\<star>\<^sub>1 = andOutSB.setter port_o"
  oops (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

lemma flash2notin[simp]:"flashInSB.setter port_i\<star> \<uplus>\<^sub>\<star> (flashOutSB.setter (port_o, port_intern)\<star>) = notInSB.setter(port_o)"
  oops (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

lemma flash2notout[simp]:"flashOutSB.setter (port_o, port_intern)\<star>\<star>\<^sub>2 = notOutSB.setter port_intern "
  oops (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

lemma flash2andinnotout[simp]:"flashInSB.setter port_i\<star> \<uplus>\<^sub>\<star> (z::(outAnd \<union> outNot)\<^sup>\<Omega>) = andInSB.setter (port_i,notOutSB.getter(z\<star>))"
  oops (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

lemma flash2notinandout[simp]:"flashInSB.setter port_i\<star> \<uplus>\<^sub>\<star> (z::(outAnd \<union> outNot)\<^sup>\<Omega>) = notInSB.setter (andOutSB.getter(z\<star>))"
  oops (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

(* DEUTLICH WICHTIGER! *)
lemma assumes "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
    and "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "(flasherComp\<cdot>(flashInSB.setter (port_i)\<star>)) = (flashOutSB.setter (port_o,port_intern)\<star>)"
  apply(simp add: flasherComp_def convflasherComp_def spfConvert_def)
  apply(rule spfcomp_eq,simp)
    apply (simp add: assms)
  oops
  

 (*nicht anwendbar wenn kanäle versteckt werden*)
(* Ignore the following stuff
datatype S = State S_and S_not bool

instance S::countable
  by(countable_datatype)

fun flashertransition::"S \<Rightarrow> bool option \<Rightarrow> S \<times> bool option"where
"flashertransition (State sand snot inputcin1) inputcin2 = 
  (let (nextand,andout) = dAand_transition sand (inputcin1, inputcin2);
                                             (nextnot, notout) = dAnot_transition snot andout in
                                                   ((State nextand nextnot notout), andout))"

lemma "flashertransition (State sand snot inputcin1) inputcin2 = (State sand snot (inputcin1 \<longrightarrow> \<not> inputcin2), inputcin1 \<and> inputcin2)"
  by(simp)

definition flashersscanl::"bool stream \<rightarrow> bool stream"where
"flashersscanl = sscanlAsnd flashertransition (State S_and.Single S_not.Single True)"

lemma flasherstep[simp]:"sscanlAsnd flashertransition (State S_and.Single S_not.Single bool)\<cdot>(\<up>a \<bullet> s) =
                   \<up>(bool \<and> a) \<bullet> sscanlAsnd flashertransition (State S_and.Single S_not.Single (\<not>(bool \<and> a)))\<cdot>s"
  by simp 

lemma flasherout:assumes"Fin (Suc n) < #input" shows"snth (Suc n) (flashersscanl\<cdot>input) = snth (Suc n) input \<and> \<not> snth n input"
  apply(simp add: flashersscanl_def)
  apply(rule scases[of input],simp)
  using assms apply auto[1]
  apply simp
  sorry

lemma flasherfinal:assumes"Fin (Suc n) < #input" 
  shows"snth (Suc n) (flashersscanl\<cdot>input) \<Longrightarrow> snth (Suc n) input \<or> snth n input"
  by(simp add: assms flasherout)
*)

end