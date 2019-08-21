theory Flasher

imports AndAutomat NotAutomat Flasher_inc spf.SPFcomp
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


lemma andOutSB_port_o: assumes " Rep c = cout" shows " andOutSB.setter port_o  \<^enum>  c = (smap (Tsyn o (map_option) \<B>)\<cdot>port_o)"
  by (metis andOutSB.setter.rep_eq outAnd.exhaust outAndChan.simps sbgetch_insert2)

lemma notOutSB_port_o: assumes " Rep c = cin2" shows " notOutSB.setter port_intern  \<^enum>  c = (smap (Tsyn o (map_option) \<B>)\<cdot>port_intern)"
  by (metis notOutSB.setter.rep_eq outNot.exhaust outNotChan.simps sbgetch_insert2)

lemma flashOutSB_port_o: assumes " Rep (c::outAnd) = cout" shows "(flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>)  \<^enum>\<^sub>\<star> c = (smap (Tsyn o (map_option) \<B>)\<cdot>port_o)"
  apply(simp add: sbgetch_insert assms rangeoutunion)
  oops


lemma flash2andout[simp]:"(flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>)\<star>\<^sub>1 = andOutSB.setter port_o"
  sorry (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

lemma flash2notin[simp]:"(flashInSB.setter port_i\<star> :: ((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>) \<uplus>\<^sub>\<star> (flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>) = notInSB.setter(port_o)"
  sorry (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

lemma flash2notout[simp]:"flashOutSB.setter (port_o, port_intern)\<star>\<star>\<^sub>2 = notOutSB.setter port_intern "
  sorry (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

lemma flash2andinnotout[simp]:"flashInSB.setter port_i\<star> \<uplus>\<^sub>\<star> (z::(outAnd \<union> outNot)\<^sup>\<Omega>) = andInSB.setter (port_i,notOutSB.getter(z\<star>))"
  oops (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

lemma flash2notinandout[simp]:"flashInSB.setter port_i\<star> \<uplus>\<^sub>\<star> (z::(outAnd \<union> outNot)\<^sup>\<Omega>) = notInSB.setter (andOutSB.getter(z\<star>))"
  oops (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)


lemma flash_setter_eq: "((flashInSB.setter port_i) \<uplus>\<^sub>\<star> (flashOutSB.setter (port_o, port_intern)\<star>::(outAnd \<union> outNot)\<^sup>\<Omega>)) = notInSB.setter(port_o)"
  (* setter eq *)
  sorry

lemma flash_setter_eq2: "((flashInSB.setter port_i) \<uplus>\<^sub>\<star> (flashOutSB.setter (port_o, port_intern)\<star>::(outAnd \<union> outNot)\<^sup>\<Omega>)) = andInSB.setter(port_i, port_intern)"
  (* setter eq *)
  sorry

(*
lemma flash_fix_old: 
  assumes "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
    and "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "(\<Lambda> (sbOut::(outAnd \<union> outNot)\<^sup>\<Omega>). andSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut) \<uplus> notSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut))\<cdot>
           (flashOutSB.setter (port_o, port_intern)\<star>) = (flashOutSB.setter (port_o, port_intern)\<star>::(outAnd \<union> outNot)\<^sup>\<Omega>)"
  apply(simp add: assms flash_setter_eq flash_setter_eq2)
  by (simp add: sbunion_eqI)

lemma flash_below_old: 
  assumes "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
    and "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "(\<mu> sbOut::(outAnd \<union> outNot)\<^sup>\<Omega>. andSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut) \<uplus> notSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut)) \<sqsubseteq>
         (flashOutSB.setter (port_o, port_intern)\<star>::(outAnd \<union> outNot)\<^sup>\<Omega>)"
  apply(rule fix_least)
  using assms flash_fix_old by blast

lemma flash_ChLen_old: assumes "Rep c\<in>chDom TYPE(outAnd \<union> outNot)" 
  and "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
  and "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "#((\<mu> sbOut::(outAnd \<union> outNot)\<^sup>\<Omega>. andSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut) \<uplus> notSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut)) \<^enum> c) =
         #((flashOutSB.setter (port_o, port_intern)\<star>::(outAnd \<union> outNot)\<^sup>\<Omega>) \<^enum> c)"  
proof - 
  have len_cout: "#((\<mu> sbOut::(outAnd \<union> outNot)\<^sup>\<Omega>. andSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut) \<uplus> notSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut)) \<^enum> (Abs cout)) = #port_i"  
    sorry
  have len_cin2: "#((\<mu> sbOut::(outAnd \<union> outNot)\<^sup>\<Omega>. andSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut) \<uplus> notSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut)) \<^enum> (Abs cin2)) = #port_i + 1"  
    sorry

  have "#port_intern = #port_i + 1"
  proof(rule ccontr)
    assume a0: "\<not> (#port_intern = #port_i +1)"
    have a1: "#port_o = lnmin\<cdot>(#port_i)\<cdot>(#port_intern)"
      using assms(2) (* with weak causal lemma *) sorry
    have a2: "#port_intern = #port_o + 1"
      using assms(3) (* with strong causal lemma *) sorry

    show False
    proof(cases "#port_intern  < #port_i + 1")
      case True
      then show ?thesis
        using a1 a2 by (metis dual_order.strict_implies_not_eq inf_ub ln_less lnat_plus_suc lnle2le lnmin_asso lnmin_eqasmthmin order.not_eq_order_implies_strict)
    next
      case False
      then have a3: "#port_intern > #port_i + 1"
        using a0 by auto
      then have a4: "#port_intern = #port_i + 1"
        by (metis a1 a2 dual_order.strict_implies_order linear lnat_plus_suc lnmin_asso lnmin_eqasmthmin lnsuc_lnle_emb)

      show ?thesis 
        using a3 a4
        by simp
    qed
  qed

  show ?thesis
    apply(simp add: fix_def)
    sorry
qed
*)

lemma flash_fix:
  assumes "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
    and "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "(\<Lambda> (x::(outAnd \<union> outNot)\<^sup>\<Omega>). andSpf\<cdot>((flashInSB.setter port_i\<star>::(((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>)) \<uplus>\<^sub>- x\<star>\<^sub>1) \<uplus> notSpf\<cdot>((flashInSB.setter port_i\<star>::(((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>)) \<uplus>\<^sub>- x\<star>\<^sub>2))\<cdot>
    (flashOutSB.setter (port_o, port_intern)\<star>) = flashOutSB.setter (port_o, port_intern)\<star>"
  apply(simp add: assms flash_setter_eq flash_setter_eq2)
  by (metis assms(1) assms(2) flash2andin flash2andout flash2notin flash2notout ubunion_id union_minus_nomagfst union_minus_nomagsnd)

lemma flash_below:
  assumes "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
    and "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "(\<mu> sbOut::(outAnd \<union> outNot)\<^sup>\<Omega>. andSpf\<cdot>(((flashInSB.setter port_i\<star>::(((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>)) \<uplus>\<^sub>- sbOut)\<star>\<^sub>1) \<uplus> notSpf\<cdot>(((flashInSB.setter port_i\<star>::(((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>)) \<uplus>\<^sub>- sbOut)\<star>\<^sub>2)) \<sqsubseteq>
         (flashOutSB.setter (port_o, port_intern)\<star>)"
  apply(rule fix_least)
  using assms flash_fix by blast

lemma flash_and_weak:
  assumes "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
  shows "#port_o = lnmin\<cdot>(#port_i)\<cdot>(#port_intern)"
proof(cases "#port_i > #port_intern")
  case True
  have "sbLen (andInSB.setter (port_i, port_intern)) = #port_intern"
    apply(subst sblen_rule, simp_all)
    (*defer
    apply(rule_tac x="Abs cout" in exI)*)  
    sorry
  moreover have "sbLen (andOutSB.setter port_o) = #port_o"
    apply(simp add: sbLen_def)
    using andOutSB.setter.rep_eq outAnd.exhaust outAndChan.simps sbgetch_insert2 LeastI andOutSB.setter.abs_eq slen_smap
    by metis
  ultimately have "#port_o = #port_intern"
    using andSpf_def assms dassem_len
    by (metis dawSem_def dawsem_len somechannotempty)
  then show ?thesis 
    apply(simp)
    by (metis True dual_order.strict_implies_order lnmin_asso lnmin_eqasmthmin)
next
  case False
  then show ?thesis sorry
qed 
(*  
  using assms apply(simp add: andSpf_def )
  using dassem_len  
 with weak causal lemma *)

lemma flash_not_strong:
  assumes "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "#port_intern = #port_o + 1"
  (* with strong causal lemma *) sorry

lemma    
  assumes "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
  and "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "#port_intern = #port_i + 1"
proof(rule ccontr)
  assume a0: "\<not> (#port_intern = #port_i +1)"
  show False
  proof(cases "#port_intern  < #port_i + 1")
    case True
    then show ?thesis
      using assms flash_and_weak flash_not_strong by (metis dual_order.strict_implies_not_eq inf_ub ln_less lnat_plus_suc lnle2le lnmin_asso lnmin_eqasmthmin order.not_eq_order_implies_strict)
  next
    case False
    then have a3: "#port_intern > #port_i + 1"
      using a0 by auto
    have a4: "#port_intern = #port_i + 1"
      using assms flash_and_weak flash_not_strong dual_order.strict_implies_order linear lnat_plus_suc lnmin_asso lnmin_eqasmthmin lnsuc_lnle_emb
      sorry
    show ?thesis 
      using a3 a4
      by simp
  qed
qed

lemma flash_ChLen: assumes "Rep c \<in> chDom TYPE(outAnd \<union> outNot)"
    and "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
    and "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "#((\<mu> sbOut::(outAnd \<union> outNot)\<^sup>\<Omega>. andSpf\<cdot>(((flashInSB.setter port_i\<star>::(((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>)) \<uplus>\<^sub>- sbOut)\<star>\<^sub>1) \<uplus> notSpf\<cdot>(((flashInSB.setter port_i\<star>::(((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>)) \<uplus>\<^sub>- sbOut)\<star>\<^sub>2))  \<^enum> c) 
       = #(flashOutSB.setter (port_o, port_intern)\<star>  \<^enum>  c)"
  sorry

lemma sblen_eqI2:
  fixes sb1 sb2::"'cs::chan\<^sup>\<Omega>"
  assumes "sb1 \<sqsubseteq> sb2"
  and "\<And>c. Rep c\<in>chDom TYPE('cs) \<Longrightarrow> #(sb1 \<^enum> c) = #(sb2 \<^enum> c)"
  shows "sb1 = sb2"
  by (simp add: assms(1) assms(2) eq_slen_eq_and_less monofun_cfun_arg sb_eqI)


(* DEUTLICH WICHTIGER! *)
lemma assumes "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
    and "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "(flasherComp\<cdot>(flashInSB.setter (port_i)\<star>)) = (flashOutSB.setter (port_o,port_intern)\<star>)"
  apply(simp add: flasherComp_def genComp_def)
  apply(rule sblen_eqI2)
  apply(simp add: assms(1) assms(2) flash_below)   
  using flash_ChLen assms(1) assms(2) by blast
  

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