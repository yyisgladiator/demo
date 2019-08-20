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

lemma outand_dom[simp]:"chDom TYPE(outAnd) = {cout}"
  apply(simp add: chDom_def Rep_outAnd_def)
  using type_definition.Rep_range type_definition_outAnd by fastforce

lemma innot_dom [simp]:"chDom TYPE(inNot) = {cout}"
  apply(simp add: chDom_def Rep_inNot_def)
  using type_definition.Rep_range type_definition_inNot by fastforce

lemma outnot_dom[simp]:"chDom TYPE(outNot) = {cin2}"
  apply(simp add: chDom_def Rep_outNot_def)
  using type_definition.Rep_range type_definition_outNot by fastforce


(* SWS: Gilt das? ich glaube "port_intern" wird versteck, also ist nach "sbConvert" nichtmehr da *)
lemma flash2andin[simp]:"(((sbConvert::inFlash\<^sup>\<Omega> \<rightarrow> ((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>)\<cdot>(flashInSB.setter port_i)) 
                         \<uplus>\<^sub>\<star> ((sbConvert::outFlash\<^sup>\<Omega> \<rightarrow> (outAnd \<union> outNot)\<^sup>\<Omega>)\<cdot>(flashOutSB.setter (port_o, port_intern)))) 
                          = (andInSB.setter (port_i, port_intern))"
  apply(simp add: sbconvert_insert)
  apply(rule sb_eqI,auto)  
  sorry




lemma andOutSB_port_o: assumes " Rep c = cout" shows " andOutSB.setter port_o  \<^enum>  c = (smap  (Tsyn o (map_option) \<B>))\<cdot>port_o"
  by (metis andOutSB.setter.rep_eq outAnd.exhaust outAndChan.simps sbgetch_insert2)

lemma notOutSB_port_o: assumes " Rep c = cin2" shows " notOutSB.setter port_intern  \<^enum>  c = (smap  (Tsyn o (map_option) \<B>))\<cdot>port_intern"
  by (metis notOutSB.setter.rep_eq outNot.exhaust outNotChan.simps sbgetch_insert2)

lemma notInSB_port_o: assumes " Rep c = cout" shows " notInSB.setter port_intern  \<^enum>  c = (smap  (Tsyn o (map_option) \<B>))\<cdot>port_intern"
  by (metis inNot.exhaust inNotChan.simps notInSB.setter.rep_eq sbgetch_insert2)

lemma outFlash_cout_rep_abs: "(Rep :: outAnd \<union> outNot \<Rightarrow> channel) (Abs cout) \<in>chDom TYPE(outFlash)"
  apply(simp add: chDom_def Rep_outFlash_def)
  apply auto
  apply (metis Rep_outFlash_def  Flashout1_rep chan_eq insert_iff range_eqI rangeoutunion )
  by (simp add: f_inv_into_f rangeoutunion)

 

lemma outFlash_cin2_rep_abs: "(Rep :: outAnd \<union> outNot \<Rightarrow> channel) (Abs cin2) \<in>chDom TYPE(outFlash)"
  apply(simp add: chDom_def Rep_outFlash_def)
  apply auto
  apply (metis Rep_outFlash_def Flashcin2_rep chan_eq insert_iff range_eqI rangeoutunion)
  by (simp add: f_inv_into_f rangeoutunion)


lemma inFlash_cin1_rep_abs: "(Rep :: ((inAnd \<union> inNot) - outAnd \<union> outNot) \<Rightarrow> channel) (Abs cin1) \<in>chDom TYPE(inFlash)"
  apply(simp add: chDom_def Rep_outFlash_def)
  apply auto
  apply (metis compin2flashin  Rep_inFlash_def Flashin1_rep   range_eqI rangeoutunion )
  using range_eq_singletonD rangecompin by auto

lemma inFlash_cin2_rep_abs: "(Rep :: ((inAnd \<union> inNot) - outAnd \<union> outNot) \<Rightarrow> channel) (Abs cin2) \<in>chDom TYPE(inFlash)"
  apply(simp add: chDom_def Rep_outFlash_def)
  apply auto
  apply (metis compin2flashin  Rep_inFlash_def   range_eqI  )
  using range_eq_singletonD rangecompin by auto
 

 
lemma flashOutSB_port_o: assumes " Rep (c::outAnd) = cout" shows "(flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>)  \<^enum>\<^sub>\<star> c = (smap  (Tsyn o (map_option) \<B>))\<cdot>port_o"
  apply(simp add: sbgetch_insert assms rangeoutunion)
  apply(simp add: outFlash_cout_rep_abs)
  apply(simp add: rangeoutunion f_inv_into_f)
  by (metis Flashout1_rep chan_inj flashOutSB.setter.rep_eq inv_f_f outFlashChan.simps(1))
 

lemma flashOutSB_port_o2: assumes " Rep (c::inAnd \<union> inNot) = cout" shows "(flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>)  \<^enum>\<^sub>\<star> c = (smap  (Tsyn o (map_option) \<B>))\<cdot>port_o"
  apply(simp add: sbgetch_insert assms rangeoutunion) 
  apply(simp add: outFlash_cout_rep_abs)
  apply(simp add: rangeoutunion f_inv_into_f)
  by (metis Flashout1_rep chan_inj flashOutSB.setter.rep_eq inv_f_f outFlashChan.simps(1)) 


lemma flashOutSB_port_inter: assumes " Rep (c::outNot) = cin2" shows "(flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>)  \<^enum>\<^sub>\<star> c = (smap  (Tsyn o (map_option) \<B>))\<cdot>port_intern"
  apply(simp add: sbgetch_insert assms rangeoutunion)
  apply(simp add: outFlash_cin2_rep_abs)
  apply(simp add: rangeoutunion f_inv_into_f)
  by (metis Flashcin2_rep chan_inj flashOutSB.setter.rep_eq inv_f_f outFlashChan.simps(2))

lemma flashInSB_port_i: assumes " Rep (c::outNot) = cin1" shows "(flashInSB.setter port_i\<star> :: ((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>)  \<uplus>\<^sub>\<star> (z::(outAnd \<union> outNot)\<^sup>\<Omega>)  \<^enum>\<^sub>\<star> c = (smap  (Tsyn o (map_option) \<B>))\<cdot>port_i"
  apply(simp add: sbgetch_insert assms rangeoutunion)
  using rangeinunion rangeoutunion  f_inv_into_f inFlash_cin1_rep_abs
  Rep_outNot Rep_outNot_def assms by auto   

lemma AndInSB_port_i: assumes " Rep (c::outNot) = cin1" shows "andInSB.setter ( port_i  , notOutSB.getter (z\<star>\<^sub>2))   \<^enum>\<^sub>\<star>  c = (smap  (Tsyn o (map_option) \<B>))\<cdot>port_i"
  apply(simp add: sbgetch_insert assms rangeoutunion)
  using rangeinunion rangeoutunion  f_inv_into_f inFlash_cin1_rep_abs
  Rep_outNot Rep_outNot_def assms 
  by simp         

lemma flashInSB_port_z: assumes " Rep (c::outNot) = cin2" shows "(flashInSB.setter port_i\<star> :: ((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>)  \<uplus>\<^sub>\<star> (z::(outAnd \<union> outNot)\<^sup>\<Omega>)  \<^enum>\<^sub>\<star> c = (smap  (Tsyn o (map_option) \<B>))\<cdot>(notOutSB.getter(z\<star>))"
  apply(simp add: sbgetch_insert assms rangeoutunion)
  using rangeinunion rangeoutunion  f_inv_into_f inFlash_cin2_rep_abs
  Rep_outNot Rep_outNot_def assms sorry



lemma flash2andout[simp]:"(flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>)\<star>\<^sub>1 = andOutSB.setter port_o"
  apply(rule sb_eqI, auto)
  by(simp add: flashOutSB_port_o andOutSB_port_o)
  (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

lemma inFlash_rep_abs: "(Rep :: inAnd \<union> inNot \<Rightarrow> channel) (Abs cin1) \<in> range (Rep :: inFlash \<Rightarrow> channel)"
  by (metis Flashin1_rep f_inv_into_f insertI1 rangeinunion repinrange)

lemma ninFlash_rep_abs: "(Rep :: ((inAnd \<union> inNot) - outAnd \<union> outNot)  \<Rightarrow> channel) (Abs cout) \<in> range (Rep :: inFlash \<Rightarrow> channel)"
 
  using compin2flashin by auto
lemma ninFlash_rep_abs2: "(Rep :: ((inAnd \<union> inNot) - outAnd \<union> outNot)  \<Rightarrow> channel) (Abs cout) \<notin> range (Rep :: outFlash \<Rightarrow> channel)"

  by (metis (full_types) Flashcin2_rep Flashout1_rep channel.distinct(25) channel.distinct(27) compin2flashin empty_iff f_inv_into_f insert_iff ninFlash_rep_abs outFlash.exhaust rangecompin)


lemma test:"(Rep :: (inNot)  \<Rightarrow> channel) (Abs cout) \<notin> chDom TYPE((inAnd \<union> inNot) - outAnd \<union> outNot) "
 apply(simp add: chDom_def )
 apply auto
  by (metis Flashout1_rep Notin1_rep abs_rep_id ninFlash_rep_abs2 rangeI)
lemma test3:assumes " Rep (c::inNot) = cout" shows " (flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>)  \<^enum>\<^sub>\<star> c = (smap  (Tsyn o (map_option) \<B>))\<cdot>port_o"
  apply(simp add: sbgetch_insert assms rangeoutunion) 
  apply(simp add: outFlash_cout_rep_abs)
  apply(simp add: rangeoutunion f_inv_into_f)
  by (metis Flashout1_rep chan_inj flashOutSB.setter.rep_eq inv_f_f outFlashChan.simps(1))



lemma test4: "((flashInSB.setter port_i\<star> :: ((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>) \<uplus>\<^sub>\<star> (flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>)) =  (flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>)"
  by(rule sb_eqI,auto)
lemma test5:assumes " Rep (c::inNot) = cout" shows "((flashInSB.setter port_i\<star> :: ((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>) \<uplus>\<^sub>\<star> (flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>))  \<^enum>\<^sub>\<star> c = (flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>)  \<^enum>\<^sub>\<star> c"
   apply(simp add: sbgetch_insert assms rangeoutunion)
  using  rangeoutunion  f_inv_into_f  assms  ninFlash_rep_abs2 
  
  sorry

lemma flashInSB_port_o: assumes " Rep (c::inNot) = cout" shows "((flashInSB.setter port_i\<star> :: ((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>) \<uplus>\<^sub>\<star> (flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>))  \<^enum>\<^sub>\<star> c = (smap  (Tsyn o (map_option) \<B>))\<cdot>port_o"

  
  using  assms test3
  by (simp add: test5)

 

 

lemma flash2notin[simp]:"(flashInSB.setter port_i\<star> :: ((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>) \<uplus>\<^sub>\<star> (flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>) = notInSB.setter(port_o)"
  apply(rule sb_eqI , auto)
  
  by(simp add: flashInSB_port_o notInSB_port_o )


   (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)
lemma flash2notout[simp]:"(flashOutSB.setter (port_o, port_intern)\<star> :: (outAnd \<union> outNot)\<^sup>\<Omega>)\<star> = notOutSB.setter port_intern "
  apply(rule sb_eqI, auto)  
  by(simp add: flashOutSB_port_inter notOutSB_port_o)
   (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

lemma flash2andinnotout[simp]:"(flashInSB.setter port_i\<star> :: ((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>) \<uplus>\<^sub>\<star> (z::(outAnd \<union> outNot)\<^sup>\<Omega>) = andInSB.setter (port_i,notOutSB.getter(z\<star>))"
   apply(rule sb_eqI, auto)  

proof -
  fix c :: inAnd
have "z = flashOutSB.setter (andOutSB.getter (z\<star>\<^sub>1), notOutSB.getter (z\<star>\<^sub>2))\<star>"
  by (metis andOutSB.sbGen_axioms flash2andout flash2notout notOutSB.set_get sbGen.set_get ubunion_id)
  then show "(flashInSB.setter port_i\<star> \<uplus>\<^sub>- z::(inAnd \<union> inNot)\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c = andInSB.setter (port_i, notOutSB.getter (z\<star>\<^sub>2)) \<^enum> c"
by (metis flash2andin sbconvert_getch union_minus_nomagfst)
next

  fix c :: inAnd
have "z = flashOutSB.setter (andOutSB.getter (z\<star>\<^sub>1), notOutSB.getter (z\<star>\<^sub>2))\<star>"
  by (metis andOutSB.sbGen_axioms flash2andout flash2notout notOutSB.set_get sbGen.set_get ubunion_id)
  then show "(flashInSB.setter port_i\<star> \<uplus>\<^sub>- z::(inAnd \<union> inNot)\<^sup>\<Omega>) \<^enum>\<^sub>\<star> c = andInSB.setter (port_i, notOutSB.getter (z\<star>\<^sub>2)) \<^enum> c"
    by (metis flash2andin sbconvert_getch union_minus_nomagfst)
qed
 (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)

lemma flash2notinandout[simp]:"(flashInSB.setter port_i\<star> :: ((inAnd \<union> inNot) - outAnd \<union> outNot)\<^sup>\<Omega>) \<uplus>\<^sub>\<star> (z::(outAnd \<union> outNot)\<^sup>\<Omega>) = notInSB.setter (andOutSB.getter(z\<star>))"
    apply(rule sb_eqI, auto)  

  by (metis flash2andin flashInSB_port_o notInSB.set_get notInSB_port_o sbconvert_getch)
   (* SWS: Gilt Nicht, doppelte magie. Anstatt den Zwischen-Datentyp zu fixieren und assumptions zu haben...
                kann man die magischen-sachen durch nicht-magie ersetzen? *)


lemma t1: "(\<Lambda> (sbOut::(outAnd \<union> outNot)\<^sup>\<Omega>). andSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut) \<uplus> notSpf\<cdot>((flashInSB.setter port_i\<star>::inFlash\<^sup>\<Omega>) \<uplus>\<^sub>\<star> sbOut))\<cdot>
           (flashOutSB.setter (port_o, port_intern)\<star>) = (flashOutSB.setter (port_o, port_intern)\<star>::(outAnd \<union> outNot)\<^sup>\<Omega>)"
  sorry

lemma t2: assumes "Rep c\<in>chDom TYPE(outAnd \<union> outNot)" 
  shows "#((\<mu> sbOut::(outAnd \<union> outNot)\<^sup>\<Omega>. andSpf\<cdot>(flashInSB.setter port_i\<star> \<uplus>\<^sub>\<star> sbOut) \<uplus> notSpf\<cdot>(flashInSB.setter port_i\<star> \<uplus>\<^sub>\<star> sbOut)) \<^enum> c) =
         #((flashOutSB.setter (port_o, port_intern)\<star>) \<^enum> c)"
  sorry

lemma sblen_eqI2:
  fixes sb1 sb2::"'cs\<^sup>\<Omega>"
  assumes "sb1 \<sqsubseteq> sb2"
  assumes "\<And>c. Rep c\<in>chDom TYPE('cs) \<Longrightarrow> #(sb1 \<^enum> c) = #(sb2 \<^enum> c)"
  shows "sb1 = sb2"
  sorry
(* DEUTLICH WICHTIGER! *)
lemma assumes "andSpf\<cdot>(andInSB.setter (port_i, port_intern)) = andOutSB.setter port_o"
    and "notSpf\<cdot>(notInSB.setter(port_o)) = notOutSB.setter port_intern"
  shows "(flasherComp\<cdot>(flashInSB.setter (port_i)\<star>)) = (flashOutSB.setter (port_o,port_intern)\<star>)"
  apply(simp add: flasherComp_def convflasherComp_def spfConvert_def)
  apply(rule spfcomp_eqI,simp)
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


