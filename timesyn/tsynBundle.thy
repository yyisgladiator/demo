(*  Title:        tsynBundle.thy
    Author:       Dennis Slotboom
    E-Mail:       dennis.slotboom@rwth-aachen.de

    Description:  Time-synchronous stream bundles.
*)

chapter {* Time-Synchronous Stream Bundles *}

theory tsynBundle
imports tsynStream "../untimed/SB" "../UFun_Templates" "../untimed/SpfStep"

begin

default_sort message

(* ----------------------------------------------------------------------- *)
  section {* tsynbNull - Automaton *}
(* ----------------------------------------------------------------------- *)

(* ToDo: add descriptions. *)

lift_definition tsynbNull :: "channel \<Rightarrow> 'm tsyn SB" is
  "\<lambda>c. [c \<mapsto> \<up>null]"
  by (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)
    
lemma tsynbnull_ubdom [simp]: "ubDom\<cdot>(tsynbNull c) = {c}"
  by (simp add:tsynbNull.rep_eq ubdom_insert)

lemma tsynbnull_ubgetch [simp]: "tsynbNull c  .  c = \<up>null"
  by (simp add: tsynbNull.rep_eq ubgetch_insert)

lemma tsynbnull_ubconc [simp]:
  assumes "c \<in> ubDom\<cdot>sb"
  shows "ubConc (tsynbNull c)\<cdot>sb  .  c = \<up>null \<bullet> (sb  .  c)"
  by (simp add: assms usclConc_stream_def)
    
lemma tsynbnull_ubconc_sbrt [simp]:
  assumes "ubDom\<cdot>sb = {c}"
  shows "sbRt\<cdot>(ubConc (tsynbNull c)\<cdot>sb) = sb"
  apply (rule ub_eq)
  by (simp add: assms sbRt_def usclConc_stream_def)+

(* ----------------------------------------------------------------------- *)
  section {* Definitions on Time-Synchronous Stream Bundles *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynbAbs}: Filter the nulls on each stream of the bundle and return the corresponding bundle. *}
definition tsynbAbs :: "'a tsyn stream ubundle \<rightarrow> 'a stream ubundle" where 
  "tsynbAbs \<equiv> \<Lambda> sb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynAbs\<cdot>(sb . c)))"

text {* @{term tsynbRemDups} removes all duplicates of the time-synchronous stream on every channel of the bundle. *}
definition tsynbRemDups :: "'a tsyn stream ubundle \<rightarrow> 'a tsyn stream ubundle" where 
  "tsynbRemDups \<equiv> \<Lambda> sb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c)))"

(* ----------------------------------------------------------------------- *)
  section {* Definitions of Time-Synchronous Test Bundles *}
(* ----------------------------------------------------------------------- *)
(* Already in UFun_Templates.thy
instantiation nat :: message
begin
  fun ctype_nat :: "channel \<Rightarrow> nat set" where 
  "ctype_nat c = range nat" 
  instance
    by (intro_classes)
end*)
 
lift_definition tsynbabsTestInput :: "nat tsyn stream ubundle " is 
  "[c1 \<mapsto> <[Msg (1 :: nat), null, Msg 2, Msg 1]>]"
  apply (simp add: ubWell_def usclOkay_stream_def ctype_tsyn_def)
  by (metis image_eqI nat_1 nat_2 numeral_2_eq_2 range_eqI)

lift_definition tsynbabsTestOutput :: "nat stream ubundle " is 
  "[c1 \<mapsto> <[(1 :: nat), 2, 1]>]"
  apply (simp add: ubWell_def usclOkay_stream_def)
  by (metis nat_1 nat_2 numeral_2_eq_2 range_eqI)

lemma tsynbabstestinput_ubdom: "ubDom\<cdot>tsynbabsTestInput = {c1}"
  by (simp add: ubDom_def tsynbabsTestInput.rep_eq)

(* ----------------------------------------------------------------------- *)
  section {* Lemmata on Time-Synchronous Stream Bundles *}
(* ----------------------------------------------------------------------- *)    

(* ----------------------------------------------------------------------- *)
  subsection {* tsynbAbs *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynAbs} channel is usclOkay. *}   
lemma tsynAbs_dom: "\<And>s c. usclOkay c s = usclOkay c (tsynAbs\<cdot>s)"
  apply(rule tsyn_ind)
  apply(simp add: usclOkay_stream_def adm_def)
  defer
  apply(simp add: ctype_tsyn_def usclOkay_stream_def)
  apply(simp add: ctype_tsyn_def usclOkay_stream_def tsynabs_sconc_msg)
  apply auto[1]
  apply(simp add: ctype_tsyn_def usclOkay_stream_def tsynabs_sconc_null)
  using chain_monofun contlub_cfun_arg dual_order.trans l44 sdom_chain2lub
  by smt

text {* @{term tsynbAbs} bundle is ubwell. *}   
lemma tsynbabs_ubwell [simp]: "ubWell (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynAbs\<cdot>(sb . c)))"
  (*by (smt domIff option.sel tsynAbs_dom ubWell_def ubdom_channel_usokay ubgetch_insert)*)
  proof -
    obtain cc :: "(channel \<Rightarrow> 'a stream option) \<Rightarrow> channel" where
      f1: "\<forall>f. cc f \<in> dom f \<and> \<not> usclOkay (cc f) f\<rightharpoonup>cc f \<or> ubWell f"
        by (metis ubwellI)
    { assume "usclOkay (cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c))) (tsynAbs\<cdot> Rep_ubundle sb\<rightharpoonup>cc (\<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot>(sb . c)))"
      moreover
      { assume "tsynAbs\<cdot> Rep_ubundle sb\<rightharpoonup>cc (\<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot> (sb . c)) \<noteq> \<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot> (sb . c)\<rightharpoonup>cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c))"
        then have "\<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot> (sb . c)\<rightharpoonup>cc (\<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<noteq> tsynAbs\<cdot> (sb . cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c)))"
          by (simp add: ubgetch_insert)
  then have "cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<in> ubDom\<cdot>sb \<longrightarrow> cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<notin> dom (\<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<or> usclOkay (cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c))) \<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot> (sb . c)\<rightharpoonup>cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c))"
    by force }
      ultimately have "cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<in> ubDom\<cdot>sb \<longrightarrow> (cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<notin> dom (\<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<or> usclOkay (cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c))) \<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot> (sb . c)\<rightharpoonup>cc (\<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot>(sb . c))) \<or> ubWell (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c))"
        by force }
    then have "cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<in> ubDom\<cdot>sb \<longrightarrow> (cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<notin> dom (\<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<or> usclOkay (cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c))) \<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot> (sb . c)\<rightharpoonup>cc (\<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot>(sb . c))) \<or> ubWell (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c))"
      using tsynAbs_dom ubdom_channel_usokay by blast
    then have "ubWell (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<or> cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<notin> dom (\<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot>(sb . c)) \<or> usclOkay (cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c))) \<lambda>c. (c \<in> ubDom\<cdot> sb)\<leadsto>tsynAbs\<cdot> (sb . c)\<rightharpoonup>cc (\<lambda>c. (c \<in> ubDom\<cdot>sb)\<leadsto>tsynAbs\<cdot>(sb . c))"
      by fastforce
    then show ?thesis
      using f1 by meson
  qed

text {* Domain of the @{term tsynbAbs} output bundle is ubDom\<cdot>sb. *}    
lemma tsynbabs_ubundle_ubdom: "ubDom\<cdot>(sb::'a tsyn stream ubundle) = ubDom\<cdot>(Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynAbs\<cdot>(sb . c)))) "
  by (simp add: ubdom_ubrep_eq)

text {* @{term tsynbAbs} is monotonic. *}    
lemma tsynbabs_mono [simp]: "monofun (\<lambda> sb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynAbs\<cdot>(sb . c))))"
  apply (rule monofunI)
  apply (simp add: ubdom_below)
  apply (simp add: ubdom_insert)
  using below_option_def below_ubundle_def domIff fun_below_iff monofun_cfun_arg option.sel option.simps(3) tsynAbs_dom ubWell_def ubgetch_insert ubrep_ubabs ubrep_well
  by smt

(*text {* The @{term tsynbAbs} output bundle is a chain. *}     
lemma tsynbabs_chain [simp]: 
  assumes "c\<in>ubDom\<cdot>sb"
  shows "chain (Y:: nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>) \<Longrightarrow> ubDom\<cdot>(Y 0) = {c} \<Longrightarrow> 
         chain (\<lambda> i. Abs_ubundle [c \<mapsto> tsynAbs\<cdot>(Y i . c)])"
  apply (rule chainI)
  apply (rule ub_below)
  apply (simp add: assms ubdom_ubrep_eq)
  apply (simp add: ubdom_ubrep_eq)
  by (simp add: monofun_cfun_arg po_class.chainE ubgetch_ubrep_eq)*)

text {* @{term tsynbAbs} is continous.*}    
lemma tsynbabs_cont [simp]: "cont (\<lambda> sb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynAbs\<cdot>(sb . c))))"
  proof (rule contI2, auto)
    show  "\<And>Y::nat \<Rightarrow> 'b tsyn stream\<^sup>\<Omega>.
       chain Y \<Longrightarrow>
       Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(\<Squnion>i. Y i))\<leadsto>tsynAbs\<cdot>((\<Squnion>i. Y i)  .  c)) \<sqsubseteq> (\<Squnion>i. Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(\<Squnion>j. Y j))\<leadsto>tsynAbs\<cdot>(Y i  .  c)))"
      sorry
  qed

(*text {* @{term tsynbAbs} satisfies well condition for universal functions. *}  
lemma tsynbabs_ufwell [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynAbs\<cdot>s)"
  shows "ufWell (tsynbAbs:: 'a tsyn stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) option)"
  apply(simp add: tsynbAbs_def)
  apply (rule ufun_wellI)
  apply (simp_all add: domIff2 assms)
  apply (simp_all add: ubclDom_ubundle_def)
  apply (simp add: ubdom_insert)
  by (simp add: assms ubdom_insert)  *)

text {* @{term tsynbAbs} insertion lemma. *}
lemma tsynbabs_insert: "tsynbAbs\<cdot>(sb ::'a tsyn stream\<^sup>\<Omega>) = Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynAbs\<cdot>(sb . c)))"
  by (simp add: tsynbAbs_def)

text {* @{term tsynbAbs} getchannel lemma. *}
lemma tsynbabs_sbgetch [simp]: assumes "c\<in>ubDom\<cdot>sb"
  shows "(tsynbAbs\<cdot>sb) . c = tsynAbs\<cdot>(sb . c)"
  by (simp add: assms tsynbabs_insert ubgetch_ubrep_eq)

text {* @{term tsynbAbs} not sure why it is here. *}
lemma tsynabs_sdom: "(sdom\<cdot>s \<subseteq> insert - (Msg ` range a)) = (sdom\<cdot>(tsynAbs\<cdot>s) \<subseteq> range a)"
  proof (induction s rule: tsyn_ind)
    case adm
    then show ?case 
      by (rule admI, simp add: contlub_cfun_arg lub_eq_Union UN_subset_iff)
  next
    case bot
    then show ?case 
      by simp
  next
    case (msg m s)
    then show ?case 
      by (simp only: tsynabs_sconc_msg sdom2un, auto)
  next
    case (null s)
    then show ?case 
      by (simp only: tsynabs_sconc_null sdom2un, auto)
  qed

text {* @{term tsynbAbs} is strict. *}
lemma tsynbabs_strict [simp]: "tsynbAbs\<cdot>(ubLeast {c} :: 'a tsyn stream\<^sup>\<Omega>) = ubLeast {c}"
  apply(simp add: tsynbabs_insert)
  apply(simp add: ubLeast_def)
  by (metis (no_types, hide_lams) singletonI tsynabs_strict ubleast_ubgetch)

text {* Test lemma for @{term tsynbAbs}. *}
lemma tsynbabs_test_finstream:
  "tsynbAbs\<cdot>(tsynbabsTestInput) = tsynbabsTestOutput"
  apply (simp add: tsynbabs_insert)
  apply (simp only: tsynbabsTestInput_def tsynbabsTestOutput_def)
  apply (subst ubgetch_ubrep_eq)
  apply (metis tsynbabsTestInput.rep_eq ubrep_well)
  apply (simp add: ubdom_insert tsynabs_insert)
  using tsynbabsTestInput.abs_eq tsynbabsTestInput.rep_eq sorry

(* ----------------------------------------------------------------------- *)
  subsection {* tsynbRemDups *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynbRemDups} bundle is ubwell. *}   
lemma tsynbremdups_ubwell [simp]: "ubWell (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c)))"
  sorry

text {* Domain of the @{term tsynbRemDups} output bundle is ubDom\<cdot>sb. *}    
lemma tsynbremdups_ubundle_ubdom: "ubDom\<cdot>(sb::'a tsyn stream ubundle) = ubDom\<cdot>(Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c)))) "
  by (simp add: ubdom_ubrep_eq)

text {* @{term tsynbRemDups} is monotonic. *}
lemma tsynbremdups_mono [simp]: "monofun (\<lambda>sb. Abs_ubundle(\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c))))"
  apply (rule monofunI)
  apply (simp add: ubdom_below)
  apply (simp add: ubdom_insert)
  sorry

text {* @{term tsynbRemDups} is continous. *}
lemma tsynbremdups_cont [simp]: "cont (\<lambda>sb. Abs_ubundle(\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c))))"
  sorry

text {* @{term tsynbRemDups} insertion lemma. *}
lemma tsynbremdups_insert: "tsynbRemDups\<cdot>sb = Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c)))"
  by (simp add: tsynbRemDups_def)

(*text {* @{term tsynbRemDups} satisfies well condition for universal functions. *}
lemma tsynbremdups_ufwell [simp]:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "ufWell (Abs_cfun (\<lambda>sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                             \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb . c1)])))"
  apply (rule uf_1x1_well)
  by (simp add: assms map_io_well_1x1_def)*)

(*text {* Domain of @{term tsynbRemDups} is {c1}. *}
lemma tsynbremdups_ufdom:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "ufDom\<cdot>(Abs_cufun (\<lambda> sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                              \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb . c1)]))) = {c1}"
  apply (rule uf_1x1_rep_dom)
  by (simp add: assms map_io_well_1x1_def)

text {* Range of @{term tsynbRemDups} is {c2}. *}
lemma tsynbremdups_ufran:
  assumes "\<And>s :: 'a tsyn stream. usclOkay c1 s = usclOkay c2 (tsynRemDups\<cdot>s)"
  shows "ufRan\<cdot>(Abs_cufun (\<lambda> sb :: 'a tsyn stream\<^sup>\<Omega>. (ubDom\<cdot>sb = {c1}) 
                              \<leadsto> (Abs_ubundle [c2 \<mapsto> tsynRemDups\<cdot>(sb . c1)]))) = {c2}"
  apply (rule uf_1x1_rep_ran)
  by (simp add: assms map_io_well_1x1_def)*)

text {* @{term tsynbRemDups} is strict.*}
lemma tsynbremdups_strict [simp]: "tsynbRemDups\<cdot>(ubLeast {c} :: 'a tsyn stream ubundle) = ubLeast {c}"
  apply(simp add: tsynbremdups_insert)
  apply(simp add: ubLeast_def)
  by (metis (no_types, hide_lams) singletonI tsynremdups_strict ubleast_ubgetch)

 
end