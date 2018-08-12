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
  "tsynbAbs \<equiv> \<Lambda> sb. Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> tsynAbs\<cdot>(sb . c))"

text {* @{term tsynbRemDups} removes all duplicates of the time-synchronous stream on every channel of the bundle. *}
definition tsynbRemDups :: "'a tsyn stream ubundle \<rightarrow> 'a tsyn stream ubundle" where 
  "tsynbRemDups \<equiv> \<Lambda> sb. Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> tsynRemDups\<cdot>(sb . c))"

(* ----------------------------------------------------------------------- *)
  section {* Definitions of Time-Synchronous Test Bundles *}
(* ----------------------------------------------------------------------- *)
 
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

lemma tsynbabstestoutput_ubdom: "ubDom\<cdot>tsynbabsTestOutput = {c1}"
  by (simp add: tsynbabsTestOutput.rep_eq ubDom_def)

(* ----------------------------------------------------------------------- *)
  section {* Lemmata on Time-Synchronous Stream Bundles *}
(* ----------------------------------------------------------------------- *)    

(* ----------------------------------------------------------------------- *)
  subsection {* tsynbAbs *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynAbs} channel is usclOkay. *}
lemma tsynabs_sdom: assumes "sdom\<cdot>s \<subseteq> ctype c" shows "sdom\<cdot>(tsynAbs\<cdot>s) \<subseteq> ctype c"
  using assms
  apply (induction s rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (metis (no_types, lifting) ch2ch_Rep_cfunR contlub_cfun_arg l44 sdom_chain2lub subset_trans)
  apply (simp_all add: tsynabs_sconc_msg tsynabs_sconc_null)
  using ctype_tsyn_iff by auto

text {* @{term tsynbAbs} ubundle is ubwell. *}   
lemma tsynbabs_ubwell [simp]: "ubWell (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (tsynAbs\<cdot>(sb . c)))"
  by (simp add: tsynabs_sdom)

text {* Domain of the @{term tsynbAbs} output bundle is the same as the input bundle domain. *}    
lemma tsynbabs_ubundle_ubdom:
  "ubDom\<cdot>(Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> tsynAbs\<cdot>(sb . c))) = ubDom\<cdot>sb"
  by (simp add: ubdom_ubrep_eq)

text {* @{term tsynbAbs} is monotonic. *}    
lemma tsynbabs_mono [simp]: "monofun (\<lambda> sb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> tsynAbs\<cdot>(sb . c)))"
  apply (rule monofunI)
  apply (simp add: ubdom_insert below_ubundle_def)
  apply (subst ubrep_ubabs, metis (no_types) tsynbabs_ubwell ubdom_insert)+
  apply (simp add: fun_below_iff)
  apply (rule)+
  apply (metis monofun_cfun_arg some_below some_below2 ubdom_insert ubgetchE)
  by (metis below_option_def domIff)+

text {* @{term tsynbAbs} is continous. *}  
lemma tsynbabs_cont [simp]: "cont (\<lambda> sb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynAbs\<cdot>(sb . c))))"
  apply (rule cont_Abs_UB, simp_all)
  apply (rule contI2)
  apply (rule monofunI)
  apply (simp add: below_option_def fun_below_iff monofun_cfun_arg ubdom_below)
  sorry

text {* @{term tsynbAbs} insertion lemma. *}
lemma tsynbabs_insert: 
  "tsynbAbs\<cdot>sb = Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> tsynAbs\<cdot>(sb . c))"
  by (simp add: tsynbAbs_def)

text {* @{term tsynbAbs} get channel lemma. *}
lemma tsynbabs_ubgetch: 
  assumes "c \<in> ubDom\<cdot>sb"
  shows "(tsynbAbs\<cdot>sb) . c = tsynAbs\<cdot>(sb . c)"
  by (simp add: assms tsynbabs_insert ubgetch_ubrep_eq)

text {* @{term tsynbAbs} is strict. *}
lemma tsynbabs_strict [simp]: "tsynbAbs\<cdot>(ubLeast {c})  = ubLeast {c}"
  apply (rule ub_eq)
  apply (metis (no_types, lifting) tsynbabs_insert tsynbabs_ubundle_ubdom ubleast_ubdom)
  by (metis (no_types, lifting) Abs_cfun_inverse2 tsynabs_strict tsynbAbs_def tsynbabs_cont 
      tsynbabs_ubgetch tsynbabs_ubundle_ubdom ubleast_ubdom ubleast_ubgetch)

text {* Test lemma for @{term tsynbAbs}. *}
lemma tsynbabs_test_finstream:
  "tsynbAbs\<cdot>(tsynbabsTestInput) = tsynbabsTestOutput"
  proof (rule ub_eq)
    have tsynbabs_tsynbabstestinput_ubdom: "ubDom\<cdot>(tsynbAbs\<cdot>tsynbabsTestInput) = {c1}"
      by (metis (no_types) tsynbabs_insert tsynbabs_ubundle_ubdom tsynbabstestinput_ubdom)
    show "ubDom\<cdot>(tsynbAbs\<cdot>tsynbabsTestInput) = ubDom\<cdot>tsynbabsTestOutput"
      by (simp add: tsynbabs_tsynbabstestinput_ubdom tsynbabstestoutput_ubdom)
    fix c :: "channel"
    have tsynabs_result: "tsynAbs\<cdot>(<[Msg (1 :: nat), null, Msg 2, Msg 1]>) = <[(1 :: nat), 2, 1]>"
      by (simp add: tsynabs_insert)
    have tsynabs_tsynbabstestinput_result: "tsynAbs\<cdot>(tsynbabsTestInput . c1)= <[(1 :: nat), 2, 1]>"
      by (metis fun_upd_same option.sel tsynabs_result tsynbabsTestInput.rep_eq ubgetch_insert)
    have tsynbabs_tsynbabstestinput_result:
      "tsynbAbs\<cdot>tsynbabsTestInput  .  c1 = tsynbabsTestOutput  .  c1"
      by (metis (full_types) fun_upd_apply insert_iff option.sel tsynabs_tsynbabstestinput_result 
          tsynbabsTestOutput.rep_eq tsynbabs_ubgetch tsynbabstestinput_ubdom ubgetch_insert)
    assume "c \<in> ubDom\<cdot>(tsynbAbs\<cdot>tsynbabsTestInput)"
    then show "tsynbAbs\<cdot>tsynbabsTestInput  .  c = tsynbabsTestOutput  .  c"
      using tsynbabs_tsynbabstestinput_result tsynbabs_tsynbabstestinput_ubdom by auto
  qed

(* ----------------------------------------------------------------------- *)
  subsection {* tsynbRemDups *}
(* ----------------------------------------------------------------------- *)

text {* @{term tsynRemDups_h} channel is usclOkay. *}  
lemma tsynremdups_h_sdom: assumes "sdom\<cdot>s \<subseteq> ctype c" 
  shows "sdom\<cdot>((sscanlA tsynRemDups_h state)\<cdot>s) \<subseteq> ctype c"
  using assms
  apply (induction s arbitrary: state rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (metis (no_types, lifting) ch2ch_Rep_cfunR contlub_cfun_arg l44 sdom_chain2lub subset_trans)
  by (simp add: ctype_tsyn_def)

text {* @{term tsynRemDups} channel is usclOkay. *}  
lemma tsynremdups_sdom: assumes "sdom\<cdot>s \<subseteq> ctype c" shows "sdom\<cdot>(tsynRemDups\<cdot>s) \<subseteq> ctype c"
  by (simp add: assms tsynremdups_insert tsynremdups_h_sdom)

text {* @{term tsynbRemDups} ubundle is ubwell. *}   
lemma tsynbremdups_ubwell [simp]: "ubWell (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c)))"
  by (simp add: tsynremdups_sdom)

text {* Domain of the @{term tsynbRemDups} output bundle is the same as the input bundle domain. *}    
lemma tsynbremdups_ubundle_ubdom: 
  "ubDom\<cdot>(Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c)))) = ubDom\<cdot>sb"
  by (simp add: ubdom_ubrep_eq)

text {* @{term tsynbRemDups} is monotonic. *}
lemma tsynbremdups_mono [simp]: "monofun (\<lambda>sb. Abs_ubundle(\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c))))"
  apply (rule monofunI)
  apply (simp add: ubdom_insert below_ubundle_def)
  apply (subst ubrep_ubabs, metis (no_types) tsynbremdups_ubwell ubdom_insert)+
  apply (simp add: fun_below_iff)
  apply (rule)+
  apply (metis monofun_cfun_arg some_below some_below2 ubdom_insert ubgetchE)
  by (metis below_option_def domIff)+

text {* @{term tsynbRemDups} is continous. *}
lemma tsynbremdups_cont [simp]: "cont (\<lambda>sb. Abs_ubundle(\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c))))"
   proof (rule contI2, auto)
    fix Y::"nat \<Rightarrow> 'a tsyn stream\<^sup>\<Omega>"
    assume a1: "chain Y"
    have "Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(\<Squnion>i. Y i))\<leadsto>tsynRemDups\<cdot>((\<Squnion>i. Y i)  .  c)) = (\<Squnion>i. Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(\<Squnion>j. Y j))\<leadsto>tsynRemDups\<cdot>(Y i  .  c)))"
      proof(rule ub_eq)
        have tsynbremdups_chain: "chain (\<lambda>i. (Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i  .  c))))"
          proof (rule chainI)
            have chain_tsyn_stream: "\<And>i::nat. (Y i::'a tsyn stream\<^sup>\<Omega>) \<sqsubseteq> (Y (Suc i)::'a tsyn stream\<^sup>\<Omega>)"
              by (simp add: a1 po_class.chainE)
            have chain_mono: "\<forall>x y.(x::'a tsyn stream\<^sup>\<Omega>) \<sqsubseteq> (y::'a tsyn stream\<^sup>\<Omega>) \<longrightarrow> (Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>x)\<leadsto>tsynRemDups\<cdot>(x  .  c)) \<sqsubseteq>
              Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>y)\<leadsto>tsynRemDups\<cdot>(y  .  c)))"
              using monofun_def by fastforce
            have ubdom_eq: "(\<And>i::nat. ubDom\<cdot>(Lub Y) = ubDom\<cdot>(Y i))"
              by (simp add: a1)
            have chain_dom: "\<And>i::nat. Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Y i))\<leadsto>tsynRemDups\<cdot>(Y i  .  c)) \<sqsubseteq>
                Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Y (Suc i)))\<leadsto>tsynRemDups\<cdot>(Y (Suc i)  .  c))"
              by (simp add: chain_tsyn_stream local.chain_mono)
            show "\<And>i::nat. Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i  .  c)) \<sqsubseteq>
              Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y (Suc i)  .  c))"
              using chain_dom ubdom_eq by auto
          qed
        have tsynbremdups_lub_dom: "\<And>i. ubDom\<cdot>(\<Squnion>i::nat. Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i  .  c))) =
                      ubDom\<cdot>(Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i  .  c)))"
          using ubdom_below tsynbremdups_chain  ubdom_chain_eq2 by fastforce
        show ubdom_lub_eq: "ubDom\<cdot>(Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>((\<Squnion>i::nat. Y i)  .  c))) =
                        ubDom\<cdot>(\<Squnion>i::nat. Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i  .  c)))"
          proof -
            have ubdom_lub: "ubDom\<cdot>(Lub Y) = ubDom\<cdot>(\<Squnion>i::nat. Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i  .  c)))"
              proof -
                have h1: "\<And>n. ubDom\<cdot> (Lub Y) = ubDom\<cdot>(Y n)"
                  by (simp add: a1)
                then have "\<And>n. ubDom\<cdot> (Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot> (Lub Y))\<leadsto>tsynRemDups\<cdot>(Y n . c))) = ubDom\<cdot>(Y n)"
                  proof -
                    fix n :: nat
                    have "\<exists>na. ubDom\<cdot> (Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(Y na))\<leadsto>tsynRemDups\<cdot>(Y n . c))) = ubDom\<cdot>(Y n)"
                      using tsynbremdups_ubundle_ubdom by blast
                    then show "ubDom\<cdot> (Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y n . c))) = ubDom\<cdot>(Y n)"
                      using h1 by auto
                  qed
                  then show ?thesis
                  using a1 tsynbremdups_lub_dom by auto
              qed
              then show ?thesis
                using tsynbremdups_ubundle_ubdom by blast
          qed
        show "\<And>c. c \<in> ubDom\<cdot>(Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>((\<Squnion>i. Y i)  .  c))) \<Longrightarrow>
         Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>((\<Squnion>i. Y i)  .  c))  .  c =
         (\<Squnion>i. Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i  .  c)))  .  c"
          proof - 
            fix c
            assume a2: "c \<in> ubDom\<cdot>(Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>((\<Squnion>i::nat. Y i)  .  c)))"
            then have a3: "c \<in> ubDom\<cdot>(Lub Y)"
              using tsynbremdups_ubundle_ubdom by auto
            have f2: "tsynRemDups\<cdot>(Lub Y  .  c) = (\<Squnion>i::nat. tsynRemDups\<cdot>(Y i  .  c))"
              by (simp add: contlub_cfun_arg a1)
            have f3: "\<And>i::nat. ubWell (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i  .  c))"
              proof -
                fix i :: nat
                have "\<exists>n. ubWell (\<lambda>c. (c \<in> ubDom\<cdot>(Y n))\<leadsto>tsynRemDups\<cdot>(Y i . c))"
                  using tsynbremdups_ubwell by blast
                then show "ubWell (\<lambda>c. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i . c))"
                  using a1 by auto
              qed
              have f4: "tsynRemDups\<cdot>(Lub Y  .  c) = ((\<Squnion>i::nat. (Rep_ubundle (Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i  .  c)))))\<rightharpoonup>c)"
                using a2 a3 f2 f3 lub_eq option.inject tsynbremdups_chain tsynbremdups_lub_dom ubdom_lub_eq ubgetchE ubgetch_insert ubgetch_lub ubrep_lub ubrep_ubabs
                by smt
            have f5: "tsynRemDups\<cdot>(Lub Y  .  c) = (\<Squnion>i::nat. Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i  .  c)))  .  c"
              by (metis (no_types, lifting) lub_eq f4 tsynbremdups_chain ubgetch_insert ubrep_lub)
            have f6: "tsynRemDups\<cdot>(Lub Y  .  c) = Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>((\<Squnion>i::nat. Y i)  .  c))  .  c"
              by (simp add: a3 ubgetch_insert)
            show "Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>((\<Squnion>i::nat. Y i)  .  c))  .  c =
                  (\<Squnion>i::nat. Abs_ubundle (\<lambda>c::channel. (c \<in> ubDom\<cdot>(Lub Y))\<leadsto>tsynRemDups\<cdot>(Y i  .  c)))  .  c"
              using f5 f6 by auto
          qed
      qed
    then show  "Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(\<Squnion>i. Y i))\<leadsto>tsynRemDups\<cdot>((\<Squnion>i. Y i)  .  c)) \<sqsubseteq> (\<Squnion>i. Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>(\<Squnion>j. Y j))\<leadsto>tsynRemDups\<cdot>(Y i  .  c)))"
      by simp
  qed

text {* @{term tsynbRemDups} insertion lemma. *}
lemma tsynbremdups_insert: 
  "tsynbRemDups\<cdot>sb = Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c)))"
  by (simp add: tsynbRemDups_def)

text {* @{term tsynbAbs} get channel lemma. *}
lemma tsynbremdups_ubgetch: 
  assumes "c \<in> ubDom\<cdot>sb"
  shows "(tsynbRemDups\<cdot>sb) . c = tsynRemDups\<cdot>(sb . c)"
  by (simp add: assms tsynbremdups_insert ubgetch_ubrep_eq)

text {* @{term tsynbRemDups} is strict.*}
lemma tsynbremdups_strict [simp]: "tsynbRemDups\<cdot>(ubLeast {c}) = ubLeast {c}"
  apply(simp add: tsynbremdups_insert)
  apply(simp add: ubLeast_def)
  by (metis (no_types, hide_lams) singletonI tsynremdups_strict ubleast_ubgetch)

end