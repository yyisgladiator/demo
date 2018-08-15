(*  Title:        tsynBundle.thy
    Author:       Dennis Slotboom
    E-Mail:       dennis.slotboom@rwth-aachen.de

    Description:  Time-synchronous stream bundles.
*)

chapter {* Time-Synchronous Stream Bundles *}

theory tsynBundle
imports tsynStream "../untimed/SB" "../UFun_Templates" "../untimed/SpfStep" 
        "../UBundle_Induction"

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

text {* @{term tsynbAbs}: Filter the nulls on each stream of the ubundle. *}
definition tsynbAbs :: "'a tsyn stream ubundle \<rightarrow> 'a stream ubundle" where 
  "tsynbAbs \<equiv> \<Lambda> sb. Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> tsynAbs\<cdot>(sb . c))"

text {* @{term tsynbRemDups}: Removes all duplicates on each stream of the ubundle. *}
definition tsynbRemDups :: "'a tsyn stream ubundle \<rightarrow> 'a tsyn stream ubundle" where 
  "tsynbRemDups \<equiv> \<Lambda> sb. Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> tsynRemDups\<cdot>(sb . c))"

(* ----------------------------------------------------------------------- *)
  section {* Definitions of Time-Synchronous Test Bundles *}
(* ----------------------------------------------------------------------- *)

(* ToDo: add tsynbRemDups test. *)

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
lemma tsynabs_sdom_sub_ctype: assumes "sdom\<cdot>s \<subseteq> ctype c" shows "sdom\<cdot>(tsynAbs\<cdot>s) \<subseteq> ctype c"
  using assms
  apply (induction s rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (metis (no_types, lifting) ch2ch_Rep_cfunR contlub_cfun_arg l44 sdom_chain2lub subset_trans)
  apply (simp_all add: tsynabs_sconc_msg tsynabs_sconc_null)
  using ctype_tsyn_iff by auto

text {* @{term tsynbAbs} ubundle is ubwell. *}   
lemma tsynbabs_ubwell [simp]: "ubWell (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> (tsynAbs\<cdot>(sb . c)))"
  by (simp add: tsynabs_sdom_sub_ctype)

text {* Domain of the @{term tsynbAbs} output bundle is the same as the input bundle domain. *}    
lemma tsynbabs_ubundle_ubdom:
  "ubDom\<cdot>(Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>sb) \<leadsto> tsynAbs\<cdot>(sb . c))) = ubDom\<cdot>sb"
  by (simp add: ubdom_ubrep_eq)

(* ToDo: remove smt. *)

text {* @{term tsynbAbs} is continous. *}  
lemma tsynbabs_cont [simp]: "cont (\<lambda> sb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynAbs\<cdot>(sb . c))))"
  apply (rule cont_Abs_UB, simp_all)
  apply (rule contI2)
  apply (rule monofunI)
  apply (simp add: below_option_def fun_below_iff monofun_cfun_arg ubdom_below)
  apply (simp, rule+)
  apply (simp only: fun_below_iff)
  by (smt contlub_cfun_arg contlub_lambda is_ub_thelub lub_eq monofun_cfun_arg not_below2not_eq 
      po_class.chain_def some_below some_lub_chain_eq)

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
lemma tsynremdups_h_sdom_sub_ctype: assumes "sdom\<cdot>s \<subseteq> ctype c" 
  shows "sdom\<cdot>((sscanlA tsynRemDups_h state)\<cdot>s) \<subseteq> ctype c"
  using assms
  apply (induction s arbitrary: state rule: tsyn_ind, simp_all)
  apply (rule admI)
  apply (metis (no_types, lifting) ch2ch_Rep_cfunR contlub_cfun_arg l44 sdom_chain2lub subset_trans)
  by (simp add: ctype_tsyn_def)

text {* @{term tsynRemDups} channel is usclOkay. *}
lemma tsynremdups_sdom_sub_ctype: assumes "sdom\<cdot>s \<subseteq> ctype c" shows "sdom\<cdot>(tsynRemDups\<cdot>s) \<subseteq> ctype c"
  by (simp add: assms tsynremdups_insert tsynremdups_h_sdom_sub_ctype)

text {* @{term tsynbRemDups} ubundle is ubwell. *}   
lemma tsynbremdups_ubwell [simp]: "ubWell (\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c)))"
  by (simp add: tsynremdups_sdom_sub_ctype)

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

(* ToDo: remove smt. *)

text {* @{term tsynbRemDups} is continous. *}
lemma tsynbremdups_cont [simp]: "cont (\<lambda>sb. Abs_ubundle(\<lambda>c. (c\<in>ubDom\<cdot>sb) \<leadsto> (tsynRemDups\<cdot>(sb . c))))"
  apply (rule cont_Abs_UB, simp_all)
  apply (rule contI2)
  apply (rule monofunI)
  apply (simp add: below_option_def fun_below_iff monofun_cfun_arg ubdom_below)
  apply (simp, rule+)
  apply (simp only: fun_below_iff)
  by (smt contlub_cfun_arg contlub_lambda is_ub_thelub lub_eq monofun_cfun_arg not_below2not_eq 
      po_class.chain_def some_below some_lub_chain_eq)

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

(* ----------------------------------------------------------------------- *)
  subsection {* tsynbCases *}
(* ----------------------------------------------------------------------- *)

text {* If the max len of the ubundle is one and none of the channel is empty then the len of every 
        channel is one. *}
lemma ubundle_ubgetch_uscllen_one:
  assumes "ubMaxLen (Fin (1 :: nat)) x"
    and "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow> x . c \<noteq> \<epsilon>"
  shows  "\<And>c. c \<in> ubDom\<cdot>x \<Longrightarrow> usclLen\<cdot>(x . c) = Fin 1"
  proof -
    have x_leq_one: "\<And>c. c\<in>ubDom\<cdot>x \<Longrightarrow> usclLen\<cdot>(x . c) \<le> Fin 1" 
      using assms ubMaxLen_def by auto
    have eps_len_zero: "usclLen\<cdot>\<epsilon> = Fin 0"
      by (simp add: usclLen_stream_def)
    hence x_not_zero: "\<And>c. c\<in>ubDom\<cdot>x \<Longrightarrow> usclLen\<cdot>(x . c) \<noteq> Fin 0" 
      using usclLen_zero assms by auto
    show "\<And>c::channel. c \<in> ubDom\<cdot>x \<Longrightarrow> usclLen\<cdot>(x  .  c) = Fin (1::nat)"
      using neq02Suclnle x_leq_one x_not_zero by fastforce
  qed

text {* Cases rule for simple time-synchronous bundles. *}
lemma tsynb_cases [case_names max_len not_ubleast numb_channel msg null]:
  assumes max_len: "ubMaxLen (Fin (1 :: nat)) x" 
    and not_ubleast: "x \<noteq> ubLeast (ubDom\<cdot>x)"
    and numb_channel: "(ubDom\<cdot>x) = {c}"
    and msg: "\<And>m. (Msg m) \<in> ctype c \<Longrightarrow> P (createBundle (Msg m) c)"
    and null: "P (tsynbNull c)"
  shows "P x"
  proof -
    have x_not_empty: "x . c \<noteq> \<epsilon>"
      by (metis not_ubleast numb_channel singletonD ubgetchI ubleast_ubdom ubleast_ubgetch)
    have x_dom_eq_createbundle: "\<And>m. ubDom\<cdot>x = ubDom\<cdot>(createBundle (Msg m) c)" 
      by (simp add: numb_channel)
    have x_dom_eq_tsynbnull: "ubDom\<cdot>x = ubDom\<cdot>(tsynbNull c)" 
      by (simp add: numb_channel)
    have createbundle_stream_eq: 
      "\<And>m. (Msg m) \<in> ctype c \<Longrightarrow> (createBundle (Msg m) c) . c = \<up>(Msg m)" 
      by (metis createBundle.rep_eq fun_upd_same option.sel ubgetch_insert) 
    have tsynbnull_stream_eq: "(tsynbNull c) . c =  \<up>null"
      by simp
    have x_singleton: "usclLen\<cdot>(x . c) = Fin 1"
      using ubundle_ubgetch_uscllen_one max_len numb_channel x_not_empty by fastforce
    obtain s where s_def: "x . c = s"
      by simp
    have s_ubundle_eq_x: "x = Abs_ubundle ([c \<mapsto> s])"
      by (metis dom_eq_singleton_conv fun_upd_same numb_channel s_def singletonI ubabs_ubrep 
          ubdom_insert ubgetchE)
    have len_one_s_cases: "usclLen\<cdot>s = Fin 1 \<Longrightarrow> (\<exists>m. s = (\<up>(Msg m))) \<or> (s = (\<up>null))"
      by (metis len_one_stream tsyn.exhaust usclLen_stream_def)
    have s_cases: "(\<exists>m. s = \<up>(Msg m)) \<or> (s = \<up>null)"
      using s_def assms x_singleton x_not_empty len_one_s_cases by blast
    have s_bundle_scases: "(\<exists>m. s = (createBundle (Msg m) c) . c) \<or> (s = (tsynbNull c) . c)"
      proof (case_tac "\<exists>m. s = \<up>(Msg m)")
        assume m_exists: "\<exists>m. s = \<up>(\<M> m)"
        then show "(\<exists>m. s = createBundle (\<M> m) c  .  c) \<or> s = tsynbNull c  .  c"          
          by (metis contra_subsetD createbundle_stream_eq insertI1 insert_is_Un lscons_conv 
              numb_channel s_def sdom2un sup'_def ubdom_channel_usokay ubgetch_insert 
              usclOkay_stream_def)
      next
        assume m_nexists: "\<nexists>m::'a. s = \<up>(\<M> m)"
        then show "(\<exists>m::'a. s = createBundle (\<M> m) c  .  c) \<or> s = tsynbNull c  .  c" 
          using s_cases by auto
      qed
    have x_bundle_cases: "(\<exists>m. x = (createBundle (Msg m) c)) \<or> (x = (tsynbNull c))" 
      by (metis numb_channel s_def s_bundle_scases singletonD ubgetchI x_dom_eq_createbundle 
          x_dom_eq_tsynbnull)
    show ?thesis 
      by (metis createBundle.rep_eq fun_upd_same msg null option.sel ubgetch_insert x_bundle_cases 
          x_not_empty)
  qed

text {* Equality of two-channel stream ubundles with its Abs_ubundle counterpart *}
lemma absubundle_ubmaxlen: assumes "ubDom\<cdot>x = {c,cc}"
and "x . c = s1"
and "x . cc = s2"
shows "x = Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2]" 
proof-
  obtain s1 where s1_def: "x . c = s1" using assms
   by metis
  obtain s2 where s2_def: "x . cc = s2" using assms
    by metis
  have dom_eq: "ubDom\<cdot>x = ubDom\<cdot>(Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2]))"
        by (metis (mono_tags, lifting) dom_empty dom_fun_upd insertI1 insert_commute option.discI 
           s1_def s2_def assms(1) ubWell_single_channel ubdom_channel_usokay ubdom_insert 
           ubgetch_insert ubrep_ubabs ubsetch_well)
  hence "\<And>ccc. ccc\<in>ubDom\<cdot>x \<Longrightarrow> x . ccc = (Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2])) . ccc"
  proof- 
    have x_eq_absubundle_cc: "x . cc = (Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2])) . cc" 
      by (metis (mono_tags, lifting) fun_upd_same insertI1 insert_commute s1_def s2_def assms(1) 
          ubWell_single_channel ubdom_channel_usokay ubgetchE ubgetch_insert ubrep_ubabs ubsetch_well)
    have x_c: "(Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2])) . c = s1" 
      by (metis fun_upd_same fun_upd_twist insert_iff s1_def s2_def assms(1)  ubWell_single_channel 
          ubdom_channel_usokay ubgetchE ubgetch_insert ubrep_ubabs ubsetch_well)
    have x_eq_absubundle_c: "x . c = (Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2])) . c"
      by (simp add: s1_def x_c x_eq_absubundle_cc) 
    show "\<And>ccc::channel. ccc \<in> ubDom\<cdot>x \<Longrightarrow> ubDom\<cdot>x = ubDom\<cdot>(Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2]) \<Longrightarrow> 
                          x . ccc = Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2] . ccc"
    using x_eq_absubundle_c x_eq_absubundle_cc assms(1) by fastforce
    qed
  thus ?thesis using ubgetchI dom_eq assms(2) assms(3) s1_def s2_def by blast
qed

text {* Equality of two-channel stream ubundles with createBundle and ubUnion *}
lemma createbundle_ubunion: assumes two_channel: "ubDom\<cdot>x = {c,cc}"
and max_len_2c: "ubMaxLen (Fin (1::nat)) x"
and not_ubleast_2c: "\<And>c. c\<in>ubDom\<cdot>x \<Longrightarrow> x . c \<noteq> ubLeast (ubDom\<cdot>x) . c"  
and xc_eq: "x . c = \<up>m1"
and xcc_eq: "x . cc = \<up>m2"
shows "x = ((createBundle m1 c) \<uplus> (createBundle m2 cc))"
proof -
  obtain m1 where m1_def: "x . c = \<up>m1" using xc_eq  by blast
  obtain m2 where m2_def: "x . cc = \<up>m2" using xcc_eq by blast
  have x_dom_eq: "ubDom\<cdot>x = ubDom\<cdot>((createBundle m1 c) \<uplus> (createBundle m2 cc))"
    by (metis createBundle_dom insert_is_Un two_channel ubclDom_ubundle_def ubclunion_ubcldom)
  have m1_shd: "m1 = shd (x . c)" 
    using m1_def by auto
  have m1_ctype: "m1 \<in> ctype c"
    by (metis (no_types, lifting) UnI1 contra_subsetD insertI1 m1_shd not_ubleast_2c sdom2un 
        surj_scons two_channel ubdom_channel_usokay ubgetch_insert ubleast_ubgetch usclOkay_stream_def)
  have m2_shd: "m2 = shd (x . cc)" 
    using m2_def by auto
  have m2_ctype: "m2 \<in> ctype cc"
    by (metis contra_subsetD insertI1 insert_commute insert_is_Un lscons_conv m2_def sdom2un 
        sup'_def two_channel ubdom_channel_usokay ubgetch_insert usclOkay_stream_def)
  have create_c: "(createBundle m1 c) . c = \<up>m1"
    by (metis createBundle.rep_eq fun_upd_same m1_ctype option.sel ubgetch_insert)
  have create_cc: "(createBundle m2 cc) . cc = \<up>m2"
    by (metis createBundle.rep_eq fun_upd_same m2_ctype option.sel ubgetch_insert)
  have ubunion_create_eq_c: "((createBundle m1 c) \<uplus> (createBundle m2 cc)) . c = \<up>m1"
    by (metis createBundle_dom create_c create_cc m1_def m2_def singletonD ubclUnion_ubundle_def 
        ubunion_getchL ubunion_getchR)
  have ubunion_create_eq_cc: "((createBundle m1 c) \<uplus> (createBundle m2 cc)) . cc = \<up>m2"
    using ubunion_getchR by (simp add: create_cc ubclUnion_ubundle_def)
  thus ?thesis 
    by (metis shd1 xc_eq xcc_eq ubunion_create_eq_c ubunion_create_eq_cc insert_iff m1_def m2_def 
        singletonD two_channel ubgetchI x_dom_eq )
qed

lemma createbundle_tsynbnull: "createBundle - c = tsynbNull c"
  by (metis contra_subsetD createBundle_apply insertI1 insert_is_Un lscons_conv sdom2un sup'_def 
      tsynbNull.abs_eq tsynbnull_ubdom tsynbnull_ubgetch ubdom_channel_usokay ubgetch_insert usclOkay_stream_def)

text {* Cases rule for simple time-synchronous bundles with two non-empty channels. *}
lemma tsynb_cases_ext [case_names max_len_2c not_ubleast_2c two_channel msg_msg null_msg msg_null null_null]:
  assumes max_len_2c: "ubMaxLen (Fin (1::nat)) x" 
    and not_ubleast_2c: "\<And>c. c\<in>ubDom\<cdot>x \<Longrightarrow> x . c \<noteq> ubLeast (ubDom\<cdot>x) . c" 
    and two_channel: "(ubDom\<cdot>x) = {c,cc}"
    and msg_msg: "\<And>m1 m2. (Msg m1) \<in> ctype c \<Longrightarrow> (Msg m2) \<in> ctype cc \<Longrightarrow> 
                           P ((createBundle (Msg m1) c) \<uplus> (createBundle (Msg m2) cc))"
    and null_msg: "\<And>m2. (Msg m2) \<in> ctype cc \<Longrightarrow> P ((tsynbNull c) \<uplus> (createBundle (Msg m2) cc))"
    and msg_null: "\<And>m2. (Msg m2) \<in> ctype c \<Longrightarrow> P ((createBundle (Msg m2) c) \<uplus> (tsynbNull cc))"
    and null_null: "P ((tsynbNull c) \<uplus> (tsynbNull cc))"
  shows "P x"
proof- 
  have x_c_not_empty: "x . c \<noteq> \<epsilon>"
    using not_ubleast_2c by (simp add: two_channel)
  have x_cc_not_empty: "x . cc \<noteq> \<epsilon>" 
    using not_ubleast_2c by (simp add: two_channel)
  have x_c_singleton: "usclLen\<cdot>(x . c) = Fin 1" 
    using max_len_2c not_ubleast_2c two_channel ubundle_ubgetch_uscllen_one by fastforce
  have x_cc_singleton: "usclLen\<cdot>(x . cc) = Fin 1" 
    using max_len_2c not_ubleast_2c two_channel ubundle_ubgetch_uscllen_one by fastforce
  have x_dom_eq_msg_msg: "\<And>m1 m2. ubDom\<cdot>x = ubDom\<cdot>((createBundle (Msg m1) c) \<uplus> (createBundle (Msg m2) cc))"
    by (metis createBundle_dom insert_is_Un two_channel ubclDom_ubundle_def ubclunion_ubcldom)
  have x_dom_eq_null_msg: "\<And>m2. ubDom\<cdot>x = ubDom\<cdot> ((tsynbNull c) \<uplus> (createBundle (Msg m2) cc))"
    by (metis createBundle_dom insert_is_Un tsynbnull_ubdom two_channel ubclDom_ubundle_def ubclunion_ubcldom)
  have x_dom_eq_msg_null: "\<And>m2. ubDom\<cdot>x = ubDom\<cdot> ((createBundle (Msg m2) c)  \<uplus> (tsynbNull cc))"
    by (metis createBundle_dom insert_is_Un tsynbnull_ubdom two_channel ubclDom_ubundle_def ubclunion_ubcldom)
  have x_dom_eq_null_null: "ubDom\<cdot>x = ubDom\<cdot> ((tsynbNull c)  \<uplus> (tsynbNull cc))"
    by (metis insert_is_Un tsynbnull_ubdom two_channel ubclDom_ubundle_def ubclunion_ubcldom)
  obtain s1 where s1_def: "x . c = s1" using assms
   by metis
  obtain s2 where s2_def: "x . cc = s2" using assms
    by metis
  have s1_ubundle_eq_x: "x = Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2])"
    using absubundle_ubmaxlen s1_def s2_def assms by blast
  have len_one_cases_c: "usclLen\<cdot>s1 = Fin 1 \<Longrightarrow> (\<exists>m. s1 = (\<up>(Msg m))) \<or>  (s1 = (\<up>null))" 
    using One_nat_def len_one_stream tsyn.exhaust usclLen_stream_def by metis 
  have len_one_cases_cc: "usclLen\<cdot>s2 = Fin 1 \<Longrightarrow> (\<exists>m. s2 = (\<up>(Msg m))) \<or>  (s2 = (\<up>null))" 
    using One_nat_def len_one_stream tsyn.exhaust usclLen_stream_def by metis 
  have s1_cases: "(\<exists>m. s1 = \<up>(Msg m)) \<or> (s1 = \<up>null)"
    using s1_def assms x_c_singleton x_c_not_empty len_one_cases_c by blast
  have s2_cases: "(\<exists>m. s2 = \<up>(Msg m)) \<or> (s2 = \<up>null)"
    using s2_def assms x_cc_singleton x_cc_not_empty len_one_cases_cc by blast
  have s1_eq: "(\<exists>m. s1 = (createBundle (Msg m) c) . c ) \<or> (s1 = (tsynbNull c) . c)" 
    proof(case_tac "\<exists>m. s1 = \<up>(Msg m)")
      show "\<exists>m::'a. s1 = \<up>(\<M> m) \<Longrightarrow> (\<exists>m::'a. s1 = createBundle (\<M> m) c  .  c) \<or> s1 = tsynbNull c . c"
        by (metis contra_subsetD createBundle.rep_eq fun_upd_same insertI1 insert_is_Un lscons_conv 
           option.sel s1_def sdom2un sup'_def two_channel ubdom_channel_usokay ubgetch_insert 
           usclOkay_stream_def)
      show "\<nexists>m::'a. s1 = \<up>(\<M> m) \<Longrightarrow> (\<exists>m::'a. s1 = createBundle (\<M> m) c  .  c) \<or> s1 = tsynbNull c . c" 
        using s1_cases by auto
    qed
  have s2_eq: "(\<exists>m. s2 = (createBundle (Msg m) cc) . cc ) \<or> (s2 = (tsynbNull cc) . cc)" 
    proof(case_tac "\<exists>m. s2 = \<up>(Msg m)")
      show "\<exists>m::'a. s2 = \<up>(\<M> m) \<Longrightarrow> (\<exists>m::'a. s2 = createBundle (\<M> m) cc  .  cc) \<or> s2 = tsynbNull cc . cc"
        by (metis contra_subsetD createBundle.rep_eq fun_upd_same insertI1 insert_is_Un lscons_conv 
           option.sel s2_def sdom2un sup'_def two_channel ubdom_channel_usokay ubgetch_insert 
           usclOkay_stream_def insert_commute)
      show "\<nexists>m::'a. s2 = \<up>(\<M> m) \<Longrightarrow> (\<exists>m::'a. s2 = createBundle (\<M> m) cc  .  cc) \<or> s2 = tsynbNull cc . cc" 
        using s2_cases by auto
    qed
  have x_cases: "(\<exists>m1 m2. x = Abs_ubundle ([c \<mapsto> \<up>(Msg m1), cc \<mapsto> \<up>(Msg m2)])) \<or> 
                 (\<exists>m1. x = Abs_ubundle ([c \<mapsto> \<up>(Msg m1), cc \<mapsto> \<up>-])) \<or> 
                 (\<exists>m2. x = Abs_ubundle ([c \<mapsto> \<up>-, cc \<mapsto> \<up>(Msg m2)])) \<or>
                 (x = Abs_ubundle ([c \<mapsto> \<up>-, cc \<mapsto> \<up>-]))" 
    using s1_eq s2_eq s1_cases s2_cases s1_def s2_def s1_ubundle_eq_x by metis
  have x_case_msg_msg: "\<exists>m1. s1 = \<up>(Msg m1) \<Longrightarrow> \<exists>m2.  s2 = \<up>(Msg m2) \<Longrightarrow> 
                        \<exists>m1 m2. x =  ((createBundle (Msg m1) c) \<uplus> (createBundle (Msg m2) cc))" 
    using createbundle_ubunion max_len_2c not_ubleast_2c s1_def s2_def two_channel by blast
  have x_case_null_null: "s1 = \<up>-  \<Longrightarrow>  s2 = \<up>- \<Longrightarrow> x = ((tsynbNull c) \<uplus> (tsynbNull cc))"
  proof- 
    have null_null: "s1 = \<up>-  \<Longrightarrow>  s2 = \<up>- \<Longrightarrow> x = ((createBundle - c) \<uplus> (createBundle - cc))"
      using createbundle_ubunion max_len_2c not_ubleast_2c s1_def s2_def two_channel by blast
    have create2tsynb: "x = ((createBundle - c) \<uplus> (createBundle - cc)) \<Longrightarrow> x = ((tsynbNull c) \<uplus> (tsynbNull cc))"
      by (simp add: createbundle_tsynbnull)
    show "s1 = \<up>-  \<Longrightarrow>  s2 = \<up>- \<Longrightarrow> x = ((tsynbNull c) \<uplus> (tsynbNull cc))" 
      using null_null create2tsynb by blast
  qed
  have x_case_msg_null: "\<exists>m1. s1 = \<up>(Msg m1) \<Longrightarrow> s2 = \<up>- \<Longrightarrow> 
                          \<exists>m1 . x =  ((createBundle (Msg m1) c) \<uplus> (tsynbNull cc))"
  proof-
    have msg_null: "\<exists>m1. s1 = \<up>(Msg m1) \<Longrightarrow> s2 = \<up>- \<Longrightarrow> 
                    \<exists>m1 . x =  ((createBundle (Msg m1) c) \<uplus> (createBundle - cc))"
      using createbundle_ubunion max_len_2c not_ubleast_2c s1_def s2_def two_channel by blast
    have create2tsynb: "\<exists>m1. x = ((createBundle (Msg m1) c) \<uplus> (createBundle - cc)) \<Longrightarrow> 
                        \<exists>m1. x =  ((createBundle (Msg m1) c) \<uplus> (tsynbNull cc))"
      by (simp add: createbundle_tsynbnull)
    show "\<exists>m1. s1 = \<up>(Msg m1) \<Longrightarrow> s2 = \<up>- \<Longrightarrow> 
                          \<exists>m1 . x =  ((createBundle (Msg m1) c) \<uplus> (tsynbNull cc))" 
      using msg_null create2tsynb by blast
  qed
  have x_case_null_msg:  "s1 = \<up>- \<Longrightarrow> \<exists>m2.  s2 = \<up>(Msg m2) \<Longrightarrow> 
                          \<exists>m2. x =  ((tsynbNull c) \<uplus> (createBundle (Msg m2) cc))"
  proof-
    have msg_null: "s1 = \<up>- \<Longrightarrow> \<exists>m2.  s2 = \<up>(Msg m2) \<Longrightarrow> 
                          \<exists>m2. x =  ((createBundle - c) \<uplus> (createBundle (Msg m2) cc))"
      using createbundle_ubunion max_len_2c not_ubleast_2c s1_def s2_def two_channel by blast
    have create2tsynb: "\<exists>m2. x = ((createBundle - c) \<uplus> (createBundle (Msg m2) cc)) \<Longrightarrow> 
                        \<exists>m2. x =  ((tsynbNull c) \<uplus> (createBundle (Msg m2) cc))"
      by (simp add: createbundle_tsynbnull)
    show "s1 = \<up>- \<Longrightarrow> \<exists>m2.  s2 = \<up>(Msg m2) \<Longrightarrow> 
                      \<exists>m2. x =  ((tsynbNull c) \<uplus> (createBundle (Msg m2) cc))" 
      using msg_null create2tsynb by blast
  qed
  have px: "P (Abs_ubundle ([c \<mapsto> s1, cc \<mapsto> s2]))"
    proof(case_tac "\<exists>m1. s1 = \<up>(\<M> m1)")
      show "\<exists>m1. s1 = \<up>(\<M> m1) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])"
        proof(case_tac "\<exists>m2. s2 = \<up>(\<M> m2)")
          show "\<exists>m1. s1 = \<up>(\<M> m1) \<Longrightarrow> \<exists>m2. s2 = \<up>(\<M> m2) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])" 
            proof- 
              assume a0: "\<exists>m1. s1 = \<up>(\<M> m1)"
              assume a1: " \<exists>m2. s2 = \<up>(\<M> m2)" 
              show " P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])"
                proof -
                  obtain m1 where m1_def: "s1 = \<up>(\<M> m1)" using a0 by blast
                  obtain m2 where m2_def: "s2 = \<up>(\<M> m2)" using a1 by blast
                  have pcreate: "P (((createBundle (\<M> m1) c) \<uplus> (createBundle (\<M> m2) cc)))"
                    by (metis createBundle.rep_eq fun_upd_same inject_scons m1_def m2_def msg_msg 
                       option.sel s1_def s1_eq s2_def s2_eq tsyn.distinct(1) tsynbnull_ubgetch 
                       ubgetch_insert x_c_not_empty x_cc_not_empty)
                  have f2: "x = ((createBundle (\<M> m1) c) \<uplus> (createBundle (\<M> m2) cc))"
                    using createbundle_ubunion m1_def m2_def max_len_2c not_ubleast_2c s1_def s2_def two_channel by blast
                thus ?thesis
                  using pcreate s1_ubundle_eq_x by auto
              qed
           qed
           show "\<exists>m1::'a. s1 = \<up>(\<M> m1) \<Longrightarrow> \<nexists>m2::'a. s2 = \<up>(\<M> m2) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])" 
             by (metis createBundle.rep_eq fun_upd_same msg_null option.sel s1_def s1_ubundle_eq_x 
                 s2_cases s2_def singletonD tsynbnull_ubdom ubclUnion_ubundle_def ubgetch_insert 
                 ubunion_getchL x_c_not_empty x_case_msg_null)
        qed
        show "\<nexists>m1::'a. s1 = \<up>(\<M> m1) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])"
          proof(case_tac "\<exists>m2. s2 = \<up>(Msg m2)")
            show "\<nexists>m1::'a. s1 = \<up>(\<M> m1) \<Longrightarrow> \<exists>m2::'a. s2 = \<up>(\<M> m2) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])"
              by (metis (mono_tags, lifting) createBundle.rep_eq createBundle_dom insertI1 
                  map_upd_Some_unfold null_msg s1_cases s1_ubundle_eq_x ubclUnion_ubundle_def 
                  ubgetchE ubunion_getchR x_case_null_msg x_cc_not_empty)
            show " \<nexists>m1::'a. s1 = \<up>(\<M> m1) \<Longrightarrow> \<nexists>m2::'a. s2 = \<up>(\<M> m2) \<Longrightarrow> P (Abs_ubundle [c \<mapsto> s1, cc \<mapsto> s2])"
              using null_null s1_cases s1_ubundle_eq_x s2_cases x_case_null_null by auto
          qed
        qed
  show ?thesis
    by (simp add: px s1_ubundle_eq_x)
qed

end