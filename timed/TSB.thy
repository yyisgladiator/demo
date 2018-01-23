(*  Title:        TSBTheorie.thy
    Author:       Sebastian Stüber, Jens Christoph Bürger
    e-mail:       sebastian.stueber@rwth-aachen.de,
                  jens.buerger@rwth-aachen.de

    Description:  Definition of "Timed Stream Bundles"
                    in 3 different versions, a general "TSB"
                                             one over infinite TStreams "TSB_inf"
                                             and one over finite TStreams "TSB_fin"
*)


chapter {* Timed Streams *}

theory TSB
imports "../UnivClasses" "../Channel" "../inc/OptionCpo" TStream TStream_JB "../UBundle" "../UBundle_Pcpo"

begin

default_sort message


(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)



(* ----------------------------------------------------------------------- *)
section \<open>Definitions on TSB \<close>
(* ----------------------------------------------------------------------- *)
    

definition TSB :: "channel set \<Rightarrow> ('m tstream\<^sup>\<Omega>) set" where
"TSB cs \<equiv> {b. ubDom\<cdot>b = cs}"


(* returns the first n blocks of the TSB *)
definition tsbTTake :: "nat \<Rightarrow> 'm tstream\<^sup>\<Omega> \<rightarrow> 'm tstream\<^sup>\<Omega>" where
"tsbTTake n \<equiv> \<Lambda> tb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTake n\<cdot>(tb  .  c)))"

abbreviation tsbTTake_abbrv :: "'m tstream\<^sup>\<Omega>  \<Rightarrow> nat \<Rightarrow> 'm tstream\<^sup>\<Omega>" ("_ \<down> _ ")where
"tb \<down> n \<equiv> tsbTTake n\<cdot>tb"


(* defintion with lnat *)
definition tsbTTakeL :: "lnat \<rightarrow> 'm tstream\<^sup>\<Omega> \<rightarrow> 'm tstream\<^sup>\<Omega>" where
"tsbTTakeL \<equiv> \<Lambda> n tb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>n\<cdot>(tb  .  c)))"


abbreviation tsbHd :: "'m tstream\<^sup>\<Omega> \<Rightarrow> 'm tstream\<^sup>\<Omega>" where
"tsbHd \<equiv> (\<lambda>tb. tsbTTake 1\<cdot>tb)"


  (* Deletes the first n Elements of each Stream *)
definition tsbDrop:: "nat \<Rightarrow> 'm tstream\<^sup>\<Omega> \<Rightarrow> 'm tstream\<^sup>\<Omega>" where
"tsbDrop n \<equiv> \<lambda> b. ubMapStream (\<lambda>s. tsDrop n\<cdot>s) b"


  (* Deletes the first Elements of each stream *)
definition tsbRt:: " 'm tstream\<^sup>\<Omega> \<Rightarrow> 'm tstream\<^sup>\<Omega>" where
"tsbRt \<equiv> tsbDrop 1"


  (* Retrieves the n-th element of each Stream *)
definition tsbNth:: "nat \<Rightarrow> 'm tstream\<^sup>\<Omega> \<Rightarrow> 'm tstream\<^sup>\<Omega>" where
"tsbNth n \<equiv> \<lambda> tb.  tsbHd (tsbDrop n tb)"
  

(* ----------------------------------------------------------------------- *)
  subsection \<open>Lemmas on TSB \<close>
(* ----------------------------------------------------------------------- *)


subsubsection \<open>TSB\<close>


lemma tsb_tsbleast [simp]:  "(ubLeast cs) \<in> TSB cs"
  by (simp add: TSB_def)

lemma tsb_exists [simp]: "\<exists>tb. tb\<in>(TSB cs)"
  using tsb_tsbleast by blast

lemma [simp]: assumes "tb\<in>(TSB cs)" shows "ubDom\<cdot>tb = cs"
  using TSB_def assms by auto


subsubsection \<open>tsbTTake\<close>

  
abbreviation tsbTTake_abbr :: "nat \<Rightarrow> 'm tstream\<^sup>\<Omega> \<Rightarrow> 'm tstream\<^sup>\<Omega>" where
"tsbTTake_abbr n tb \<equiv> Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>tb)\<leadsto>tb  .  c \<down> n )"

(* DO NOT USE THIS, just for internal reasoning *)
definition tsbTTake_abbr_fun :: "nat \<Rightarrow> 'm tstream\<^sup>\<Omega> \<Rightarrow> 'm tstream\<^sup>\<Omega>" where
"tsbTTake_abbr_fun n tb \<equiv> Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot>tb)\<leadsto>tb  .  c \<down> n )"

lemma tsbTTake_well [simp]: "ubWell (\<lambda>c. (c \<in> ubDom\<cdot>tb)\<leadsto> ((tb  .  c) \<down> n ))"
  apply (simp add: ubWell_def usclOkay_tstream_def)
  by (metis (no_types, lifting) dual_order.trans tsttake_dom ubdom_channel_usokay ubgetch_insert usclOkay_tstream_def)
                       
lemma tsbttake_abbr_dom [simp]: "ubDom\<cdot>(tsbTTake_abbr i tb) = ubDom\<cdot>tb"
proof -
  have "\<And>f. \<not> ubWell f \<or> dom f = UBundle.ubDom\<cdot>(Abs_ubundle f::'a tstream\<^sup>\<Omega>)"
    by (metis ubdom_insert ubrep_ubabs)
  then have "\<not> ubWell (\<lambda>c. (c \<in> UBundle.ubDom\<cdot> tb)\<leadsto>tb . c \<down> i ) \<or> UBundle.ubDom\<cdot>(tsbTTake_abbr i tb) = UBundle.ubDom\<cdot>tb"
    by fastforce
  then show ?thesis
    using tsbTTake_well by blast
qed

lemma tsbttake_abb_getchInsert: assumes "c \<in> ubDom\<cdot>tb"
  shows "((tsbTTake_abbr n tb)  .  c) = ((tb  .  c) \<down>n)"
  by(simp add: ubgetch_insert assms)
  
lemma tsbttake_mono [simp]: "monofun  (\<lambda> tb. tsbTTake_abbr n tb)"
   apply (rule monofunI)
  apply (rule ub_below)
   apply (simp only: tsbttake_abbr_dom, simp add: ubdom_below)
  apply (subst tsbttake_abb_getchInsert, simp)
    apply (subst tsbttake_abb_getchInsert, simp only: tsbttake_abbr_dom, simp add: ubdom_below)
  by (simp add: monofun_cfun_arg monofun_cfun_fun) 
    
lemma tsbTTake_abb2fun: "tsbTTake_abbr n tb =  tsbTTake_abbr_fun n tb"
  by (simp add: tsbTTake_abbr_fun_def)
    
lemma tsbTTake_abb2funE: "tsbTTake_abbr_fun n tb = tsbTTake_abbr n tb"
  by (simp add: tsbTTake_abbr_fun_def)
    
lemma tsbTTake_abbr_fun_mono [simp]: "monofun (tsbTTake_abbr_fun n)"
proof -
  have "monofun (tsbTTake_abbr n)"
    by simp
  thus ?thesis
    by (simp add: tsbTTake_abb2fun)
qed
    
lemma tsbttake_cont_pre: assumes "chain Y"
  shows "tsbTTake_abbr n (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. tsbTTake_abbr n (Y i))"
proof -
  have f1: "ubDom\<cdot>(tsbTTake_abbr_fun n (Lub Y)) = ubDom\<cdot>(\<Squnion>i. tsbTTake_abbr_fun n (Y i))"
  proof -
    have "\<forall>n. chain (\<lambda>na. tsbTTake_abbr_fun n (Y na))"
      using assms ch2ch_monofun tsbTTake_abbr_fun_mono by blast
    then show "ubDom\<cdot>(tsbTTake_abbr_fun n (Lub Y)) = ubDom\<cdot>(\<Squnion>na. tsbTTake_abbr_fun n (Y na))"
      by (metis (no_types) assms test34 tsbTTake_abb2fun ubdom_below ubdom_insert tsbttake_abbr_dom)
  qed
  have f11: "chain (\<lambda> i. tsbTTake_abbr n (Y i))"
    by (subst tsbTTake_abb2fun, simp add: assms ch2ch_monofun)
  have f2: "\<And> i tb. ubDom\<cdot>(tsbTTake_abbr_fun  i tb) = ubDom\<cdot>tb"
    by (subst tsbTTake_abb2funE, simp)
  have f3: "\<And>c. c \<in> ubDom\<cdot>(Lub Y) \<Longrightarrow> (\<Squnion>i. tsbTTake_abbr_fun n (Y i)) . c = (\<Squnion>i. tsbTTake_abbr_fun n (Y i) .  c)"
    using f11 contlub_cfun_arg
  proof -
    fix c :: channel
    show "(\<Squnion>na. tsbTTake_abbr_fun n (Y na)) . c = (\<Squnion>na. tsbTTake_abbr_fun n (Y na) . c)"
      by (metis (no_types) assms contlub_cfun_arg monofun_def po_class.chain_def tsbTTake_abbr_fun_mono)
  qed
  show ?thesis
    apply (subst (1 2) tsbTTake_abb2fun)
    apply (rule ub_below)
      apply (simp add: f1)
      apply (simp only: f2 f3)
        (* ISAR Proof generateable by sledgehammer
      by (smt assms contlub_cfun_arg lub_eq lub_eval not_below2not_eq theRep_chain tsbChain_dom_eq2 
          tsbTTake_abb2fun tsbgetch_insert tsbttake_abb_getchInsert)*)
    sorry
qed
        
lemma tsbttake_cont [simp]: "cont (\<lambda> tb. tsbTTake_abbr n tb)"
  apply (rule contI2, simp)
  by (rule+, simp only: tsbttake_cont_pre)
    
lemma tsbttake_abbr2def: "tsbTTake_abbr n tb = tsbTTake n\<cdot>tb"
  by (simp add: tsbTTake_def)

lemma tsbttake_dom [simp]: "ubDom\<cdot>(tb \<down> i) = ubDom\<cdot>tb"
  by (simp add: tsbTTake_def ubdom_ubrep_eq)

lemma tsbttake2least: "(tb \<down> 0) = ubLeast (ubDom\<cdot>tb)"
  apply (rule ub_eq)
   apply (simp)
  apply simp
  by (simp add: tsbTTake_def ubgetch_insert)

lemma tsbttake_getch_least [simp]: assumes "c\<in>ubDom\<cdot>tb"
  shows "tb \<down> 0  .  c = \<bottom>"
  by (simp add: tsbttake2least assms)

lemma tsbttake2ttakeI [simp]: assumes "c \<in> ubDom\<cdot>tb"
 shows "((tb \<down> n)  .  c) = ((tb  .  c) \<down>n)"
by (simp add: assms tsbTTake_def ubgetch_insert)

lemma tsbttake_below [simp]: fixes tb:: "'m tstream\<^sup>\<Omega>"
  shows "(tb \<down> i) \<sqsubseteq> tb"
  by (rule ub_below, auto)

lemma tsbttake_lub [simp] : fixes tb:: "'m tstream\<^sup>\<Omega>"
  shows "(\<Squnion>i. (tb \<down> i)) = tb"
  apply (rule ub_eq)
  oops


subsubsection \<open>tsbTTakeL\<close>


lemma tsTakel_lub1_getch_eq: assumes "chain Y" and "c \<in> ubDom\<cdot>tb"
  shows "tsTakeL\<cdot>(Lub Y)\<cdot>(tb  .  c) \<sqsubseteq> (\<Squnion>i::nat. tsTakeL\<cdot>(Y i)\<cdot>(tb  .  c))"
  by (simp add: assms(1) contlub_cfun_arg contlub_cfun_fun)

lemma tsTakel_lub2_getch_eq: assumes "chain Y" and "c \<in> ubDom\<cdot>(Lub Y)"
  shows "tsTakeL\<cdot>n\<cdot>(Lub Y  .  c) \<sqsubseteq> (\<Squnion>i. tsTakeL\<cdot>n\<cdot>(Y i  .  c))"
proof -
    fix c :: channel
    have "(\<Squnion>na. tsTakeL\<cdot>n\<cdot>(Y na . c)) = tsTakeL\<cdot>n\<cdot>(Lub Y . c)"
      by (simp add: assms contlub_cfun_arg contlub_cfun_fun)
    then show "tsTakeL\<cdot>n\<cdot>(Lub Y . c) \<sqsubseteq> (\<Squnion>na. tsTakeL\<cdot>n\<cdot>(Y na . c))"
      by simp
qed


lemma tsbttakeL_well [simp]: "ubWell (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>n\<cdot>(tb  .  c)))"
proof (cases "n \<noteq> \<infinity>")
  case True
  have f1: "n < \<infinity>"
    by (simp add: True less_le)
  obtain j where f2: "n = Fin j"
  by (metis f1 infI neq_iff)
  thus ?thesis
  apply (simp add: ubWell_def tsTakeL_def usclOkay_tstream_def)
    by (metis (no_types, lifting) dual_order.trans tsttake_dom ubdom_channel_usokay ubgetch_insert usclOkay_tstream_def)  
next
  case False
  then show ?thesis
    apply (simp add: ubWell_def tsTakeL_def)
    by (simp add: ubgetch_insert)
  qed

lemma tsbttakeL_dom [simp]: "ubDom\<cdot>(Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>n\<cdot>(tb  .  c)))) = ubDom\<cdot>tb"
  by (simp add: ubdom_ubrep_eq)

lemma tsbttakeL_least: "Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>(Fin 0)\<cdot>(tb  .  c))) = ubLeast (ubDom\<cdot>tb)"
  apply (rule ub_eq, simp_all)
  by (simp add: ubgetch_insert)

lemma tsbttakeL_inf [simp]: "Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>\<infinity>\<cdot>(tb  .  c))) = tb"
  apply (simp only: tstakeL_inf)
  by(simp add: ub_eq)

lemma tsbttakeL_least_getch [simp]: assumes "c \<in> ubDom\<cdot>tb"
  shows "(Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>(Fin 0)\<cdot>(tb  .  c)))) . c = \<bottom>"
  by (simp add: assms tsbttakeL_least)

lemma tsbttakeL_getch [simp]: assumes "c \<in> ubDom\<cdot>tb"
  shows "((Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>n\<cdot>(tb  .  c)))) . c) = tsTakeL\<cdot>n\<cdot>(tb . c)"
proof (cases "n \<noteq> \<infinity>")
  case True
  have f1: "n < \<infinity>"
      by (simp add: True less_le)
  obtain j where f2: "n = Fin j"
  by (metis f1 infI neq_iff)
  then show ?thesis
    by (simp add: tsbTTakeL_def ubgetch_insert assms)
next
  case False
  have f1: "\<And>t. Abs_ubundle (\<lambda>c. (c \<in> ubDom\<cdot> t)\<leadsto>tsTakeL\<cdot>\<infinity>\<cdot> (t . c)) = t"
    apply (simp only: tstakeL_inf)
    by(simp add: ub_eq)
  then show ?thesis
    using False by auto
qed

lemma tsbttakeL_below [simp]: "(Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>n\<cdot>(tb  .  c)))) \<sqsubseteq> tb"
  by (rule ub_below, auto)

lemma tsbttake_mono2 [simp]: "monofun (\<lambda> tb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>n\<cdot>(tb  .  c))))"
  apply (rule monofunI)
  apply (rule ub_below)
   apply (simp only: tsbttakeL_dom, simp add: ubdom_below)
  apply (subst tsbttakeL_getch, simp)
    apply (subst tsbttakeL_getch, simp only: tsbttakeL_dom, simp add: ubdom_below)
  by (simp add: monofun_cfun_arg monofun_cfun_fun)

lemma tsbttake_mono1 [simp]: "\<And> tb. monofun (\<lambda> n. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>n\<cdot>(tb  .  c))))"
  apply (rule monofunI)
  apply (rule ub_below)
   apply (simp add: ubdom_below)
   apply (subst tsbttakeL_getch, simp)
   apply (subst tsbttakeL_getch, simp add: ubdom_below)
  by (simp add: monofun_cfun_arg monofun_cfun_fun)

lemma tsbttake_chain1: assumes "chain Y"
  shows "chain (\<lambda>i::nat. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>(Y i)\<cdot>(tb  .  c))))"
proof -
  have "\<And>i j. i \<sqsubseteq> j \<Longrightarrow> (Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>i\<cdot>(tb  .  c)))) 
                          \<sqsubseteq> Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>j\<cdot>(tb  .  c)))"
      using lnless_def monofunE tsbttake_mono1 by blast
    thus ?thesis
      apply (rule chainI)
      using assms po_class.chainE by blast
  qed

lemma lubgetCh: assumes "chain Y" and "c \<in> ubDom\<cdot>(\<Squnion> i. Y i)"
  shows "(\<Squnion>i. Y i) . c = (\<Squnion>i. (Y i) . c)"
  by (simp add: assms(1) contlub_cfun_arg contlub_cfun_fun)

lemma tsbttake_cont1_pre: assumes "chain Y"
  shows "(Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>(\<Squnion>i. Y i)\<cdot>(tb  .  c)))) 
          \<sqsubseteq> (\<Squnion>i::nat. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>(Y i)\<cdot>(tb  .  c))))"
proof -
  have f1: "\<And>c. c \<in> ubDom\<cdot>tb \<Longrightarrow> (\<Squnion>i. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>(Y i)\<cdot>(tb  .  c)))) . c = (\<Squnion>i. (Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>(Y i)\<cdot>(tb  .  c)))) . c)"
    apply (rule lubgetCh, simp only: tsbttake_chain1 assms)
    using assms tsbttakeL_dom tsbttake_chain1 ubdom_chain_eq2 by blast
  show ?thesis
    apply (rule ub_below)
     apply (subst ubdom_lub, simp_all add: assms)
     apply (simp only: tsbttake_chain1 assms)
       apply (simp add: f1 assms)
       by (simp add: tsTakel_lub1_getch_eq assms)
qed

lemma tsbttake_cont1 [simp]: "\<And>tb. cont (\<lambda> n. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>n\<cdot>(tb  .  c))))"
  apply (rule contI2)
  by (simp_all add: tsbttake_cont1_pre)

(*
abbreviation tsbTTakeL_ab :: "lnat \<Rightarrow> 'm TSB \<Rightarrow> 'm TSB" where
"tsbTTakeL_ab n tb \<equiv>  (\<lambda>c. (c\<in>tsbDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>n\<cdot>(tb  .  c)))\<Omega>"


lemma tmp_tsbttake_chain: assumes "chain Y"
  shows "chain (\<lambda>i. tsbTTakeL_ab n (Y i))"
  sorry
    (* was previously shown as follows 
    apply (simp add: assms ch2ch_monofun) 
    *)
    
lemma tsbttake_cont2_pre: assumes "chain Y"
  shows "tsbTTakeL_ab n (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. tsbTTakeL_ab n (Y i))"
  sorry
    
proof - 
  have f1: "\<And>c. c \<in> tsbDom\<cdot>(Lub Y) \<Longrightarrow> (\<Squnion>i. tsbTTakeL_ab n (Y i)) . c = (\<Squnion>i. tsbTTakeL_ab n (Y i) .  c)" 
    apply (rule lubgetCh) 
     (* apply (simp add: assms ch2ch_monofun) 
     by (metis assms monofunE po_class.chain_def tsbChain_dom_eq2 tsbttakeL_dom tsbttake_mono2) *)
    sorry
  have f2: "\<And> c. c \<in> tsbDom\<cdot>(Lub Y) \<Longrightarrow> (\<Squnion>i. (\<lambda>c. (c \<in> tsbDom\<cdot>(\<Squnion>j. Y j))\<leadsto>tsTakeL\<cdot>n\<cdot>(Y i  .  c))\<Omega>)  .  c  = (\<Squnion>i. tsbTTakeL_ab n (Y i) .  c)"
    sorry
  show ?thesis 
    apply (rule tsb_below) 
     apply (subst tsbdom_lub,simp_all add: assms) 
     apply (simp add: assms ch2ch_monofun)
      defer
      apply (simp only: f2, simp add: assms) 
    by (simp add: tsTakel_lub2_getch_eq assms) 
qed
*) 

lemma tsbttake_cont2 [simp]: "\<And>n. cont (\<lambda> tb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>n\<cdot>(tb  .  c))))"
  apply (rule contI2, simp)
  apply (rule+)
  sorry
    
(* tsbttakeL is a continuous function *)
lemma tsbttakel_cont [simp]: "cont (\<lambda> n. \<Lambda> tb. Abs_ubundle (\<lambda>c. (c\<in>ubDom\<cdot>tb) \<leadsto> (tsTakeL\<cdot>n\<cdot>(tb  .  c))))"
  by (simp add: cont2cont_LAM)
 
lemma tsbttakeL_below2 [simp]: "(tsbTTakeL\<cdot>n\<cdot>tb) \<sqsubseteq> tb"
  by (simp add: tsbTTakeL_def)
      
lemma tsbttakeL_dom2 [simp]: "ubDom\<cdot>(tsbTTakeL\<cdot>i\<cdot>tb) = ubDom\<cdot>tb"
  by (simp add: ubdom_below)

lemma tsbttakeL_least2: "tsbTTakeL\<cdot>(Fin 0)\<cdot>tb = ubLeast(ubDom\<cdot>tb)"
  apply (rule ub_eq, simp_all)
  by (simp add: tsbTTakeL_def ubgetch_insert)

lemma tsbttakeL_inf2 [simp]: "(tsbTTakeL\<cdot>\<infinity>\<cdot>tb) = tb"
  by (simp add: tsbTTakeL_def)

lemma tsbttakeL_least_getch2 [simp]: assumes "c \<in> ubDom\<cdot>tb"
  shows "(tsbTTakeL\<cdot>(Fin 0)\<cdot>tb) . c = \<bottom>"
  by (metis assms ubleast_ubgetch tsbttakeL_least2)


(*
subsubsection \<open>tsbTickcount\<close>
(* general lemma *)
lemma tsb_below_ran_below1: assumes "x \<sqsubseteq> y" and "tsbDom\<cdot>x \<noteq> {}"
  shows "\<forall> ts \<in> ran (Rep_TSB x).(\<exists> ts2\<in> (ran (Rep_TSB y)). (ts) \<sqsubseteq> (ts2))"
proof -
  have f1: "tsbDom\<cdot>y \<noteq> {}"
    using assms(1) assms(2) tsbdom_below by blast
  have f2: "\<forall> c \<in> tsbDom\<cdot>x. x . c \<sqsubseteq> y . c"
    by (simp add: assms(1) monofun_cfun_arg monofun_cfun_fun)
  show ?thesis
    (* ISAR proof generateable via sledgehammer *)
    by (smt assms(1) domI f2 mem_Collect_eq option.simps(1) ran_def tsbdom_below tsbdom_insert 
            tsbgetchE)
qed
  
lemma tsb_below_ran_below2: assumes "x \<sqsubseteq> y" and "tsbDom\<cdot>x \<noteq> {}"
  shows "\<forall> ts \<in> ran (Rep_TSB y).(\<exists> ts2\<in> (ran (Rep_TSB x)). (ts2) \<sqsubseteq> (ts))"
proof -
  have f1: "tsbDom\<cdot>y = tsbDom\<cdot>x"
    using assms(1)  tsbdom_below by blast
  have f2: "\<forall> c \<in> tsbDom\<cdot>y . x . c \<sqsubseteq> y . c"
    using assms(1) monofun_cfun_arg monofun_cfun_fun by blast
  thus ?thesis
    (* ISAR proof generateable via sledgehammer *)
    by (smt domI f1 mem_Collect_eq option.simps(1) ran_def tsbdom_insert tsbgetchE)
qed
  
  (* general lemma *)

    
(* general lemma *)
lemma lnat_set_min_below: assumes "finite (A:: lnat set)" and "finite (B ::lnat set)" 
                          and "A \<noteq> {}" and "B \<noteq> {}" and "\<forall> a \<in> A . \<exists> b \<in> B.  a \<sqsubseteq> b"
                                                     and "\<forall> b \<in> B. \<exists> a \<in> A. a \<sqsubseteq> b"
  shows "Min A \<sqsubseteq> Min B"
  by (meson Min_in Min_le_iff assms(1) assms(2) assms(3) assms(4) assms(6) lnle_conv)  
  
  
(* is equal to the defintion of tsbTickCount3 *)
definition tsbTickCount :: "'m TSB \<rightarrow> lnat" where
"tsbTickCount \<equiv> \<Lambda> tb. if tsbDom\<cdot>tb \<noteq> {} then (LEAST ln. ln\<in>{(#\<surd>(tb. c)) | c. c \<in> tsbDom\<cdot>tb}) else \<infinity>"

abbreviation tsbTickCount_abbrv :: "'m TSB \<Rightarrow> lnat "  ("#\<surd>tsb _ ") where
" #\<surd>tsb tsb \<equiv> tsbTickCount\<cdot>tsb"

lemma tsbtick_lengths_ne: assumes "tsbDom\<cdot>tb \<noteq> {}"
  shows "{(#\<surd>(tb. c)) | c. c \<in> tsbDom\<cdot>tb} \<noteq> {}"
    using assms by blast

lemma tsbtick_least_in_set: assumes "tsbDom\<cdot>tb \<noteq> {}"
  shows "(LEAST ln. ln\<in>{(#\<surd>(tb. c)) | c. c \<in> tsbDom\<cdot>tb}) \<in> {(#\<surd>(tb. c)) | c. c \<in> tsbDom\<cdot>tb}"
  by (metis (mono_tags, lifting) LeastI all_not_in_conv assms mem_Collect_eq)
    
lemma tsbtick_min_on_channel: assumes "tsbDom\<cdot>tb \<noteq> {}"
  shows "\<exists> c \<in> tsbDom\<cdot>tb. (#\<surd>(tb. c)) = (LEAST ln. ln\<in>{(#\<surd>(tb. c)) | c. c \<in> tsbDom\<cdot>tb})"
    by (smt LeastI assms mem_Collect_eq tsbtick_least_in_set)

lemma lnat_set_least_below: assumes "(A :: lnat set) \<noteq> {}" and "(B :: lnat set) \<noteq> {}"
  and "\<forall> a \<in> A . \<exists> b \<in> B.  a \<sqsubseteq> b" and "\<forall> b \<in> B. \<exists> a \<in> A. a \<sqsubseteq> b"
shows "(LEAST ln. ln \<in> A) \<sqsubseteq> (LEAST ln. ln \<in> B)"
  by (metis (no_types, lifting) LeastI Least_le all_not_in_conv assms(2) assms(4) lnle_conv rev_below_trans)
  
lemma tsbtick_set_below: assumes "\<forall>b\<in>{(y  .  c) |c. c \<in> tsbDom\<cdot>y}. \<exists>a\<in>{(x  .  c) |c. c \<in> tsbDom\<cdot>x}. (#\<surd> a) \<sqsubseteq> (#\<surd> b)"
  shows "\<forall>b\<in>{#\<surd> (y  .  c) |c. c \<in> tsbDom\<cdot>y}. \<exists>a\<in>{#\<surd> (x  .  c) |c. c \<in> tsbDom\<cdot>x}. a \<sqsubseteq> b"
    using assms by fastforce
    
      
lemma tsbtick_least_mono_pre1: assumes "x \<sqsubseteq> y" and "tsbDom\<cdot>x \<noteq> {}"
  shows "(LEAST ln. ln\<in>{(#\<surd>(x. c)) | c. c \<in> tsbDom\<cdot>x}) \<sqsubseteq> (LEAST ln. ln\<in>{(#\<surd>(y. c)) | c. c \<in> tsbDom\<cdot>y})"
proof -
  have f1: "tsbDom\<cdot>y = tsbDom\<cdot>x"
    using assms(1) assms(2) tsbdom_below by blast
  have f2: "\<forall>b\<in>{(y  .  c) |c. c \<in> tsbDom\<cdot>y}. \<exists>a\<in>{(x  .  c) |c. c \<in> tsbDom\<cdot>x}. (a) \<sqsubseteq> (b) 
          \<Longrightarrow> \<forall>b\<in>{(y  .  c) |c. c \<in> tsbDom\<cdot>y}. \<exists>a\<in>{(x  .  c) |c. c \<in> tsbDom\<cdot>x}. (#\<surd> a) \<sqsubseteq> (#\<surd> b)"
    by (meson monofun_cfun_arg)
  show ?thesis
    apply (rule lnat_set_least_below)
      using assms(2) apply blast
      using assms(2) f1 apply blast
      apply (smt assms(1) f1 mem_Collect_eq monofun_cfun_arg tsbgetch_below)
      apply (rule tsbtick_set_below, rule f2)
      using assms(1) f1 tsbgetch_below by fastforce
  qed
    
lemma tsbtick_mono_pre: assumes "x \<sqsubseteq> y"
  shows "(if tsbDom\<cdot>x \<noteq> {} then (LEAST ln. ln\<in>{(#\<surd>(x. c)) | c. c \<in> tsbDom\<cdot>x}) else \<infinity>)
         \<sqsubseteq> (if tsbDom\<cdot>y \<noteq> {} then (LEAST ln. ln\<in>{(#\<surd>(y. c)) | c. c \<in> tsbDom\<cdot>y}) else \<infinity>)"
proof (cases "tsbDom\<cdot>x \<noteq> {}")
  case True
  then show ?thesis
    using assms tsbtick_least_mono_pre1 by force
next
  case False
    moreover
    have f1: "tsbDom\<cdot>y = tsbDom\<cdot>x"
      using assms(1)  tsbdom_below by blast
    ultimately show ?thesis
      by (simp)
qed
  
    
lemma tsbtick_mono [simp]:
  shows "monofun (\<lambda> tb. if tsbDom\<cdot>tb \<noteq> {} then 
                                          (LEAST ln. ln\<in>{(#\<surd>(tb. c)) | c. c \<in> tsbDom\<cdot>tb}) else \<infinity>)"
  using monofun_def tsbtick_mono_pre by blast

lemma tsbtick_chain [simp]:   assumes "chain Y" and "\<And> i. tsbDom\<cdot>(Y i) \<noteq> {}" 
shows "chain (\<lambda> i. if tsbDom\<cdot>(Y i) \<noteq> {} then (LEAST ln. ln\<in>{(#\<surd>((Y i). c)) | c. c \<in> tsbDom\<cdot>(Y i)}) else \<infinity>)"
proof -
  have f1: "\<And>i.(Y i) \<sqsubseteq> (Y (Suc i))"
    by (simp add: assms(1) po_class.chainE)
  have f2: "\<And> i. tsbDom\<cdot>(\<Squnion>i. Y i) = tsbDom\<cdot>(Y i)"
    by (simp add: assms(1) assms(2))
  show ?thesis  
    apply (rule chainI)
    by (rule tsbtick_mono_pre, simp add: f1)
qed
  

lemma tsbtick_least_chain2: assumes "chain Y" and "\<And> i. tsbDom\<cdot>(Y i) \<noteq> {}"
  shows "chain (\<lambda> i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))"
proof -
  have f1: "\<And>i.(Y i) \<sqsubseteq> (Y (Suc i))"
    by (simp add: assms(1) po_class.chainE)
  have f2: "\<And> i. tsbDom\<cdot>(\<Squnion>i. Y i) = tsbDom\<cdot>(Y i)"
    by (simp add: assms(1) assms(2))
    
  have f3: "chain (\<lambda> i. if tsbDom\<cdot>(Y i) \<noteq> {} then (LEAST ln. ln\<in>{(#\<surd>((Y i). c)) | c. c \<in> tsbDom\<cdot>(Y i)}) else \<infinity>)"
    apply (rule chainI)
    by (rule tsbtick_mono_pre, simp add: f1)
  have f4: "\<And> i. (LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i)) = (if tsbDom\<cdot>(Y i) \<noteq> {} then (LEAST ln. ln\<in>{(#\<surd>((Y i). c)) | c. c \<in> tsbDom\<cdot>(Y i)}) else \<infinity>)"
    using assms(2) f2 by auto
  show ?thesis
    apply (subst f4)
    by (simp add: f3)
qed  
  
lemma tsbtick_least_chain: assumes "chain Y" and "tsbDom\<cdot>(\<Squnion>i. Y i) \<noteq> {}"
  shows "chain (\<lambda> i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Lub Y))"
proof -
  have f1: "\<And>i.(Y i) \<sqsubseteq> (Y (Suc i))"
    by (simp add: assms(1) po_class.chainE)
  have f2: "\<And> i. tsbDom\<cdot>(\<Squnion>i. Y i) = tsbDom\<cdot>(Y i)"
    by (simp add: assms(1) assms(2))
  have f3: "\<And>i . (LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Lub Y)) =  (LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))"
    using f2 by presburger
  show ?thesis
    apply (subst f3)
    apply (rule tsbtick_least_chain2)
      by (simp_all add: assms f2)
qed    
 
lemma tsbtick_least_chain3: assumes "chain Y" and "\<And> i. tsbDom\<cdot>(Y i) \<noteq> {}"
  shows "chain (\<lambda> i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))"
proof -
  have f1: "\<And>i.(Y i) \<sqsubseteq> (Y (Suc i))"
    by (simp add: assms(1) po_class.chainE)
  have f2: "\<And> i. tsbDom\<cdot>(\<Squnion>i. Y i) = tsbDom\<cdot>(Y i)"
    by (simp add: assms(1) assms(2))
    
  have f3: "chain (\<lambda> i. if tsbDom\<cdot>(Y i) \<noteq> {} then (LEAST ln. ln\<in>{(#\<surd>((Y i). c)) | c. c \<in> tsbDom\<cdot>(Y i)}) else \<infinity>)"
    apply (rule chainI)
    by (rule tsbtick_mono_pre, simp add: f1)
  have f4: "\<And> i. (LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i)) = (if tsbDom\<cdot>(Y i) \<noteq> {} then (LEAST ln. ln\<in>{(#\<surd>((Y i). c)) | c. c \<in> tsbDom\<cdot>(Y i)}) else \<infinity>)"
    using assms(2) f2 by auto
  show ?thesis
    apply (subst f4)
    by (simp add: f3)
qed
  
lemma chains_lub_eq: assumes "chain (Y::nat \<Rightarrow> lnat)" and "chain (X::nat \<Rightarrow> lnat)" and "\<exists> i. \<forall> j\<ge>i. Y j = X j" shows "(\<Squnion>i. Y i) = (\<Squnion>i. X i)"
proof - 
  have "(\<Squnion>i. Y i) \<le> (\<Squnion>i. X i)"
  proof - 
    obtain i where f1: "\<forall> j\<ge>i. Y j = X j"
      using assms by blast
    have "\<And> j. (X j) \<le> (\<Squnion>i. X i)" 
      using assms(2) is_ub_thelub lnle_def by blast
    then have "\<forall> j\<ge>i. (Y j) \<le> (\<Squnion>i. X i)"
      by (simp add: f1)
    then show ?thesis
    proof -
      have f1: "\<forall>n na f l. (\<not> (n::nat) \<le> na \<or> \<not> f na \<le> (l::lnat) \<or> (\<exists>n na. n \<le> na \<and> \<not> f n \<le> f na)) \<or> f n \<le> l"
        by (meson order_subst2)
      obtain nn :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" and nna :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" where
        f2: "\<forall>x1. (\<exists>v4 v5. v4 \<le> v5 \<and> \<not> x1 v4 \<le> x1 v5) = (nn x1 \<le> nna x1 \<and> \<not> x1 (nn x1) \<le> x1 (nna x1))"
        by moura
      have f3: "\<forall>n. \<not> i \<le> n \<or> Y n \<le> Lub X"
        by (metis \<open>\<forall>j\<ge>i. Y j \<le> (\<Squnion>i. X i)\<close>)
      then have f4: "Y i \<le> Lub X"
        by (metis nat_le_linear)
      obtain nnb :: "lnat \<Rightarrow> (nat \<Rightarrow> lnat) \<Rightarrow> nat" where
        f5: "\<forall>f l. (\<not> chain f \<or> f (nnb l f) \<notsqsubseteq> l) \<or> Lub f \<sqsubseteq> l"
        by (meson lub_below)
      have "\<not> nn Y \<le> nna Y \<or> Y (nn Y) \<le> Y (nna Y)"
        by (meson assms(1) lnle_conv po_class.chain_mono)
      then show ?thesis
        using f5 f4 f3 f2 f1 by (metis (full_types) assms(1) lnle_conv nat_le_linear)
    qed
  qed  
  moreover have "(\<Squnion>i. X i) \<le> (\<Squnion>i. Y i)"
  proof -   
    obtain i where f1: "\<forall> j\<ge>i. X j = Y j"
      using assms(3) by fastforce
    have "\<And> j. (Y j) \<le> (\<Squnion>i. Y i)" 
      using assms(1) is_ub_thelub lnle_def by blast
    then have "\<forall> j\<ge>i. (X j) \<le> (\<Squnion>i. Y i)"
      by (simp add: f1)
    then show ?thesis
    proof -
      have f1: "\<forall>n na f l. (\<not> (n::nat) \<le> na \<or> \<not> f na \<le> (l::lnat) \<or> (\<exists>n na. n \<le> na \<and> \<not> f n \<le> f na)) \<or> f n \<le> l"
        by (meson order_subst2)
      obtain nn :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" and nna :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" where
        f2: "\<forall>x1. (\<exists>v4 v5. v4 \<le> v5 \<and> \<not> x1 v4 \<le> x1 v5) = (nn x1 \<le> nna x1 \<and> \<not> x1 (nn x1) \<le> x1 (nna x1))"
        by moura
      have f3: "\<forall>n. \<not> i \<le> n \<or> X n \<le> Lub Y"
        by (meson \<open>\<forall>j\<ge>i. X j \<le> (\<Squnion>i. Y i)\<close>)
      then have f4: "X i \<le> Lub Y"
        by (meson nat_le_linear)
      obtain nnb :: "lnat \<Rightarrow> (nat \<Rightarrow> lnat) \<Rightarrow> nat" where
          f5: "\<forall>f l. (\<not> chain f \<or> f (nnb l f) \<notsqsubseteq> l) \<or> Lub f \<sqsubseteq> l"
        by (meson lub_below)
      have "\<not> nn X \<le> nna X \<or> X (nn X) \<le> X (nna X)"
        by (metis assms(2) lnle_conv po_class.chain_mono)
      then show ?thesis
        using f5 f4 f3 f2 f1 by (metis (full_types) assms(2) lnle_conv nat_le_linear)
    qed
  qed    
  ultimately show ?thesis
    using order_trans by auto
qed    

  (* lemma chain_lub_eq: assumes "chain (X::nat \<Rightarrow> lnat)" and "" shows "\<exists> i. \<forall> j\<ge>i. X i = X j \<longrightarrow> (\<Squnion>i. X i) = X i" *)
lemma chain_lub_eq: assumes "chain (X::nat \<Rightarrow> lnat)" and "\<forall> j\<ge>i. X i = X j" shows "(\<Squnion>i. X i) = X i"
  using assms(1) assms(2) lub_eqI lub_finch1 max_in_chain_def by blast
  
lemma chain_lub_lessInf: assumes "chain (Y::nat \<Rightarrow> lnat)" and "\<exists> i. \<forall> j\<ge>i. Y i = Y j \<and> Y i < \<infinity>" shows "(\<Squnion>i. Y i) < \<infinity>"
  by (metis assms(1) assms(2) dual_order.strict_trans2 lnle_def lub_below nat_le_linear po_class.chain_mono)
    
lemma chain_lub_inf: assumes "chain (Y::nat \<Rightarrow> lnat)" and "\<forall> i. \<exists> j\<ge>i. Y j > Y i" shows "(\<Squnion>i. Y i) = \<infinity>"
  by (metis assms(1) assms(2) below_antisym l42 lnless_def test34 unique_inf_lub) 

lemma chain_mono: assumes "chain (Y::nat \<Rightarrow> lnat)" and "\<exists> i. \<forall> j\<ge>i. (Y i \<ge> Y j)" shows "\<exists> i. \<forall> j\<ge>i. (Y i = Y j)"
  by (meson assms(1) assms(2) dual_order.antisym lnle_def po_class.chain_mono)

    (*
lemma h1: assumes "chain Y" 
              and "\<forall> i. \<forall> ch1 \<in> tsbDom\<cdot>(Lub Y). \<exists> j\<ge>i. ((#\<surd> Y i . ch1) < (#\<surd> Y j . ch1))"
              and "tsbDom\<cdot>(Lub Y) \<noteq> {}"
            shows "(x < \<infinity> \<and> c \<in> tsbDom\<cdot>(Lub Y)) \<Longrightarrow> (\<exists> k\<ge>a. x < #\<surd> Y k . c)"
proof -
  fix x c
  fix a
  assume f0: "x < \<infinity> \<and> c \<in> tsbDom\<cdot>(Lub Y)"
  have f1: "x < \<infinity>"
    using f0 by auto
  have f2: "c \<in> tsbDom\<cdot>(Lub Y)"
    using f0 by auto
  have f3: "\<forall>i. \<exists>j\<ge>i. #\<surd> Y i . c <  #\<surd> Y j . c"
    using assms f0 by blast
  have f4: "x < #\<surd> Y 0 . c \<Longrightarrow> \<exists>k\<ge>a. x < #\<surd> Y k . c"
    by (meson assms(1) chain_mono_less dual_order.strict_trans1 leI lnle_def monofun_cfun_arg order_refl tsbgetch_below)
  moreover have f5: "x \<ge> #\<surd> Y 0 . c \<Longrightarrow> \<exists>k\<ge>a. x < #\<surd> Y k . c"
    sorry
  ultimately moreover have f6: "\<exists>k\<ge>a. x < #\<surd> Y k . c" 
    using leI by blast
  ultimately show ?thesis
    sorry
qed

lemma h2: assumes "chain Y" 
              and "tsbDom\<cdot>(Lub Y) \<noteq> {}"
            shows "\<exists>h. (\<exists>c \<in> tsbDom\<cdot>(Lub Y). h = ((kch :: channel \<Rightarrow> nat) c)) \<and> (\<forall>c \<in> tsbDom\<cdot>(Lub Y). h \<ge> (kch c))"  
  
  oops
    
    *)
    
lemma jc_lem1: assumes "((LEAST l. \<exists>c. l = #\<surd> Y j . c \<and> c \<in> tsbDom\<cdot>(Y j)) \<le> (#\<surd> Y j  .  ch2) ) \<and> ((#\<surd> Y j  .  ch2) < (#\<surd> Y j  .  ch1))"
  shows "(LEAST l. \<exists>c. l = #\<surd> Y j . c \<and> c \<in> tsbDom\<cdot>(Y j)) < (#\<surd> Y j  .  ch1)"
  using assms by auto  
    
 (* convert betwwen set and non-set based definiton *)
lemma testc_conv1: "(LEAST ln. ln \<in> {#\<surd> (Y i)  .  c |c. c \<in> tsbDom\<cdot>(Y i)})
                  = (LEAST l. \<exists>c. l = #\<surd> Y i . c \<and> c \<in> tsbDom\<cdot>(Y i))"
  by auto
    
lemma testc_conv2: "(LEAST ln. ln \<in> {#\<surd> (\<Squnion> i. Y i)  .  c |c. c \<in> tsbDom\<cdot>(\<Squnion> i. Y i)})
                  = (LEAST l. \<exists>c. l = #\<surd> (\<Squnion> i. Y i) . c \<and> c \<in> tsbDom\<cdot>(\<Squnion> i. Y i))"
by auto
 
lemma tsbtick_cont_pre: assumes "chain Y" and "finite (tsbDom\<cdot>(Lub Y))"
  shows "(if tsbDom\<cdot>(\<Squnion>i. Y i) \<noteq> {} then LEAST ln. ln \<in> {#\<surd> (\<Squnion>i. Y i)  .  c |c. c \<in> tsbDom\<cdot>(\<Squnion>i. Y i)} else \<infinity>) \<sqsubseteq>
         (\<Squnion>i. if tsbDom\<cdot>(Y i) \<noteq> {} then LEAST ln. ln \<in> {#\<surd> ((Y i)  .  c) |c. c \<in> tsbDom\<cdot>(Y i)} else \<infinity>)"
proof (cases "tsbDom\<cdot>(\<Squnion>i. Y i) \<noteq> {}")
  case True
  hence f1: "\<forall> i. tsbDom\<cdot>(Y i) = tsbDom\<cdot>(\<Squnion>i. Y i)"
    by (simp add: assms(1))
  hence f11: "\<forall> i. tsbDom\<cdot>(\<Squnion>i. Y i) =  tsbDom\<cdot>(Y i)"
    by (simp add: assms(1))
  hence f10: "\<forall> i. tsbDom\<cdot>(Y i) \<noteq> {}"
    using True by auto
  have f2: "\<forall> c. #\<surd> (Lub Y  .  c) = (\<Squnion> i. #\<surd> ((Y i) .c))"
    by (metis (mono_tags, lifting) assms contlub_cfun_arg lub_eq lub_eval theRep_chain tsbgetch_insert)
  show ?thesis
    apply (simp only: True f10)
    apply auto
    proof (cases "finite_chain Y")
      case True
      hence "(LEAST ln. \<exists>c. ln = #\<surd> Lub Y  .  c \<and> c \<in> tsbDom\<cdot>(Lub Y)) \<sqsubseteq> (\<Squnion>i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))"
      proof -
        obtain nn :: "(nat \<Rightarrow> 'a TSB) \<Rightarrow> nat" where
          f1: "\<And>f. \<not> finite_chain f \<or> \<not> chain f \<or> Lub f = f (nn f)"
          using l42 by moura
        have "\<forall>f. \<exists>n. tsbDom\<cdot>(f n::'a TSB) = {} \<or> chain (\<lambda>n. LEAST l. \<exists>c. l = #\<surd> f n . c \<and> c \<in> tsbDom\<cdot>(f n)) \<or> \<not> chain f"
          using tsbtick_least_chain2 by blast
        then have "\<And>n. (LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n)) \<sqsubseteq> (\<Squnion>n. LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n))"
          using assms f10 is_ub_thelub by blast
        then show ?thesis
          using f1 True assms by presburger
      qed
      thus  "(LEAST ln. \<exists>c. ln = #\<surd> Lub Y  .  c \<and> c \<in> tsbDom\<cdot>(Lub Y)) \<le> (\<Squnion>i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))"
        using lnle_conv by blast  
    next
      case False
      hence f300: "\<not> finite_chain Y"
        by simp 
      have f301: "chain (\<lambda> i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))"
        using assms f10 tsbtick_least_chain3 by blast
      have f302: "(LEAST ln. \<exists>c. ln = #\<surd> Lub Y  .  c \<and> c \<in> tsbDom\<cdot>(Lub Y)) \<sqsubseteq> (\<Squnion>i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))"
      proof(cases "finite_chain (\<lambda> i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))")
        case True
        then have f30211: "\<exists>i. max_in_chain i (\<lambda> i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))"
          using finite_chain_def f301 by blast
            
        then obtain maxI where f30212: "\<forall>j. maxI \<le> j \<longrightarrow> (LEAST ln. \<exists>c. ln = #\<surd> Y maxI  .  c \<and> c \<in> tsbDom\<cdot>(Y maxI)) = (LEAST ln. \<exists>c. ln = #\<surd> Y j  .  c \<and> c \<in> tsbDom\<cdot>(Y j))"
          by (meson max_in_chain_def)
        then obtain maxCount where f30213: "maxCount = (LEAST ln. \<exists>c. ln = #\<surd> Y maxI  .  c \<and> c \<in> tsbDom\<cdot>(Y maxI))"
          by blast
        then have f30214: "maxCount = (\<Squnion>i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))"
          by (metis (mono_tags, lifting) True f30212 f301 l42 le_cases max_in_chainI3 max_in_chain_def)
        
        have f30215: "finite (tsbDom\<cdot>(Lub Y))"  
          using assms by blast
            
        have f30216: "\<exists> maxCh \<in> tsbDom\<cdot>(Lub Y). \<forall>j\<ge>maxI. maxCount = #\<surd> (Y j . maxCh)"
        proof(rule ccontr)
          assume "\<not>?thesis"
          then have f302161: "\<forall> ch1 \<in> tsbDom\<cdot>(Lub Y). \<exists>j\<ge>maxI. maxCount < #\<surd> (Y j . ch1)"
            by (smt Least_le assms f30212 f30213 order.not_eq_order_implies_strict tsbChain_dom_eq2)
          show "False" 
          proof(cases "card (tsbDom\<cdot>(Lub Y))")
            case 0
            then show ?thesis 
              using f1 f10 f30215 by auto
          next
            case (Suc nat)
            then have i1: "card (tsbDom\<cdot>(Lub Y)) = Suc nat"
              by blast
            show ?thesis
            proof - 
              obtain n where i2: "card (tsbDom\<cdot>(Lub Y)) = n"
                by blast
              then have i3: "n > 0"    
                by (simp add: i1) 
                  
              obtain f where i4: "tsbDom\<cdot>(Lub Y) = f ` {i::nat. i < n}"
                using finite_imp_nat_seg_image_inj_on f30215 card_image i2 by fastforce     
              then have i5: "\<forall>i<n. \<exists>j\<ge>maxI. maxCount < #\<surd> (Y j . (f i))"
                using f302161 by blast

              then obtain x where i6: "x = Max {(LEAST x. x\<ge>maxI \<and> (maxCount < #\<surd> (Y x . (f i)))) | i::nat. i < n}"
                by blast
              have i7: "\<forall>i<n. \<exists>m. (m = (LEAST x. x\<ge>maxI \<and> (maxCount < #\<surd> (Y x . (f i)))) \<and> m\<ge>maxI \<and> (maxCount < #\<surd> (Y m . (f i))))"    
                by (metis (no_types, lifting) LeastI i5)
              have i0: "tsbDom\<cdot>(Lub Y) = tsbDom\<cdot>(Y x)"    
                using assms by simp    
              have i01: "\<forall>i<n. maxCount < #\<surd> (Y x . f i)"
              proof -
                have i010: "\<forall>i<n. maxCount < #\<surd> (Y (LEAST x. x\<ge>maxI \<and> (maxCount < #\<surd> (Y x . (f i)))) . f i)"
                  using i7 by blast
                moreover have i011: "\<forall>i<n. (LEAST x. x\<ge>maxI \<and> (maxCount < #\<surd> (Y x . (f i)))) \<le> x"
                proof - 
                  obtain g where "g = (\<lambda>i. (LEAST x. x\<ge>maxI \<and> (maxCount < #\<surd> (Y x . (f i)))))"
                    by blast
                  then have "g ` {i::nat. i < n} = {(LEAST x. x\<ge>maxI \<and> (maxCount < #\<surd> (Y x . (f i)))) | i::nat. i < n}"
                    by blast
                  then have "finite {(LEAST x. x\<ge>maxI \<and> (maxCount < #\<surd> (Y x . (f i)))) | i::nat. i < n}"
                    using nat_seg_image_imp_finite by auto
                  then show ?thesis
                    using Max_ge i6 by blast
                qed
                ultimately show ?thesis
                proof - 
                  have "\<forall>i<n. #\<surd> (Y (LEAST x. x\<ge>maxI \<and> (maxCount < #\<surd> (Y x . (f i)))) . f i) \<le> #\<surd> (Y x . (f i))"
                    using assms(1) i011 lnle_conv monofun_cfun_arg po_class.chain_mono tsbgetch_below by blast
                  then show ?thesis
                    using i010 less_le_trans by blast
                qed
              qed
              then have i02: "\<forall>ch1\<in>tsbDom\<cdot>(Lub Y). maxCount < #\<surd> (Y x . ch1)"
                by (simp add: i4)
              then have i8: "maxCount < (LEAST ln. \<exists>c. ln = #\<surd> Y x  .  c \<and> c \<in> tsbDom\<cdot>(Y x))"
                using f10 tsbtick_min_on_channel i0 by fastforce
              then have i9: "maxCount < (\<Squnion>i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))"
                using f301 f30214 lnless_def po_eq_conv test34 by fastforce
              then show ?thesis
                using f30214 by simp
            qed  
          qed
        qed
        then obtain maxCh where f30217: "maxCh \<in> tsbDom\<cdot>(Lub Y) \<and> (\<forall>j\<ge>maxI. maxCount = #\<surd> (Y j . maxCh))"
          by blast
        then have f30218: "\<forall>j\<ge>maxI. #\<surd> (Y j . maxCh) = (LEAST ln. \<exists>c. ln = #\<surd> Y j  .  c \<and> c \<in> tsbDom\<cdot>(Y j))"
          by (simp add: f30212 f30213)
        have f30219: "maxCh \<in> tsbDom\<cdot>(Lub Y) \<and> (\<forall> j. \<forall> ch2 \<in> tsbDom\<cdot>(Lub Y). (maxI \<le> j) \<longrightarrow> ((#\<surd> Y j . maxCh) \<sqsubseteq> (#\<surd> Y j .  ch2)))"    
          by (smt Least_le assms f30212 f30213 f30217 lnle_conv tsbChain_dom_eq2)      
        have f302110: "(\<Squnion>i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i)) = (\<Squnion>i.  (#\<surd> Y i  .  maxCh))"
          apply(subst chains_lub_eq, simp_all)
          using f301 apply auto[1]
          using assms apply auto[1]
          using f30218 by fastforce
        show ?thesis 
          apply(subst f302110)
          by (metis (mono_tags, lifting) Least_le f2 f30219 lnle_conv)
      next
        case False
        then have f30221: "\<not>(\<exists>i. max_in_chain i (\<lambda> i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i)))"
          using finite_chain_def f301 by blast
        have f30222: "\<forall>i. \<exists>j\<ge>i. (LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i)) < ( LEAST ln. \<exists>c. ln = #\<surd> Y j  .  c \<and> c \<in> tsbDom\<cdot>(Y j))"
        proof(rule ccontr)
          assume "\<not>?thesis"
          then have "\<exists>i. \<forall>j\<ge>i. (LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i)) = ( LEAST ln. \<exists>c. ln = #\<surd> Y j  .  c \<and> c \<in> tsbDom\<cdot>(Y j))"
          proof -
            { fix nn :: "nat \<Rightarrow> nat" and nna :: "nat \<Rightarrow> (nat \<Rightarrow> lnat) \<Rightarrow> nat" and nnb :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat"
              obtain nnc :: nat where
                ff1: "\<And>n. \<not> nnc \<le> n \<or> (LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n)) \<le> (LEAST l. \<exists>c. l = #\<surd> Y nnc . c \<and> c \<in> tsbDom\<cdot>(Y nnc))"
                using \<open>\<not> (\<forall>i. \<exists>j\<ge>i. (LEAST ln. \<exists>c. ln = #\<surd> Y i . c \<and> c \<in> tsbDom\<cdot>(Y i)) < (LEAST ln. \<exists>c. ln = #\<surd> Y j . c \<and> c \<in> tsbDom\<cdot>(Y j)))\<close> not_le_imp_less by blast
              { assume "(LEAST l. \<exists>c. l = #\<surd> Y (nn (nnb (\<lambda>n. LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n)))) . c \<and> c \<in> tsbDom\<cdot> (Y (nn (nnb (\<lambda>n. LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot> (Y n)))))) \<noteq> (LEAST l. \<exists>c. l = #\<surd> Y (nnb (\<lambda>n. LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n))) . c \<and> c \<in> tsbDom\<cdot> (Y (nnb (\<lambda>n. LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n)))))"
                have "(\<exists>n na f nb. \<not> n \<le> nn n \<or> \<not> na \<le> nna na f \<or> (LEAST l. \<exists>c. l = #\<surd> Y (nn n) . c \<and> c \<in> tsbDom\<cdot>(Y (nn n))) = (LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n)) \<or> chain f \<and> nnb f \<le> nb \<and> f (nna na f) \<le> f na \<and> f (nnb f) \<noteq> f nb) \<or> (\<exists>n\<ge>nnb (\<lambda>n. LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n)). (LEAST l. \<exists>c. l = #\<surd> Y (nnb (\<lambda>n. LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n))) . c \<and> c \<in> tsbDom\<cdot> (Y (nnb (\<lambda>n. LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n))))) \<noteq> (LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n)))"
                  by fastforce
                then have "\<exists>n na f nb. \<not> n \<le> nn n \<or> \<not> na \<le> nna na f \<or> (LEAST l. \<exists>c. l = #\<surd> Y (nn n) . c \<and> c \<in> tsbDom\<cdot>(Y (nn n))) = (LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n)) \<or> chain f \<and> nnb f \<le> nb \<and> f (nna na f) \<le> f na \<and> f (nnb f) \<noteq> f nb"
                  using ff1 f301 by blast }
              then have "\<exists>n na f nb. \<not> n \<le> nn n \<or> \<not> na \<le> nna na f \<or> (LEAST l. \<exists>c. l = #\<surd> Y (nn n) . c \<and> c \<in> tsbDom\<cdot>(Y (nn n))) = (LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n)) \<or> chain f \<and> nnb f \<le> nb \<and> f (nna na f) \<le> f na \<and> f (nnb f) \<noteq> f nb"
                by blast }
            then have "\<exists>n. \<forall>na nb. \<exists>f. \<forall>nc. \<exists>nd ne. \<not> n \<le> na \<or> \<not> nd \<le> nc \<or> (LEAST l. \<exists>c. l = #\<surd> Y na . c \<and> c \<in> tsbDom\<cdot>(Y na)) = (LEAST l. \<exists>c. l = #\<surd> Y n . c \<and> c \<in> tsbDom\<cdot>(Y n)) \<or> chain f \<and> nb \<le> ne \<and> (f nc::lnat) \<le> f nd \<and> f nb \<noteq> f ne"
              using Suc_le_eq by blast
            then show ?thesis
              using TSB.chain_mono \<open>\<not> (\<forall>i. \<exists>j\<ge>i. (LEAST ln. \<exists>c. ln = #\<surd> Y i . c \<and> c \<in> tsbDom\<cdot>(Y i)) < (LEAST ln. \<exists>c. ln = #\<surd> Y j . c \<and> c \<in> tsbDom\<cdot>(Y j)))\<close> f301 leI by blast
          qed
          then have "\<exists>i. max_in_chain i (\<lambda> i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))" 
            by (meson max_in_chainI)
          then show "False" 
            using f30221 by blast
        qed      
        then have "(\<Squnion>i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i)) = \<infinity>"
          apply(subst chain_lub_inf)
          apply(simp_all add: assms)
          using True assms tsbtick_least_chain by blast
        then show ?thesis 
          by simp
      qed  
      thus "(LEAST ln. \<exists>c. ln = #\<surd> Lub Y  .  c \<and> c \<in> tsbDom\<cdot>(Lub Y)) \<le> (\<Squnion>i. LEAST ln. \<exists>c. ln = #\<surd> Y i  .  c \<and> c \<in> tsbDom\<cdot>(Y i))"
        using lnle_conv by blast 
    qed
next
  case False
  hence "\<forall> i. tsbDom\<cdot>(Y i) = {}"
    by (simp add: assms)
  thus?thesis
    by (simp)
qed   
  
lemma tsbtick_cont [simp]:
  shows "cont (\<lambda> tb. if tsbDom\<cdot>tb \<noteq> {} then 
                                          (LEAST ln. ln\<in>{(#\<surd>(tb. c)) | c. c \<in> tsbDom\<cdot>tb}) else \<infinity>)"
proof - 
  have f1: "\<forall>sb. finite (tsbDom\<cdot>sb)"
    sorry
  show ?thesis
    apply (rule contI2)
    apply simp
    using f1 tsbtick_cont_pre by blast
qed
      

(* more lemmas *)
  thm tsbTickCount_def
     
    
lemma tsbtick_least1 [simp]: assumes "cs = {}" 
  shows "#\<surd>tsb tsbLeast cs = \<infinity>"
proof -
  have "tsbDom\<cdot>(tsbLeast cs) = {}"
    by (simp add: assms)
  thus ?thesis
    by (simp add: tsbTickCount_def)
qed
  
    
lemma tsbtick_least2 [simp]: assumes "cs \<noteq> {}" 
 shows "#\<surd>tsb tsbLeast cs = Fin 0 "
proof -
  have f1: "tsbDom\<cdot>(tsbLeast cs) \<noteq> {}"
    by (simp add: assms)
  moreover
  have f2: "\<forall> c \<in> tsbDom\<cdot>(tsbLeast cs). #\<surd> ((tsbLeast cs) . c) = Fin 0"
    by simp
  ultimately show ?thesis
    apply (simp add: tsbTickCount_def)
    by (smt Fin_0 LeastI f2 tsbleast_tsdom tsbtick_min_on_channel)
qed
  
lemma tsbtick_below [simp]: assumes "x \<sqsubseteq> y"
  shows "#\<surd>tsb x \<sqsubseteq> #\<surd>tsb y"
  using assms monofun_cfun_arg by blast
       
lemma tsbtick_least: assumes "tsbDom\<cdot>tsb1 \<noteq> {}"
  shows "#\<surd>tsb tsb1 = n \<Longrightarrow> \<forall> c \<in> tsbDom\<cdot>tsb1 . n \<sqsubseteq> #\<surd> (tsb1 . c)"
  apply rule
  apply (subst (asm) tsbTickCount_def, simp add: assms)
  by (metis (mono_tags, lifting) Least_le)
    

(* Intro rule for tsbtickcount *)
lemma tsbtickI: assumes "\<exists> c \<in> tsbDom\<cdot>tb . #\<surd> (tb . c) = n"
 and "\<forall> c \<in> tsbDom\<cdot>tb. n \<sqsubseteq> #\<surd> (tb . c)"
 shows "#\<surd>tsb tb = n"
proof -
  have f0: "tsbDom\<cdot>tb \<noteq> {}"
    using assms(1) by blast
  obtain cc :: channel where
    f1: "cc \<in> tsbDom\<cdot>tb \<and> #\<surd> tb . cc = n"
    using assms(1) by blast
  have f2: "\<forall>t l. (tsbDom\<cdot>(t::'a TSB) = {} \<or> #\<surd>tsb t \<noteq> l) \<or> (\<forall>c. c \<notin> tsbDom\<cdot>t \<or> l \<sqsubseteq> #\<surd> t . c)"
    using tsbtick_least by blast
  have f3: "tsbTickCount_abbrv = (\<lambda>t. if tsbDom\<cdot>(t::'a TSB) \<noteq> {} then 
                                    LEAST l. l \<in> {#\<surd> t . c |c. c \<in> tsbDom\<cdot>t} else \<infinity>)"
    by (simp add: tsbTickCount_def)
  obtain cca :: "'a TSB \<Rightarrow> channel" where
    f4: "\<forall>t. tsbDom\<cdot>t = {} \<or> cca t \<in> tsbDom\<cdot>t 
              \<and> #\<surd> t . cca t = (LEAST l. l \<in> {#\<surd> t . c |c. c \<in> tsbDom\<cdot>t})"
    using tsbtick_min_on_channel by moura
  hence f5: "n \<sqsubseteq> #\<surd> tb . cca tb"
    using f0 assms(2) by blast
  have "(LEAST l. l \<in> {#\<surd> tb . c |c. c \<in> tsbDom\<cdot>tb}) \<sqsubseteq> n"
    using f3 f2 f1 by (meson f0)
  thus ?thesis
    using f5 f4 f3 f0 by auto
qed

(* insertion rule for tsbtickcount *)
lemma tsbtick_insert: "#\<surd>tsb tb = (if tsbDom\<cdot>tb \<noteq> {} then 
                                          (LEAST ln. ln\<in>{(#\<surd>(tb. c)) | c. c \<in> tsbDom\<cdot>tb}) else \<infinity>)"
  by (simp add: tsbTickCount_def)
    
lemma tsbtickI_inf: assumes "tsbDom\<cdot>tb = {}"
  shows "#\<surd>tsb tb = \<infinity>"
  by (metis assms empty_iff tsb_eq tsbleast_tsdom tsbtick_least1)
  
lemma tsbtick_pref_eq: assumes "tsb1 \<sqsubseteq> tsb2" and "Fin n \<le> #\<surd>tsb tsb1"
  shows "(tsbTTake n\<cdot>tsb1) = (tsbTTake n\<cdot>tsb2)"
proof -
  have f0: "tsbDom\<cdot>tsb1 = tsbDom\<cdot>tsb2"
    by (simp add: assms(1) tsbdom_below)
  have f1: "\<forall> c . tsb1 . c \<sqsubseteq> tsb2 . c"
    by (simp add: assms(1) tsbgetch_below)
  have f2: "\<forall> c \<in> tsbDom\<cdot>tsb1. Fin n \<le> (#\<surd> (tsb1 . c))"
    by (metis (mono_tags, hide_lams) all_not_in_conv assms(2) lnle_def trans_lnle tsbtick_least)
      (*
  have f3: "\<forall> c \<in> tsbDom\<cdot>tsb1. (#\<surd> (tsb1 . c)) \<le> (#\<surd> (tsb2 . c))"
    using f1 lnle_def monofun_cfun_arg by blast
  have f4: "\<forall> c \<in> tsbDom\<cdot>tsb1. Fin n \<le> (#\<surd> (tsb2 . c))"
    using f2 f3 trans_lnle by blast
      *)
  
  show ?thesis
    apply (rule tsb_eq)
    apply (simp add: assms(1) tsbdom_below)
    apply (subst (1 2) tsbttake2ttakeI, simp_all)
      using assms(1) tsbdom_below apply blast
      using f1 f2 tstake_less_below by blast
  qed 
    
lemma tsbtick_geI: assumes "\<forall> c \<in> tsbDom\<cdot>tb. n \<le> #\<surd>(tb . c)"
  shows "n \<le> #\<surd>tsb tb"
  by (metis (no_types, lifting) assms inf_ub tsbtick_insert tsbtick_min_on_channel)

    
lemma tsbtick_le: assumes "tsbDom\<cdot>tb1 \<noteq> {}" and "((#\<surd>tsb tb1)) \<le> (#\<surd>tsb tb2)"
shows "\<exists> c1 \<in> tsbDom\<cdot>tb1. \<forall> c2 \<in> tsbDom\<cdot>tb2. (#\<surd>(tb1 . c1)) \<le> (#\<surd>(tb2 . c2))"
  by (smt assms(1) assms(2) dual_order.trans equals0D lnle_def tsbtick_insert tsbtick_least 
          tsbtick_min_on_channel) 

lemma tsbtick_tsbttake: assumes "tsbDom\<cdot>tb \<noteq> {}"
  shows "#\<surd>tsb (tsbTTake n\<cdot>tb) = min (#\<surd>tsb tb) (Fin n)"
    apply (rule tsbtickI, subst tsbttake_dom)
       apply (metis (no_types, lifting) assms tsbtick_insert tsbtick_min_on_channel 
                    tsbttake2ttakeI tstake_len)
       apply (subst tsbttake_dom)
       using min_le_iff_disj tsbtick_least by fastforce

lemma tsbtick_tsbres:  shows "(#\<surd>tsb tb) \<le> #\<surd>tsb (tb\<bar>cs)"
proof -
  have "\<forall>t. #\<surd>tsb t::'a TSB = (if tsbDom\<cdot>t = {} then \<infinity> else LEAST l. l \<in> {#\<surd> t . c |c. c \<in> tsbDom\<cdot>t})"
    by (simp add: tsbtick_insert)
  hence f1: "\<forall>t. if tsbDom\<cdot>(t::'a TSB) = {} then #\<surd>tsb t = \<infinity> else #\<surd>tsb t = (LEAST l. l \<in> {#\<surd> t . c |c. c \<in> tsbDom\<cdot>t})"
    by meson
  have f2: "\<forall>t l. tsbDom\<cdot>(t::'a TSB) = {} \<or> #\<surd>tsb t \<noteq> l \<or> (\<forall>c. c \<notin> tsbDom\<cdot>t \<or> l \<sqsubseteq> #\<surd> t . c)"
    using tsbtick_least by blast
  have f3: "\<forall>C Ca c. \<not> C \<subseteq> Ca \<or> (c::channel) \<notin> C \<or> c \<in> Ca"
    by blast
  have f4: "tsbDom\<cdot>tb \<inter> cs \<subseteq> tsbDom\<cdot>tb"
    by blast
  obtain cc :: "'a TSB \<Rightarrow> channel" where
    "\<forall>t. tsbDom\<cdot>t = {} \<or> cc t \<in> tsbDom\<cdot>t \<and> #\<surd> t . cc t = (LEAST l. l \<in> {#\<surd> t . c |c. c \<in> tsbDom\<cdot>t})"
    using tsbtick_min_on_channel by moura
  hence f5: "tsbDom\<cdot>(tb \<bar> cs) = {} \<or> cc (tb \<bar> cs) \<in> tsbDom\<cdot>(tb \<bar> cs) \<and> #\<surd> (tb \<bar> cs) . cc (tb \<bar> cs) = (LEAST l. l \<in> {#\<surd> (tb \<bar> cs) . c |c. c \<in> tsbDom\<cdot>(tb \<bar> cs)})"
    by blast
  hence f6: "tsbDom\<cdot>(tb \<bar> cs) \<noteq> {} \<longrightarrow> cc (tb \<bar> cs) \<in> tsbDom\<cdot>tb \<inter> cs"
    using tsresrict_dom3 by blast
  have f7: "tsbDom\<cdot>(tb \<bar> cs) \<noteq> {} \<and> tsbDom\<cdot>tb \<noteq> {} \<longrightarrow> ((LEAST l. l \<in> {#\<surd> tb . c |c. c \<in> tsbDom\<cdot>tb}) \<sqsubseteq> #\<surd> tb . cc (tb \<bar> cs)) = (#\<surd>tsb tb \<sqsubseteq> #\<surd>tsb tb \<bar> cs )"
    using f5 f1 by force
  { assume "(\<infinity> \<le> \<infinity>) \<noteq> (#\<surd>tsb tb \<le> #\<surd>tsb tb \<bar> cs )"
    hence "tsbDom\<cdot>tb \<noteq> {}"
      by force
    moreover
    { assume "tsbDom\<cdot>tb \<noteq> {} \<and> ((LEAST l. l \<in> {#\<surd> tb . c |c. c \<in> tsbDom\<cdot>tb}) \<le> \<infinity>) \<noteq> (#\<surd>tsb tb \<le> #\<surd>tsb tb \<bar> cs )"
      hence "tsbDom\<cdot>tb \<noteq> {} \<and> #\<surd>tsb tb \<bar> cs \<noteq> \<infinity>"
        by force
      hence ?thesis
        using f7 f6 f4 f3 f2 f1 by (meson lnle_def) }
    ultimately have ?thesis
      using inf_ub by blast }
  thus ?thesis
    by blast
qed
  
 
  
lemma tsbtick_tsbunion1: assumes "tsbDom\<cdot>tb1 \<noteq> {}"
                        and "tsbDom\<cdot>tb1 \<inter> tsbDom\<cdot>tb2 = {}"
                        and "((#\<surd>tsb tb1)) \<le> (#\<surd>tsb tb2)"
  shows "(#\<surd>tsb(tb1 \<uplus> tb2)) = ((#\<surd>tsb tb1))"
proof -
  have f1: "tsbDom\<cdot>(tb1 \<uplus> tb2) \<noteq> {}"
    by (simp add: assms(1))
  have f2: "\<exists> c1 \<in> tsbDom\<cdot>tb1. \<forall> c2 \<in> tsbDom\<cdot>tb2. (#\<surd>(tb1 . c1)) \<le> (#\<surd>(tb2 . c2))"
    using assms(1) assms(3) tsbtick_le by blast
  have f3: "\<forall> c1 \<in> tsbDom\<cdot>tb1 . ((tb1 \<uplus> tb2) . c1) = (tb1 . c1)"
    by (meson assms(2) disjoint_iff_not_equal tsbunion_getchL)
  have f4: "tsbDom\<cdot>(tb1 \<uplus> tb2) = (tsbDom\<cdot>tb1 \<union> tsbDom\<cdot>tb2)"
    by simp
  obtain cmin where o1: "(#\<surd>((tb1 \<uplus> tb2) . cmin)) = ((#\<surd>tsb tb1))"
    by (metis (no_types, lifting) assms(1) f3 tsbtick_insert tsbtick_min_on_channel)
  have f5: "\<forall> c1 \<in> tsbDom\<cdot>tb1 . (#\<surd>((tb1 \<uplus> tb2) . cmin)) \<le> (#\<surd>((tb1 \<uplus> tb2) . c1))"
    using o1 f3 tsbtick_least by fastforce
  have f6: "\<forall> c2 \<in> tsbDom\<cdot>tb2.  (#\<surd>((tb1 \<uplus> tb2) . cmin)) \<le> (#\<surd>((tb1 \<uplus> tb2) . c2))"
    using f2 f3 f5 by fastforce
  show ?thesis
    by (smt Abs_cfun_inverse2 Int_commute UnE assms(2) below_antisym f1 f4 f5 f6 lnle_def o1 
            tsbTickCount_def tsbtick_cont tsbtick_min_on_channel tsbtick_tsbres tsbunion_restrict3)
qed
  
lemma tsbtick_tsbunion2: assumes "tsbDom\<cdot>tb2 \<noteq> {}"
                         and "tsbDom\<cdot>tb1 \<inter> tsbDom\<cdot>tb2 = {}"
                         and "(#\<surd>tsb tb2) \<le> ((#\<surd>tsb tb1))"
  shows "(#\<surd>tsb(tb1 \<uplus> tb2)) = (#\<surd>tsb tb2)"
  by (metis assms(1) assms(2) assms(3) inf_commute tsbtick_tsbunion1 tsbunion_commutative)    

 
lemma tsbtick_tsbunion: assumes "tsbDom\<cdot>tb1 \<inter> tsbDom\<cdot>tb2 = {}"
  shows "(#\<surd>tsb(tb1 \<uplus> tb2)) = min ((#\<surd>tsb tb1)) (#\<surd>tsb tb2)"
proof -
  { assume "tsbDom\<cdot>tb1 \<noteq> {}"
    moreover
    { assume "(tsbDom\<cdot>tb1 \<noteq> {}) \<and> ((#\<surd>tsb tb2) \<noteq> \<infinity>)"
      hence "tsbDom\<cdot>tb2 \<noteq> {} \<and> tsbDom\<cdot>tb1 \<noteq> {}"
        by (meson tsbtick_insert)
      hence "(#\<surd>tsb tb1) \<le> (#\<surd>tsb tb2) \<and> (#\<surd>tsb tb1) \<le> (#\<surd>tsb tb2) 
                \<and> (tsbDom\<cdot>tb1 \<noteq> {}) 
                \<or> (#\<surd>tsb (tb1 \<uplus> tb2)) = min (#\<surd>tsb tb1) (#\<surd>tsb tb2)"
        by (metis (no_types) assms min.cobounded1 min_def tsbtick_tsbunion2) }
    ultimately have ?thesis
      by (metis (no_types) assms inf_ub min_def tsbtick_tsbunion1) }
  thus ?thesis
    by (metis (no_types) empty_subsetI inf_ub min.absorb2 tsbtick_insert tsbunion_idL)
qed
 
 
lemma tsbtick_single_ch1: assumes "tsb_well [ch2 \<mapsto> ts]"
 shows "#\<surd>tsb [ch2 \<mapsto> ts]\<Omega> = #\<surd> ts"
proof -
  have f1: "{ch2} = tsbDom\<cdot>([ch2 \<mapsto> ts]\<Omega>)"
    by (simp add: assms tsbdom_rep_eq)
  then have f2: "tsbDom\<cdot>([ch2 \<mapsto> ts]\<Omega>) \<noteq> {}"
    by blast
  have f3: "\<forall>t. tsbDom\<cdot>(t::'a TSB) = {} 
              \<or> (\<exists>c. c \<in> tsbDom\<cdot>t \<and> #\<surd> t . c = (LEAST l. l \<in> {#\<surd> t . c |c. c \<in> tsbDom\<cdot>t}))"
    using tsbtick_min_on_channel by blast
  have "tsbDom\<cdot>([ch2 \<mapsto> ts]\<Omega>) \<noteq> {}"
    using f1 by blast
  then obtain cc :: "'a TSB \<Rightarrow> channel" where
    f4: "cc ([ch2 \<mapsto> ts]\<Omega>) \<in> tsbDom\<cdot>([ch2 \<mapsto> ts]\<Omega>) \<and> #\<surd> ([ch2 \<mapsto> ts]\<Omega>) . cc ([ch2 \<mapsto> ts]\<Omega>) 
         = (LEAST l. l \<in> {#\<surd> ([ch2 \<mapsto> ts]\<Omega>) . c |c. c \<in> tsbDom\<cdot>([ch2 \<mapsto> ts]\<Omega>)})"
    using f3 by meson
  obtain tt :: "(channel \<Rightarrow> 'a tstream option) \<Rightarrow> 'a TSB" where
    f5: "[ch2 \<mapsto> ts] = Rep_TSB (tt [ch2 \<mapsto> ts])"
    by (metis (no_types) Rep_TSB_cases assms mem_Collect_eq)
  then have f6: "[ch2 \<mapsto> ts]\<Omega> = tt [ch2 \<mapsto> ts]"
    by (metis Rep_TSB_inverse)
  have "cc ([ch2 \<mapsto> ts]\<Omega>) = ch2"
    using f4 f1 by blast
  then show ?thesis
    using f6 f5 f4 f2 by (simp add: tsbgetch_insert tsbtick_insert)
qed
    
lemma tsbtick_single_ch2: assumes "tsbDom\<cdot>tb = {ch1}"
  shows "#\<surd>tsb tb = #\<surd> (tb . ch1)"
  using assms tsbtickI by fastforce

*)

   
(*

(* ----------------------------------------------------------------------- *)
  section \<open>TSB-fin\<close>
(* ----------------------------------------------------------------------- *)



definition tsb_fin_well :: "(channel \<rightharpoonup> 'm tstream) \<Rightarrow> bool" where
"tsb_fin_well f \<equiv> (\<forall>c \<in> dom f. tsDom\<cdot>(f\<rightharpoonup>c) \<subseteq> ctype c)
           \<and> (\<exists>n. \<forall>c \<in> dom f.  #\<surd>(f\<rightharpoonup>c) = Fin n)"

lemma tsb_fin_exists [simp]: "tsb_fin_well empty"
  by (simp add: tsb_fin_well_def)

typedef ('m :: message) TSB_fin = "{b :: channel \<rightharpoonup> 'm tstream . tsb_fin_well b }"
  using tsb_fin_exists by blast






(* ----------------------------------------------------------------------- *)
  section \<open>TSB-inf\<close>
(* ----------------------------------------------------------------------- *)


  subsection \<open>Definitions on TSB-inf \<close>
(* ----------------------------------------------------------------------- *)

definition tsb_inf_well :: "(channel \<rightharpoonup> 'm tstream) \<Rightarrow> bool" where
"tsb_inf_well f \<equiv> (\<forall>c \<in> dom f. tsDom\<cdot>(f\<rightharpoonup>c) \<subseteq> ctype c)
                \<and> (\<forall>c \<in> dom f. #\<surd>(f\<rightharpoonup>c) = \<infinity>)"


lemma tsb_inf_exists [simp]: "tsb_inf_well empty"
  by (simp add: tsb_inf_well_def)

lemma tsb_inf_adm[simp]: "adm (\<lambda>x. \<forall>c\<in>dom x. #\<surd> x\<rightharpoonup>c = \<infinity>)"
  apply (rule admI)
  apply rule+
  by (simp add: contlub_cfun_arg part_dom_lub part_the_chain part_the_lub)


cpodef ('m :: message) TSB_inf = "{b :: channel \<rightharpoonup> 'm tstream . tsb_inf_well b }"
   using tsb_inf_exists apply blast
  by (simp add: tsb_inf_well_def)

setup_lifting type_definition_TSB_inf


definition tsbiDom :: "'m TSB_inf \<rightarrow> channel set" where
"tsbiDom \<equiv> \<Lambda> x . dom (Rep_TSB_inf x)"

definition TSBi :: "channel set \<Rightarrow> 'm TSB_inf set" where
"TSBi cs = {tb | tb. tsbiDom\<cdot>tb = cs}"

definition tsbiGetCh :: "'m TSB_inf \<rightarrow> channel \<rightarrow> 'm tstream" where
"tsbiGetCh \<equiv> \<Lambda> tbi c. (Rep_TSB_inf tbi) \<rightharpoonup> c"

abbreviation tsbigetch_abbrv :: "'m TSB_inf \<Rightarrow> channel \<Rightarrow> 'm tstream" ("_ . _") where
"tbi  .  c \<equiv> tsbiGetCh\<cdot>tbi\<cdot>c"


definition tsbiUnion :: "'m TSB_inf \<rightarrow> 'm TSB_inf \<rightarrow> 'm TSB_inf"  where
"tsbiUnion \<equiv> \<Lambda> tb1 tb2 . Abs_TSB_inf ((Rep_TSB_inf tb1) ++ (Rep_TSB_inf tb2))"

abbreviation tsbiUnion_abbrv :: "'m TSB_inf \<Rightarrow> 'm TSB_inf \<Rightarrow> 'm TSB_inf" (infixl "\<uplus>" 100) where
"tb1 \<uplus> tb2 \<equiv> tsbiUnion\<cdot>tb1\<cdot>tb2"


 (* Channels not in the channel set are set to "None". *)
definition tsbiRestrict:: "channel set \<Rightarrow> 'm TSB_inf \<rightarrow> 'm TSB_inf" where
"tsbiRestrict cs \<equiv>  \<Lambda> b. Abs_TSB_inf (Rep_TSB_inf b |` cs)"

abbreviation tsbiRestrict_abbr :: "'m TSB_inf \<Rightarrow> channel set \<Rightarrow> 'm TSB_inf" (infix "\<bar>" 65)
where "b\<bar>cs \<equiv> tsbiRestrict cs\<cdot>b"


definition tsbiTTake :: "nat \<Rightarrow> 'm TSB_inf \<rightarrow> 'm TSB" where
"tsbiTTake n \<equiv> \<Lambda> tbi . Abs_TSB (\<lambda>c. (c\<in>(tsbiDom\<cdot>tbi)) \<leadsto> ((tbi . c) \<down> n))"

abbreviation tsbiTTake_abbrv:: "'m TSB_inf \<Rightarrow> nat \<Rightarrow> 'm TSB" ( "_\<down>_") where
"tbi \<down> n \<equiv> tsbiTTake n\<cdot>tbi"



definition tsb2tsbInf :: "'m TSB \<Rightarrow> 'm TSB_inf" where
"tsb2tsbInf tb \<equiv> Abs_TSB_inf (\<lambda>c. (c\<in>tsbDom\<cdot>tb)\<leadsto>(tb  .  c) \<bullet>\<surd> tsInfTick)"

definition tsbInf2tsb :: "'m TSB_inf \<rightarrow> 'm TSB" where
"tsbInf2tsb \<equiv> \<Lambda> tbi.  Abs_TSB (Rep_TSB_inf tbi)"







  subsection \<open>lemmas on TSB-inf \<close>
(* ----------------------------------------------------------------------- *)

lemma [simp]: "tsb_inf_well (Rep_TSB_inf x)"
  using Rep_TSB_inf by blast

lemma [simp]: "Abs_TSB_inf (Rep_TSB_inf y) = y"
  by (simp add: Rep_TSB_inf_inverse)

lemma [simp]: "tsb_inf_well x \<Longrightarrow> Rep_TSB_inf (Abs_TSB_inf x) = x"
by (simp add: Abs_TSB_inf_inverse)

lemma tsbi_infticks[simp]: assumes "c\<in>dom (Rep_TSB_inf tsbi)"
  shows "#\<surd> ((Rep_TSB_inf tsbi)\<rightharpoonup>c) = \<infinity>"
  using Rep_TSB_inf assms tsb_inf_well_def by force

(* an infinite stream can only be a prefix of another if they are both identical, hence the elementwise
   order relation on TSB_inf also becomes the discrete order *)
lemma tsbi_blow_eq [simp]:  fixes x y :: "'m TSB_inf"
  assumes "x \<sqsubseteq> y"
  shows "x = y"
  proof -
  have dom_eq: "dom (Rep_TSB_inf x) = dom (Rep_TSB_inf y)" by (meson assms below_TSB_inf_def le0 part_dom_eq po_class.chain_mono)
  have tsbi_below: "\<And> c. c\<in>dom (Rep_TSB_inf x) \<Longrightarrow> (Rep_TSB_inf x) \<rightharpoonup> c \<sqsubseteq>  (Rep_TSB_inf y) \<rightharpoonup> c"
    by (metis assms below_TSB_inf_def below_option_def below_refl fun_belowD le0 po_class.chain_mono)
  hence "\<And> c. c\<in>dom (Rep_TSB_inf x) \<Longrightarrow> #\<surd>(Rep_TSB_inf x) \<rightharpoonup> c = \<infinity>" by simp
  hence "\<And> c. c\<in>dom (Rep_TSB_inf x) \<Longrightarrow> (Rep_TSB_inf x) \<rightharpoonup> c =  (Rep_TSB_inf y) \<rightharpoonup> c" by (metis ts_approxl tsbi_below tsconc_id)
  thus "x = y" by (metis Rep_TSB_inf_inverse dom_eq part_eq)
qed

instance TSB_inf :: ( message ) discrete_cpo
  apply (intro_classes)
  using tsbi_blow_eq by blast


lemma tsbi_fun_blow [simp]:
  fixes x y :: "'a TSB_inf \<Rightarrow> 'a TSB_inf"
  assumes "x\<sqsubseteq>y"
  shows "x = y"
 using assms fun_belowD by fastforce

lemma tsbi_option_below [simp]:
  fixes x y :: "'a TSB_inf \<rightharpoonup> 'a TSB_inf"
  assumes "x\<sqsubseteq>y"
  shows "x = y"
  using assms below_option_def fun_below_iff by fastforce


lemma tsbi_option_chain_max_in [simp]:
  fixes Y:: "nat \<Rightarrow> ('a TSB_inf \<rightharpoonup> 'b TSB_inf)"
  assumes "chain Y"
  shows "max_in_chain 0 Y"
  apply (rule max_in_chainI)
proof -
  fix j :: nat
  have f1: "\<forall>f t. (\<not> chain f) \<or> chain (\<lambda>n. f n\<rightharpoonup>(t::'a TSB_inf)::'b TSB_inf)"
    by (metis (full_types) part_the_chain)
  have f2: "\<forall>t ta. (t::'b TSB_inf) \<notsqsubseteq> ta \<or> t = ta"
    by (metis tsbi_blow_eq)
  obtain tt :: "('a TSB_inf \<Rightarrow> 'b TSB_inf option) \<Rightarrow> ('a TSB_inf \<Rightarrow> 'b TSB_inf option) \<Rightarrow> 'a TSB_inf" where
    "\<forall>f fa. (dom f \<noteq> dom fa \<or> tt fa f \<in> dom f \<and> f\<rightharpoonup>tt fa f \<noteq> fa\<rightharpoonup>tt fa f) \<or> f = fa"
    by (metis (no_types) part_eq)
  then show "Y 0 = Y j"
    using f2 f1 by (metis assms is_ub_thelub part_dom_eq1)
qed


lemma tsbi_option_chain_finite [simp]:
  fixes Y:: "nat \<Rightarrow> ('a TSB_inf \<rightharpoonup> 'b TSB_inf)"
  assumes "chain Y"
  shows "finite_chain Y"
  using assms finite_chainl1 tsbi_option_chain_max_in by blast


lemma tsbi_option_adm [simp]:
  fixes g:: "('a TSB_inf \<rightharpoonup> 'b TSB_inf) \<Rightarrow> bool"
  shows "adm g"
  apply (rule admI)
  by (metis l42 tsbi_option_chain_finite)




subsubsection \<open>tsbiDom\<close>

thm tsbiDom_def

lemma tsbidom_insert: "tsbiDom\<cdot>x = dom (Rep_TSB_inf x)"
  by (simp add: tsbiDom_def)

lemma tsbidom_rep_eq: "tsb_inf_well tbi \<Longrightarrow> tsbiDom\<cdot>(Abs_TSB_inf tbi) = dom tbi"
by (simp add: tsbidom_insert)


lemma [simp]: "tsb_inf_well (\<lambda>c.(c\<in>cs) \<leadsto> tsInfTick)"
by (simp add: tsb_inf_well_def)

lemma tsbiLeast_dom [simp]: "tsbiDom\<cdot>(Abs_TSB_inf (\<lambda>c.(c\<in>cs) \<leadsto> tsInfTick)) = cs"
by (simp add: tsbiDom_def)

lemma tsbi_dom_ex[simp]: "\<exists>tbi. tsbiDom\<cdot>tbi = cs"
using tsbiLeast_dom by blast

lemma tsbi_dom_ex2 [simp]: "\<exists>b. dom (Rep_TSB_inf b) = cs"
using tsbi_dom_ex tsbidom_insert by fastforce


lemma tsbi_ex[simp]: "TSBi cs \<noteq> {}"
by (simp add: TSBi_def)


subsubsection \<open>tsbiGetCh\<close>

thm tsbiGetCh_def

lemma tsbigetch_insert: "tbi  .  c = (Rep_TSB_inf tbi) \<rightharpoonup> c"
by (simp add: tsbiGetCh_def)

lemma tsbigetch_rep_eq: "tsb_inf_well tbi \<Longrightarrow> (Abs_TSB_inf tbi)  .  c = tbi \<rightharpoonup> c"
by (simp add: tsbiGetCh_def)


lemma tsbi_getch_inf [simp]:
  shows "c\<in>tsbiDom\<cdot>tbi \<Longrightarrow> #\<surd> tbi . c = \<infinity>"
  by (simp add: tsbiGetCh_def tsbiDom_def)

lemma tsbi_getch_type[simp]: "c\<in>tsbiDom\<cdot>tbi \<Longrightarrow> tsDom\<cdot>(tbi  .  c) \<subseteq> ctype c"
apply (simp add: tsbiGetCh_def)
using tsb_inf_well_def tsbidom_insert by fastforce



lemma tsbi_eq: "tsbiDom\<cdot>x = tsbiDom\<cdot>y \<Longrightarrow> (\<And> c. c\<in>tsbiDom\<cdot>x \<Longrightarrow> x . c =y . c) \<Longrightarrow> x=y"
  by (metis (no_types, lifting) Abs_cfun_inverse2 Rep_TSB_inf_inject cont_discrete_cpo part_eq tsbiGetCh_def tsbidom_insert)

lemma tsbi_below: "tsbiDom\<cdot>x = tsbiDom\<cdot>y \<Longrightarrow> (\<And> c. c\<in>tsbiDom\<cdot>x \<Longrightarrow> x . c \<sqsubseteq> y . c) \<Longrightarrow> x\<sqsubseteq>y"
by (metis below_TSB_inf_def part_below tsbidom_insert tsbigetch_insert)





subsubsection \<open>tsbiUnion\<close>

(* tsbUnion produces a welltyped partial-function *)
lemma tsbiunion_well[simp]: assumes "tsb_inf_well b1" and "tsb_inf_well b2"
  shows "tsb_inf_well (b1 ++ b2)"
  apply (simp add: tsb_inf_well_def)
  apply (rule, rule)
   apply (metis (no_types, lifting) Un_iff assms(1) assms(2) map_add_dom_app_simps(1) map_add_dom_app_simps(3) tsb_inf_well_def)
  apply rule
  by (metis (no_types, lifting) Un_iff assms(1) assms(2) map_add_dom_app_simps(1) map_add_dom_app_simps(3) tsb_inf_well_def)


(* insert rule for sbUnion *)
lemma tsbiunion_insert: "(tb1 \<uplus> tb2) = (Abs_TSB_inf (Rep_TSB_inf tb1 ++ Rep_TSB_inf tb2))"
  by (simp add: tsbiUnion_def)

(* if all channels in b1 are also in b2 the union produces b2 *)
lemma tsbiunion_idL:  "tsbiDom\<cdot>tb1\<subseteq>tsbiDom\<cdot>tb2 \<Longrightarrow> tb1 \<uplus> tb2 = tb2"
  by (simp add: Rep_TSB_inf_inverse tsbidom_insert tsbiunion_insert)

(* if b1 and b2 have no common channels, sbUnion is commutative *)
lemma tsbiunion_commutative: "tsbiDom\<cdot>b1 \<inter> tsbiDom\<cdot>b2 = {} \<Longrightarrow> b1\<uplus>b2 = b2\<uplus>b1"
  apply (simp add: tsbiunion_insert)
  by (metis map_add_comm tsbidom_insert)


(* the second argument has priority in sbUnion *)
lemma tsbiunion_getchR [simp]:
  shows "c\<in>tsbiDom\<cdot>b2 \<Longrightarrow> b1\<uplus>b2  .  c = b2  .  c"
  apply (simp add: tsbiunion_insert tsbiGetCh_def )
  by (simp add: map_add_dom_app_simps(1) tsbidom_insert)

lemma tsbiunion_getchL [simp]: "c\<notin>tsbiDom\<cdot>b2 \<Longrightarrow> b1\<uplus>b2  .  c = b1  .  c"
  apply (simp add: tsbiunion_insert tsbiGetCh_def)
  by (metis map_add_dom_app_simps(3) tsbidom_insert)

lemma tsbiunion_dom [simp]: "tsbiDom\<cdot>(tb1 \<uplus> tb2) = tsbiDom\<cdot>tb1 \<union> tsbiDom\<cdot>tb2"
  by (simp add: tsbidom_insert tsbiunion_insert Un_commute)

lemma tsbiunion_assoc [simp]: fixes x y z :: "'m TSB_inf"
  shows "(x \<uplus> y) \<uplus> z = x \<uplus> (y \<uplus> z)"
by (simp add: tsbiunion_insert)






subsubsection \<open>tsbiRes\<close>

lemma [simp]: "tsb_inf_well (Rep_TSB_inf b |` cs)"
  apply (simp add: tsb_inf_well_def)
  by (metis IntD1 Rep_TSB_inf mem_Collect_eq tsb_inf_well_def)

lemma tsbirestrict_insert: "tbi \<bar> cs = Abs_TSB_inf (Rep_TSB_inf tbi |` cs)"
  by (simp add: tsbiRestrict_def)

lemma tsbirestrict_dom [simp]: "tsbiDom\<cdot>(tb \<bar> cs) \<subseteq> cs"
  by (simp add: tsbiRestrict_def tsbidom_insert)

lemma tsbiresrict_dom2 [simp]: "cs \<subseteq> tsbiDom\<cdot>tb \<Longrightarrow> tsbiDom\<cdot>(tb \<bar> cs) = cs"
  apply (simp add: tsbidom_insert tsbiRestrict_def)
  by blast

lemma tsbirestrict_dom3: "tsbiDom\<cdot>(tb \<bar> cs) = tsbiDom\<cdot>tb \<inter> cs"
  by (simp add: tsbidom_insert tsbiRestrict_def)

lemma [simp]: fixes tb :: "'m TSB_inf"
  shows "(tb \<bar> cs1) \<bar> cs2 = tb \<bar> (cs1\<inter>cs2)"
  by (simp add: tsbiRestrict_def)

lemma tsbirestrict_dom2 [simp]: "tsbiDom\<cdot>(tb \<bar> cs) = cs \<Longrightarrow> cs \<subseteq> tsbiDom\<cdot>tb"
  by (auto simp add: tsbidom_insert tsbiRestrict_def)

lemma tsbiRestrict_getch [simp]:  "c \<in> cs \<Longrightarrow> tbi \<bar> cs . c   = tbi . c "
by (simp add: tsbirestrict_insert tsbiGetCh_def)


lemma tsbiunion_restrict3 [simp]: "(tsbiDom\<cdot>y)\<inter>(tsbiDom\<cdot>x) = {} \<Longrightarrow> (x\<uplus>y) \<bar> tsbiDom\<cdot>x = x"
  apply (simp add: tsbidom_insert tsbiRestrict_def tsbiunion_insert)
  by (metis Int_absorb Rep_TSB_inf_inverse map_union_restrict2 restrict_restrict)

lemma tsbiunion_restrict2 [simp]:"(x\<uplus>y) \<bar> tsbiDom\<cdot>y = y"
  by (simp add: tsbiunion_insert tsbidom_insert tsbiRestrict_def)

lemma tsbiunion_restrict [simp]:"(tsbiDom\<cdot>y)\<inter>cs2 = {} \<Longrightarrow> (x\<uplus>y) \<bar> cs2 = x \<bar> cs2"
  by (simp add: tsbiunion_insert tsbirestrict_insert tsbiDom_def)











subsubsection \<open>tsbiTTake\<close>

thm tsbiTTake_def
lemma tsbittake_well[simp]: "tsb_well (\<lambda>c. (c \<in> tsbiDom\<cdot>tbi)\<leadsto>tbi . c \<down> n )"
  apply (rule tsb_wellI)
   apply simp
   by (meson order.trans tsbi_getch_type tsttake_dom)
  (* by (simp add: tsbiGetCh_def tsbidom_insert) *)


lemma tsbittake_getch [simp]: fixes tsbi:: "'m TSB_inf"
  shows "c\<in>tsbiDom\<cdot>tsbi \<Longrightarrow> tsbi \<down> n  .  c = tsbi . c \<down>n"
by (simp add: tsbiTTake_def tsbgetch_insert)

lemma tsbiGetCh_rep_eq: "tsb_inf_well tbi \<Longrightarrow> (Abs_TSB_inf tbi)  .  c = tbi \<rightharpoonup> c "
by (simp add: tsbiGetCh_def)


lemma [simp]: "tsbDom\<cdot>(tbi \<down> n) = tsbiDom\<cdot>tbi"
by (simp add: tsbiTTake_def tsbdom_insert)


lemma tsbiTtake_chain [simp]: fixes tbi :: "'a TSB_inf"
  shows "chain (\<lambda>i. tbi \<down> i)"
  apply (rule chainI)
  apply (rule tsb_below)
   apply simp
  by simp









subsubsection \<open>tsb2tsbInf\<close>
thm tsb2tsbInf_def

lemma [simp]: "tsb_inf_well (\<lambda>c. (c\<in>tsbDom\<cdot>tb)\<leadsto>(tb  .  c) \<bullet> tsInfTick)"
  by (simp add: tsb_inf_well_def tsbgetch_insert)

lemma tsb2tsbInf_dom [simp]: "tsbiDom\<cdot>(tsb2tsbInf tb) = tsbDom\<cdot>tb"
  by (simp add: tsb2tsbInf_def tsbidom_insert)

lemma rep_tsbi_tsb_well [simp]: "tsb_well (Rep_TSB_inf tbi)"
  using Rep_TSB_inf tsb_inf_well_def tsb_well_def by fastforce

lemma tsbinf2tsb_insert: "tsbInf2tsb\<cdot>tbi = Abs_TSB (Rep_TSB_inf tbi)"
  by (simp add: tsbInf2tsb_def)

lemma [simp]: "tsbDom\<cdot>(tsbInf2tsb\<cdot>tbi) =tsbiDom\<cdot>tbi"
  by (simp add: tsbdom_insert tsbinf2tsb_insert tsbidom_insert)

lemma tsbInf2tsb_getch [simp]: "tsbInf2tsb\<cdot>tb  . c = tb .  c"
by (simp add: tsbInf2tsb_def tsbgetch_insert tsbigetch_insert)


lemma tsbiTtake_Lub [simp]: "(\<Squnion>i. (tb\<down>i)) = tsbInf2tsb\<cdot>tb" (is "?L = ?R")
proof(rule tsb_eq)
  have "chain (\<lambda>i. tb\<down> i)" by simp
  hence dom1: "tsbDom\<cdot>(\<Squnion>i. (tb\<down>i)) = tsbDom\<cdot>(tb\<down>0)" using tsbChain_dom_eq2 by blast
  thus "tsbDom\<cdot>?L = tsbDom\<cdot>?R" by simp

  fix c
  assume "c\<in>tsbDom\<cdot>?L"
  hence "c\<in>tsbiDom\<cdot>tb" using dom1 by auto
  hence "?L  .  c = (\<Squnion>i. (tb  .  c \<down> i))" by (simp add: contlub_cfun_arg contlub_cfun_fun)
  hence l_eq: "?L  .  c = tb  .  c" by simp
  have r_eq: "?R  .  c = tb  .  c"
    by (simp add: tsbgetch_rep_eq tsbigetch_insert tsbinf2tsb_insert)
  show "?L  . c = ?R  . c" by (simp add: l_eq r_eq)
qed

lemma tsb_ttake_restrict: fixes tbi :: "'a TSB_inf"
  shows "(tbi \<bar> cs) \<down> i = (tbi \<down> i) \<bar>cs" (is "?L = ?R")
proof(rule tsb_eq)
  show "tsbDom\<cdot> ?L = tsbDom\<cdot>?R" by (simp add: tsbirestrict_dom3 tsresrict_dom3)
  fix c
  assume "c\<in>tsbDom\<cdot>?L"
  hence c_def: "c\<in>cs\<inter>tsbiDom\<cdot>tbi" by (simp add: tsbirestrict_dom3)
  hence c_def2: "c\<in>cs" by simp
  hence c_def3: "c\<in>tsbiDom\<cdot>(tbi \<bar> cs)" using c_def by (simp add: tsbirestrict_dom3)
  hence "?L  . c = tbi  . c \<down>i" by (simp add: c_def c_def2)
  thus "?L  . c = ?R  .  c" using c_def by auto
qed



lemma tsbiSucTake: fixes b1 b2 :: "'a TSB_inf"
  assumes "b1\<down>(Suc n) = b2 \<down> (Suc n)"
  shows "b1 \<down> n = b2 \<down> n"
proof(rule tsb_eq)
  have "tsbDom\<cdot>(b1 \<down> (Suc n)) = tsbDom\<cdot>(b2 \<down> (Suc n))" by (simp add: assms)
  hence dom_eq: "tsbiDom\<cdot>b1 = tsbiDom\<cdot>b2" by simp
  thus "tsbDom\<cdot>(b1 \<down> n) = tsbDom\<cdot>(b2 \<down> n)" by simp

  fix c
  assume "c\<in>tsbDom\<cdot>(b1\<down> n)"
  hence c_def: "c\<in>tsbiDom\<cdot>b1" by simp
  hence c_def2: "c\<in>tsbiDom\<cdot>b2" by (simp add: dom_eq)
  hence "b1\<down> (Suc n)  .  c = b2\<down> (Suc n)  .  c" by (simp add: assms)
  hence "b1  .  c \<down> n = b2  . c \<down> n" using c_def c_def2 by (subst tsSucTake; auto)
  thus " b1\<down>n  .  c = b2\<down>n  .  c" by (simp add: c_def dom_eq c_def2)
qed

*)
  
  
  
  
  
  
  
  

  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  

  
  
  
  




(* OBSOLETE THINGS:





definition tsbMinTick :: "'m TSB \<Rightarrow> 'm TSB \<Rightarrow> lnat" where
"tsbMinTick tb1 tb2 \<equiv> lnmin\<cdot>((#\<surd>tsb tb1))\<cdot>(#\<surd>tsb tb2)"

lemma tsb_tick_eq2: assumes "c1\<in>tsbDom\<cdot>f" and "c2\<in>tsbDom\<cdot>f"
  shows "#\<surd> f . c1 = #\<surd> f . c2"
  using assms by (simp add: tsbdom_insert tsbgetch_insert tsb_tick_eq)




(*Experimentell ... *)

thm tsbTickCount_def

lemma tsbtickcount_cont[simp]: "cont (\<lambda> tb. if tsbDom\<cdot>tb \<noteq> {} then #\<surd>(SOME ts. 
                                      ts \<in> ran (Rep_TSB tb)) else \<infinity>)"
apply (rule contI2)
apply (rule monofunI)
  sorry

lemma tsbtickcount_insert: "tsbTickCount\<cdot>tb = (if tsbDom\<cdot>tb \<noteq> {} then #\<surd>(SOME ts. 
                                                ts \<in> ran (Rep_TSB tb)) else \<infinity>)"
  by (simp add: tsbTickCount_def)

lemma tsbtickcountch_eq1: "\<exists>n. \<forall> c \<in> tsbDom\<cdot>tb . n = #\<surd> (tb . c)"
  by (metis ts_ex_len tsbdom_insert tsbgetch_insert)

lemma tsbtickcountgetch: assumes "c \<in> tsbDom\<cdot>tb"
  shows "#\<surd>tsb tb = #\<surd> (tb . c)"
proof -
  have f0: "tsbDom\<cdot>tb \<noteq> {}"
    using assms by auto

  have f1:"(Rep_TSB tb\<rightharpoonup>c) \<in> ran (Rep_TSB tb)"
    by (metis assms domIff option.exhaust_sel ranI tsbdom_insert)
  have f2: "\<forall> ts \<in> ran (Rep_TSB tb). \<exists> c \<in> tsbDom\<cdot>tb.  ts = (tb . c)"
    by (smt Abs_cfun_inverse2 domI mem_Collect_eq option.sel ran_def tsbDom_def tsbdom_cont 
            tsbgetch_insert)
  hence f3: "\<exists>n. \<forall> ts \<in> ran (Rep_TSB tb). #\<surd> ts = n"
    by (metis ts_ex_len tsbdom_insert tsbgetch_insert)
  show ?thesis
    apply (simp add: tsbTickCount_def tsbgetch_insert, simp add: f0)
    by (metis f1 f3 someI_ex)
qed


lemma "cs \<noteq> {} \<Longrightarrow> #\<surd>tsb (tsbLeast cs) = Fin 0"
apply (simp add: tsbTickCount_def)
apply (simp add:  tsbLeast_def, simp add: optionLeast_def)
apply auto
oops

lemma tsbttakeL_len: assumes "tsbDom\<cdot>tb \<noteq> {}"
 shows "#\<surd>tsb (tsbTTakeL (n) tb) = min (#\<surd>tsb tb) (n)"
proof (cases "n \<noteq> \<infinity>")
  case True
  have f1: "n < \<infinity>"
    by (simp add: True less_le)
  obtain j where f2: "n = Fin j"
    by (metis f1 infI neq_iff)
  obtain c where f3: "c \<in> tsbDom\<cdot>tb"
    using assms by blast
  have f4: "#\<surd>tsb (tsbTTakeL (n) tb) = #\<surd> (tsbTTakeL (n) tb) . c"
    by (rule tsbtickcountgetch, simp add: f3)
  have f5: "(tsbTTakeL (n) tb) . c = tsTakeL\<cdot>n\<cdot>(tb . c)"
    by (simp add: f3)
  have f6: "#\<surd> (tb . c) = #\<surd>tsb tb"
    by (subst tsbtickcountgetch, simp_all add: f3)
  then show ?thesis
    by (simp add: f4 f5)
next
  case False
  then show ?thesis
    by simp
qed

*)
  
      
      
      
      
      
      
      
      
      
      
(*    
      
      
      
(* lengths set is not empty if domain is not empty *)
lemma tsbtick_lengths_ne: assumes "tsbDom\<cdot>tb \<noteq> {}"
  shows "{(#\<surd>ts) | ts. (ts \<in> ran (Rep_TSB tb))} \<noteq> {}"
proof -
  obtain ts where f1:"(ts \<in> ran (Rep_TSB tb))"
    by (metis assms ranI singletonI subsetI subset_singletonD tsbgetchE)
  thus ?thesis
    by auto
qed
  
(* general lemma *)
lemma dom_ran_finite: assumes "finite (dom (f:: channel \<rightharpoonup> 'm tstream))"
  shows "finite (ran f)"
apply (simp add: ran_def)
    oops
  
lemma tsbtick_lengths_finite: assumes "finite (tsbDom\<cdot>tb)"
  shows "finite {(#\<surd>ts) | ts. (ts \<in> ran (Rep_TSB tb))}"
proof -
  have f1: "dom (Rep_TSB tb) = tsbDom\<cdot>tb"
    by (simp add: tsbDom_def)
  have f2: "finite (dom (Rep_TSB tb))"
    by (subst f1, simp only: assms)
  (* have f3: "(ran (Rep_TSB tb)) = {ts}" *)
  have "finite (ran (Rep_TSB tb))"
    apply (simp add: ran_def)
    by (smt assms domI dom_def ex_new_if_finitel1 f1 finite_image_set mem_Collect_eq 
            option.inject tsbgetchE)
  thus ?thesis
    by simp
qed
 
lemma Min_in_lnat [simp]:
  assumes "(A::lnat set) \<noteq> {}"
  shows "Min A \<in> A"
  oops
  
lemma tsbtick_min_in_set: assumes "tsbDom\<cdot>tb \<noteq> {}" and "finite (tsbDom\<cdot>tb)"
  shows "(Min {(#\<surd>ts) | ts. (ts \<in> ran (Rep_TSB tb))}) \<in> {(#\<surd>ts) | ts. (ts \<in> ran (Rep_TSB tb))}"
  by (metis (mono_tags, lifting) Collect_cong Min_in assms(1) assms(2) tsbtick_lengths_finite 
            tsbtick_lengths_ne)

lemma tsbtick_is_min1: assumes "tsbDom\<cdot>tb \<noteq> {}" and "finite (tsbDom\<cdot>tb)" 
                       and  "Min {(#\<surd>ts) | ts. (ts \<in> ran (Rep_TSB tb))} = n"
  shows "\<exists> c. (#\<surd>(tb . c)) = n"
    (* ISAR proof can be generated via sledgehammer *)
  by (smt Collect_cong assms(1) assms(2) assms(3) mem_Collect_eq ran_exists tsbgetch_insert 
          tsbtick_min_in_set)
  
(* general lemma *)
lemma tsb_below_ran_below1: assumes "x \<sqsubseteq> y" and "tsbDom\<cdot>x \<noteq> {}"
  shows "\<forall> ts \<in> ran (Rep_TSB x).(\<exists> ts2\<in> (ran (Rep_TSB y)). (ts) \<sqsubseteq> (ts2))"
proof -
  have f1: "tsbDom\<cdot>y \<noteq> {}"
    using assms(1) assms(2) tsbdom_below by blast
  have f2: "\<forall> c \<in> tsbDom\<cdot>x. x . c \<sqsubseteq> y . c"
    by (simp add: assms(1) monofun_cfun_arg monofun_cfun_fun)
  show ?thesis
    (* ISAR proof generateable via sledgehammer *)
    by (smt assms(1) domI f2 mem_Collect_eq option.simps(1) ran_def tsbdom_below tsbdom_insert 
            tsbgetchE)
qed
  
lemma tsb_below_ran_below2: assumes "x \<sqsubseteq> y" and "tsbDom\<cdot>x \<noteq> {}"
  shows "\<forall> ts \<in> ran (Rep_TSB y).(\<exists> ts2\<in> (ran (Rep_TSB x)). (ts2) \<sqsubseteq> (ts))"
proof -
  have f1: "tsbDom\<cdot>y = tsbDom\<cdot>x"
    using assms(1)  tsbdom_below by blast
  have f2: "\<forall> c \<in> tsbDom\<cdot>y . x . c \<sqsubseteq> y . c"
    using assms(1) monofun_cfun_arg monofun_cfun_fun by blast
  thus ?thesis
    (* ISAR proof generateable via sledgehammer *)
    by (smt domI f1 mem_Collect_eq option.simps(1) ran_def tsbdom_insert tsbgetchE)
qed
  
  (* general lemma *)
lemma tsbgetch_below: assumes "x \<sqsubseteq> y"
  shows "\<forall> c. (x . c) \<sqsubseteq> (y . c)"
    by (simp add: assms monofun_cfun_arg monofun_cfun_fun)
    
(* general lemma *)
lemma lnat_set_min_below: assumes "finite (A:: lnat set)" and "finite (B ::lnat set)" 
                          and "A \<noteq> {}" and "B \<noteq> {}" and "\<forall> a \<in> A . \<exists> b \<in> B.  a \<sqsubseteq> b"
                                                     and "\<forall> b \<in> B. \<exists> a \<in> A. a \<sqsubseteq> b"
  shows "Min A \<sqsubseteq> Min B"
  by (meson Min_in Min_le_iff assms(1) assms(2) assms(3) assms(4) assms(6) lnle_conv)
    
lemma "(\<exists> b \<in> B. P b) = (\<exists> b. b \<in> B \<and> P b)"
  oops
  
lemma "(\<forall>a\<in>{#\<surd> ts |ts. ts \<in> ran (Rep_TSB x)}. P a) =  (\<forall> a \<in> {ts |ts. ts \<in> ran (Rep_TSB x)}. P (#\<surd> a)) "
  by blast
    
lemma tsbtick_tick_set_below: "(\<forall>b\<in>{#\<surd> ts |ts. ts \<in> A}. \<exists>a\<in>{#\<surd> ts |ts. ts \<in> B}. a \<sqsubseteq> b) 
                             = (\<forall>b\<in>{ts |ts. ts \<in> A}. \<exists>a\<in>{ts |ts. ts \<in> B}. (#\<surd> a) \<sqsubseteq> (#\<surd> b))"
  by blast
    
(* belongs to tstickcount *)
lemma tstickcount_below: assumes "a\<sqsubseteq>b"
  shows " (#\<surd> a \<sqsubseteq> #\<surd> b)"
    using assms lnle_def monofun_cfun_arg by blast
   
lemma tsbtick_min_mono_pre1: assumes "x \<sqsubseteq> y" and "tsbDom\<cdot>x \<noteq> {}" and "finite (tsbDom\<cdot>x)"
  shows "(Min {(#\<surd>ts) | ts. (ts \<in> ran (Rep_TSB x))}) \<sqsubseteq> (Min {(#\<surd>ts) | ts. (ts \<in> ran (Rep_TSB y))})"
proof -
  have f1: "tsbDom\<cdot>y = tsbDom\<cdot>x"
    using assms(1) assms(2) tsbdom_below by blast
  moreover
  have f2: "finite (tsbDom\<cdot>y)"
    by (simp add: f1 assms(3))
  moreover
  have f31: "finite {#\<surd> ts |ts. ts \<in> ran (Rep_TSB x)}"
    by (simp add: assms(3) tsbtick_lengths_finite)
  have f32: "finite {#\<surd> ts |ts. ts \<in> ran (Rep_TSB y)}"
    by (simp add: f2 tsbtick_lengths_finite)
  have f41: "{#\<surd> ts |ts. ts \<in> ran (Rep_TSB x)} \<noteq> {}"
    using assms(2) tsbtick_lengths_ne by auto
  have f42: "{#\<surd> ts |ts. ts \<in> ran (Rep_TSB y)} \<noteq> {}"
    using assms(2) f1 tsbtick_lengths_ne by auto
  have f50: "\<forall> x y. (\<forall>a\<in>{#\<surd> ts |ts. ts \<in> x}. \<exists>b\<in>{#\<surd> ts |ts. ts \<in> y}. a \<sqsubseteq> b) = (\<forall>a\<in>{ts |ts. ts \<in> x}. \<exists>b\<in>{ts |ts. ts \<in> y}. (#\<surd> a) \<sqsubseteq> (#\<surd> b))"
    by blast
  have f51: "\<forall>a\<in>{#\<surd> ts |ts. ts \<in> ran (Rep_TSB x)}. \<exists>b\<in>{#\<surd> ts |ts. ts \<in> ran (Rep_TSB y)}. a \<sqsubseteq> b"
    apply (simp only: f50, simp)
     by (meson assms(1) assms(2) lnle_def tsb_below_ran_below1 tstickcount_below)
  have f52: "\<forall>b\<in>{#\<surd> ts |ts. ts \<in> ran (Rep_TSB y)}. \<exists>a\<in>{#\<surd> ts |ts. ts \<in> ran (Rep_TSB x)}. a \<sqsubseteq> b"
    apply (simp only: tsbtick_tick_set_below, simp)
      by (meson assms(1) assms(2) lnle_def tsb_below_ran_below2 tstickcount_below)
  show ?thesis
    apply(rule lnat_set_min_below, simp_all only: f31 f32 f41 f42, simp, simp)
    using f51 apply blast
    using f52 by blast
qed
  
  
  (* tsbtickcount is monotone if tsb domain is finite *)
lemma tsbtick_mono_pre: assumes "x \<sqsubseteq> y" and "finite (tsbDom\<cdot>x)"
  shows "(if tsbDom\<cdot>x \<noteq> {} then Min {(#\<surd>ts) | ts. (ts \<in> ran (Rep_TSB x))} else \<infinity>)
          \<sqsubseteq> (if tsbDom\<cdot>y \<noteq> {} then Min {(#\<surd>ts) | ts. (ts \<in> ran (Rep_TSB y))} else \<infinity>)"
proof (cases "tsbDom\<cdot>x \<noteq> {}")
  case True
  moreover have "tsbDom\<cdot>y = tsbDom\<cdot>x"
    using assms(1) tsbdom_below by blast
  ultimately show ?thesis
    using assms(1) assms(2) tsbtick_min_mono_pre1 by auto
next
  case False
  moreover have "tsbDom\<cdot>y = tsbDom\<cdot>x"
    using assms(1) tsbdom_below by blast
  ultimately show ?thesis
    by simp
qed
  
lemma finite_tsbdom: "finite (tsbDom\<cdot>tb)"  
proof -
  have "finite {c :: channel . True}"
    sorry (* sledgehammer does not find any solution, is the type internally really finite? *)
  thus ?thesis
    using ex_new_if_finitel1 by blast
qed  
  
lemma tsbtick_mono[simp]: "monofun (\<lambda> tb. if tsbDom\<cdot>tb \<noteq> {} then Min {(#\<surd>ts) | ts. (ts \<in> ran (Rep_TSB tb))} else \<infinity>)"
  apply (rule monofunI)
    using finite_tsbdom tsbtick_mono_pre by blast
  
lemma tsbtick_chain: assumes "chain X"
  shows "chain (\<lambda> i. if tsbDom\<cdot>x \<noteq> {} then Min {#\<surd> ts |ts. ts \<in> ran (Rep_TSB (X i))} else \<infinity>)"
proof -
  have f1: "\<forall> i. X i \<sqsubseteq> X (Suc i)"
    by (simp add: assms po_class.chainE)
  have f2: "\<forall> i. finite (tsbDom\<cdot> (X i))"
    by (simp add: finite_tsbdom)
  show ?thesis
    apply (rule chainI)
    by (smt Collect_cong assms empty_iff f1 f2 po_eq_conv tsbChain_dom_eq3 tsb_eq 
            tsbtick_min_mono_pre1)
qed
  
lemma tsbtick_inner_chain: assumes "chain X" 
  shows "chain (\<lambda> i. Min {#\<surd> ts |ts. ts \<in> ran (Rep_TSB (X i))})"  
    sorry
   
lemma assumes "chain Y" and "(Rep_TSB (Lub Y)) \<sqsubseteq> (\<Squnion> i. (Rep_TSB (Y i)))"
  shows "Min {#\<surd> ts |ts. ts \<in> ran (Rep_TSB (Lub Y))} \<le> (\<Squnion>i. Min {#\<surd> ts |ts. ts \<in> ran (Rep_TSB (Y i))})"
proof -
  have "True"
    apply (rule tsb_below)
    
lemma tsbtick_cont_pre: assumes "chain Y" and "\<forall> i .finite (tsbDom\<cdot>(Y i))"
  shows "(if tsbDom\<cdot>(\<Squnion>i. Y i) \<noteq> {} then Min {#\<surd> ts |ts. ts \<in> ran (Rep_TSB (\<Squnion>i. Y i))} else \<infinity>) \<sqsubseteq> (\<Squnion>i. if tsbDom\<cdot>(Y i) \<noteq> {} then Min {#\<surd> ts |ts. ts \<in> ran (Rep_TSB (Y i))} else \<infinity>)"
proof (cases "tsbDom\<cdot>(\<Squnion>i. Y i) \<noteq> {}")
  case True
  hence f1: "\<forall> i. tsbDom\<cdot>(Y i) = tsbDom\<cdot>(\<Squnion>i. Y i)"
    by (simp add: assms(1))
  hence f2: "finite (tsbDom\<cdot>(\<Squnion>i. Y i))"
    using assms(2) by auto
   
  show ?thesis
  proof -
    have f10: "(Rep_TSB (Lub Y)) \<sqsubseteq> (\<Squnion> i. (Rep_TSB (Y i)))"
      by (simp add: assms(1) rep_lub)
    thus ?thesis
      apply (simp only: True f1, simp)
        
        
next
  case False
  hence "\<forall> i. tsbDom\<cdot>(Y i) = {}"
    by (simp add: assms)
  then show ?thesis
    by (simp)
qed
  

  
lemma chain_chain_lub: assumes "chain X" and "chain Y"
  shows "\<Squnion> i. (X (Y i)) = X (\<Squnion> i. Y i)"
    

     
    
lemma tsbtick_cont: "cont (\<lambda> tb. if tsbDom\<cdot>tb \<noteq> {} then Min {(#\<surd>ts) | ts. (ts \<in> ran (Rep_TSB tb))} else \<infinity>)"
proof (rule contI2)
 
*)


end