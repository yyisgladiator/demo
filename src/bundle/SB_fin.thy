(*<*)
theory SB_fin
  imports SB
begin
(*>*)

declare[[show_types]]

section\<open>default sort finite and chan\<close>
default_sort "{finite,chan}"

section\<open> SB functions with finite type \<close>

subsection \<open>Cont version of sbHdElem\_h\<close>
definition sbHdElemWell::"'c\<^sup>\<Omega>  \<Rightarrow> bool" where
"sbHdElemWell  \<equiv> \<lambda> sb. (\<forall>c::'c. sb  \<^enum>  c \<noteq> \<epsilon>)"  



lemma cont_h1: assumes"s\<in>{c::'c. \<forall>i::nat. Y i  \<^enum>  c = \<epsilon>}"
  shows" s\<in>UNIV\<and> s\<notin>{c::'c. \<exists>i::nat. Y i  \<^enum>  c \<noteq> \<epsilon>}"
  
  using assms by auto


lemma cont_h2:assumes"\<exists>s. s\<in>UNIV \<and> s\<notin>{c::'c. \<exists>i::nat. Y i  \<^enum>  c \<noteq> \<epsilon>}"
  shows"{c::'c. \<exists>i::nat. Y i  \<^enum>  c \<noteq> \<epsilon>}\<noteq>UNIV"

  using assms by auto
lift_definition sbHdElem_h_cont::"'c\<^sup>\<Omega> \<rightarrow> ('c\<^sup>\<surd>) u"is
"sbHdElem_h"
  apply(simp add: sbHdElem_h_def)
  apply(intro cont2cont)
  apply(rule Cont.contI2)
   apply(rule monofunI)
  apply auto[1]
  apply (metis minimal monofun_cfun_arg po_eq_conv)
   apply (meson below_shd monofun_cfun_arg)
proof-
  fix Y::"nat \<Rightarrow> 'c\<^sup>\<Omega>"
  assume ch1:"chain Y"
  assume ch2:"chain (\<lambda>i::nat. if \<exists>c::'c. Y i  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y i  \<^enum>  c)))))"

  have "\<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon> \<Longrightarrow> \<exists>c::'c. \<forall>i. (Y i)  \<^enum>  c = \<epsilon>"
    by (metis ch1 is_ub_thelub minimal monofun_cfun_arg po_eq_conv)
  have "adm (\<lambda>sb::'c\<^sup>\<Omega>. \<exists>c::'c. sb \<^enum> c= \<epsilon>)" (*Similar proof in spfstep.thy (automaton project)*)
  proof(rule admI)
    fix Y::"nat \<Rightarrow> 'c\<^sup>\<Omega>"
    assume chain:"chain Y"
  
    assume epsholds:"\<forall>i::nat. \<exists>c::'c. Y i  \<^enum>  c = \<epsilon>"
      have well:"\<forall> i.  \<not> sbHdElemWell (Y i) " 
        by (simp add: epsholds sbHdElemWell_def)
    then have h0:"\<forall>c i. ((Y i) \<^enum> c \<noteq> \<epsilon>) \<longrightarrow> ((\<Squnion>i::nat. Y i)  \<^enum>  c \<noteq> \<epsilon>)"
      by (metis (full_types) chain is_ub_thelub minimal monofun_cfun_arg po_eq_conv)
    then obtain set_not_eps where set_not_eps_def:"set_not_eps = {c::'c. \<exists>i. Y i \<^enum> c \<noteq> \<epsilon>}"
      by simp
    then have h01:"finite set_not_eps"
      by simp
    then have h02:"finite (UNIV - set_not_eps)"
      by simp
    have h1:"\<forall>c\<in>(UNIV - set_not_eps). (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon>"
      by (simp add: chain contlub_cfun_arg set_not_eps_def)
    have h2:"\<forall>c\<in>(set_not_eps). (\<Squnion>i::nat. Y i)  \<^enum>  c \<noteq> \<epsilon>"
      using h0 set_not_eps_def by auto

    have f6: "set_not_eps \<noteq> UNIV"
      apply(simp add: set_not_eps_def )
      apply(subst cont_h2)
      apply(auto)
      apply (rule ccontr)
      proof(simp)
      (*  apply(cases  " Rep  (c::'c) \<in> cEmpty")
      
      using SB.slen_empty_eq Stream.slen_empty_eq apply blast*)
    assume a1: "\<forall>c::'c. \<exists>i::nat. Y i   \<^enum>  c \<noteq> \<epsilon> "
     have f1: "\<And> c::'c.  (\<exists>i::nat. Y i  \<^enum>  c \<noteq> \<epsilon>)"
       by (simp add: a1)
     have f10 : "\<And>i. \<exists> c j. (Y i) \<^enum>  c = \<epsilon> \<and> (Y j) \<^enum>  c \<noteq> \<epsilon>"
          by (simp add: epsholds f1)
     have f12: "\<exists> i. sbHdElemWell (Y i)"      
      apply (rule ccontr)
       apply simp
     proof-

         assume a10: "\<forall>i::nat. \<not> sbHdElemWell (Y i)"
            have f110: "\<And> i::nat. \<not> sbHdElemWell (Y i)"
              by (simp add: a10)
            obtain i where i_def: "\<not> sbHdElemWell (Y i)"
              by (simp add: a10)
            obtain ch_not_eps where ch_not_eps_def: "ch_not_eps = {{i. Y i \<^enum> (ch) \<noteq> \<epsilon>}|ch::'c. True }"
              by blast
            obtain surj_f where surj_f_def: "surj_f = (\<lambda> ch. {i. Y i \<^enum> (ch::'c) \<noteq> \<epsilon>})"
              by simp
          have "ch_not_eps \<subseteq>  surj_f ` ({c::'c | c. True})"
      using ch_not_eps_def surj_f_def  
      by auto
            have ch_not_epsfinite: "finite ch_not_eps"
       
              by (meson \<open>(ch_not_eps::nat set set) \<subseteq> (surj_f::'c \<Rightarrow> nat set) ` {c |c::'c. True}\<close> finite_code finite_surj)
            have ch_not_eps_ele_not_emp: "\<forall> ele \<in> ch_not_eps. ele \<noteq> {}"
            proof rule
              fix ele
              assume a11: "ele \<in> ch_not_eps"
              obtain ch where ch_def: "ele = surj_f ch" 
                using a11 ch_not_eps_def surj_f_def by blast
              obtain j where j_def: "(Y j) \<^enum> ch \<noteq> \<epsilon>"
                using a1  by blast
              then show "ele \<noteq> {}"
                using ch_def surj_f_def by blast
            qed
            have dom_emty_iff:"(ch_not_eps={})  \<longleftrightarrow> (( Rep  (c::'c) \<in> cEmpty) )"
              using ch_not_eps_def
              by (metis (full_types, lifting) Collect_empty_eq_bot Diff_cancel Diff_eq_empty_iff a1 bot_empty_eq cEmpty_def ex_in_conv mem_Collect_eq sbgetch_ctype_notempty set_mp)
            have dom_not_emp_false: "ch_not_eps\<noteq>{} \<Longrightarrow> False"
            proof -
              assume a111: "ch_not_eps\<noteq>{}"
              have "\<forall> ele. ele \<in> ch_not_eps \<longrightarrow> (\<exists> i. i \<in> ele \<and> (\<forall> j \<in> ele. i \<le> j))"
                apply (rule ccontr)
              proof (simp)
                assume a1111: "\<exists>ele::nat set. ele \<in>ch_not_eps \<and>  (\<forall>i::nat. i \<in> ele \<longrightarrow> (\<exists>x::nat\<in>ele. \<not> i \<le> x))"
                obtain ele where ele_def: "ele \<in> ch_not_eps \<and> (\<forall>i::nat. i \<in> ele \<longrightarrow> (\<exists>x::nat\<in>ele. \<not> i \<le> x))"
                  using a1111 by blast
                obtain the_ch where the_ch_def: "ele = surj_f the_ch"
                  using ch_not_eps_def ele_def surj_f_def by blast
                have ele_def2: "ele = {i. Y i \<^enum> the_ch \<noteq> \<epsilon>}"
                  using surj_f_def the_ch_def by blast
                obtain the_i where the_i_def: "the_i \<in> ele"
                  using ch_not_eps_ele_not_emp ele_def by auto
                obtain the_subs where the_subst_def: "the_subs = {i. i \<le> the_i \<and> Y i \<^enum> the_ch \<noteq> \<epsilon>}"
                  by simp
                have the_subs_subs: "the_subs \<subseteq> ele"
                  apply (simp add: the_subst_def ele_def2)
                  apply rule
                  by simp
                have the_min: "\<forall> i \<in> the_subs. Min the_subs \<le> i"
                  by (simp add: the_subst_def)
                have the_min_in_subs: "Min the_subs \<in> the_subs"
                  apply (rule Min_in)
                  apply (simp add: the_subst_def)
                  using ele_def2 the_i_def the_subst_def by blast
                then have the_min_in: "Min the_subs \<in> ele"
                  using the_subs_subs by auto
                have the_min_min: "\<forall> i \<in> ele. Min the_subs \<le> i"
                  apply rule
                  apply (case_tac "i \<le> the_i")
                  using ele_def2 the_min the_subst_def apply blast
                  using the_min_in_subs the_subst_def by auto
                show False
                  using ele_def the_min_in the_min_min by auto
              qed
              then have "\<And> ele. ele \<in> ch_not_eps \<Longrightarrow> (\<exists> i. i \<in> ele \<and> (\<forall> j \<in> ele. i \<le> j))"
                by blast
              then have "\<And> ele. ele \<in> ch_not_eps \<Longrightarrow> (\<exists>! i. i \<in> ele \<and> (\<forall> j \<in> ele. i \<le> j))"
                using le_antisym by blast
              obtain finite_ch_n_eps 
                where min_i_ch_def: "finite_ch_n_eps = {the_i | the_i ele. ele \<in> ch_not_eps \<and> (\<forall> i \<in> ele. the_i \<le> i) \<and> the_i \<in> ele}"
                by simp
              obtain bla::"nat set \<Rightarrow> nat set" where bla_def: "bla = (\<lambda> da_set. {the_i. (\<forall> i \<in> da_set. the_i \<le> i) \<and> the_i \<in> da_set})"
                by simp
              have "\<forall> da_set \<in> ch_not_eps. \<exists>! i \<in> da_set. bla da_set = {i}"
              proof rule
                fix da_set
                assume bla: "da_set \<in> ch_not_eps"
                obtain the_i where the_i_def: "the_i \<in> da_set" and the_i_def2: "(\<forall> j \<in> da_set. the_i \<le> j)"
                  using \<open>\<And>ele::nat set. ele \<in> (ch_not_eps::nat set set) \<Longrightarrow> \<exists>i::nat. i \<in> ele \<and> (\<forall>j::nat\<in>ele. i \<le> j)\<close> bla by blast
                have "the_i \<in> bla da_set"
                  using \<open>(bla::nat set \<Rightarrow> nat set) = (\<lambda>da_set::nat set. {the_i::nat. (\<forall>i::nat\<in>da_set. the_i \<le> i) \<and> the_i \<in> da_set})\<close> the_i_def the_i_def2 by blast
                have "\<forall> i \<in> bla da_set. i = the_i"
                  by (simp add: \<open>(bla::nat set \<Rightarrow> nat set) = (\<lambda>da_set::nat set. {the_i::nat. (\<forall>i::nat\<in>da_set. the_i \<le> i) \<and> the_i \<in> da_set})\<close> eq_iff the_i_def the_i_def2)
                show "\<exists>!i::nat. i \<in> da_set \<and> bla da_set = {i}"
                  apply (rule ex_ex1I)
                   apply (rule_tac x ="the_i" in exI)
                   apply rule
                    apply (simp add: the_i_def)
                   apply rule
                    apply (simp add: \<open>\<forall>i::nat\<in>(bla::nat set \<Rightarrow> nat set) (da_set::nat set). i = (the_i::nat)\<close> subsetI)
                   apply (simp add: \<open>(the_i::nat) \<in> (bla::nat set \<Rightarrow> nat set) (da_set::nat set)\<close>)
                  by auto
              qed
              obtain min_set_set::"nat set" where min_set_set_def: "min_set_set = {THE i. i \<in> bla da_set | da_set. da_set \<in> ch_not_eps}"
                by simp
              have i_max_is_max: "\<forall> ch::'c. \<exists> i . (i \<in> min_set_set) \<longrightarrow> Y i \<^enum> ch \<noteq> \<epsilon>"
              proof  rule
                fix ch
                
                obtain ch_set where ch_set_def: "ch_set = surj_f ch"
                  by simp
                obtain the_set where the_st_def: "the_set = bla ch_set"
                  by simp
                have ch_set_in_ch_not_eps: "ch_set \<in> ch_not_eps"
                  apply (simp add: ch_not_eps_def)
                  using  ch_set_def surj_f_def by blast
                obtain the_min where the_min_def: "the_min \<in> ch_set \<and> (\<forall> j \<in> ch_set. the_min \<le> j)"
                  using \<open>\<And>ele::nat set. ele \<in> (ch_not_eps::nat set set) \<Longrightarrow> \<exists>i::nat. i \<in> ele \<and> (\<forall>j::nat\<in>ele. i \<le> j)\<close> ch_set_in_ch_not_eps by auto
        
                have "bla ch_set = {the_min}"
                  using bla_def the_min_def by force
                then have "the_min \<in> bla ch_set"
                  by simp
                have "\<And> i. i \<in> bla ch_set \<Longrightarrow> i = the_min"
                  using \<open>(bla::nat set \<Rightarrow> nat set) (ch_set::nat set) = {the_min::nat}\<close> by auto
                then have "(THE i::nat. i \<in> bla ch_set) = the_min"
                  using \<open>(the_min::nat) \<in> (bla::nat set \<Rightarrow> nat set) (ch_set::nat set)\<close> by blast
                then have "the_min \<in> min_set_set"
                  apply (simp add: min_set_set_def)
                  apply (rule_tac x="ch_set" in exI)
                  apply rule defer
                   apply (simp add: ch_set_in_ch_not_eps)
                  by simp
                then show " \<exists>i::nat. i \<in> min_set_set \<longrightarrow> Y i  \<^enum> ch \<noteq> \<epsilon>"
                  apply (rule_tac x=the_min in exI)
                  apply simp
                  using ch_set_def mem_Collect_eq surj_f_def the_min_def by blast
              qed
              have "finite min_set_set"
                by (simp add: ch_not_epsfinite min_set_set_def)
              obtain the_max where the_max_def: "the_max = Max min_set_set"
                by simp
              have "the_max \<in> min_set_set"
  
                apply (subst the_max_def)
                apply (rule Max_in)
                 apply (simp add: \<open>finite (min_set_set::nat set)\<close>)
                using a111 min_set_set_def by auto
              have "\<exists> i. sbHdElemWell (Y i)"
              proof (rule_tac x="the_max" in exI, simp add: sbHdElemWell_def, rule)
                fix c::'c 
                
                obtain the_set where the_set_def: "the_set = surj_f c"
                  by simp
                have "the_set \<in> ch_not_eps"
                  using ch_not_eps_def surj_f_def the_set_def by auto
                then obtain the_min where the_min_def: "the_min \<in> the_set \<and> (\<forall> j \<in> the_set. the_min \<le> j)"
                  using \<open>\<forall>ele::nat set. ele \<in> (ch_not_eps::nat set set) \<longrightarrow> (\<exists>i::nat. i \<in> ele \<and> (\<forall>j::nat\<in>ele. i \<le> j))\<close> by blast
                have "bla the_set = {the_min}"
                  using bla_def the_min_def by force
                then have "the_min \<in> bla the_set"
                  by simp
                have "\<And> i. i \<in> bla the_set \<Longrightarrow> i = the_min"
                  using \<open>(bla::nat set \<Rightarrow> nat set) (the_set::nat set) = {the_min::nat}\<close> by auto
                then have "(THE i::nat. i \<in> bla the_set) = the_min"
                  using \<open>(the_min::nat) \<in> (bla::nat set \<Rightarrow> nat set) (the_set::nat set)\<close> by blast
                then have "the_min \<in> min_set_set"
                  apply (simp add: min_set_set_def)
                  apply (rule_tac x="the_set" in exI)
                  apply rule defer
                  apply (simp add: \<open>(the_set::nat set) \<in> (ch_not_eps::nat set set)\<close>)
                  by simp
                then have "the_min \<le> the_max"
                  by (simp add: \<open>finite (min_set_set::nat set)\<close> the_max_def)
                then have "Y the_min \<sqsubseteq> Y the_max"
               
                  by (simp add: chain po_class.chain_mono)
                have "Y the_min \<^enum> c \<noteq> \<epsilon>"
                  using surj_f_def the_min_def the_set_def by blast
                then show "Y the_max  \<^enum>  c \<noteq> \<epsilon>"
                  using \<open>(the_min::nat) \<le> (the_max::nat)\<close>  order_class.order.antisym 
                  by (metis \<open>(Y::nat \<Rightarrow> 'c\<^sup>\<Omega>) (the_min::nat) \<sqsubseteq> Y (the_max::nat)\<close> bottomI monofun_cfun_arg)
              qed
              then show False
                by (simp add: a10)
            qed
            then show False
              apply (case_tac "ch_not_eps={}")
           
              using ch_not_eps_def apply blast
           
              by simp 
              qed
     show False
  
       by (meson f12 well epsholds sbHdElemWell_def)
   qed 
      
    then show "\<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon>"
      using h1 by blast
  qed
  then have "\<forall>i::nat. \<exists>c::'c. Y i  \<^enum>  c = \<epsilon> \<Longrightarrow> \<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon>"
    apply(rule admD)
    by(simp_all add: ch1)
  then have finiteIn:"\<forall>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c \<noteq> \<epsilon> \<Longrightarrow> \<exists>i. \<forall>c::'c. (Y i) \<^enum> c \<noteq> \<epsilon>"
    by blast
  then show "(if \<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd ((\<Squnion>i::nat. Y i)  \<^enum>  c))))) \<sqsubseteq>
       (\<Squnion>i::nat. if \<exists>c::'c. Y i  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y i  \<^enum>  c)))))"
  proof(cases "\<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon>")
    case True
    then show ?thesis
      by simp
  next
    case False
    have ch3:"\<And>c. chain (\<lambda>i. Y i  \<^enum>  c)"
      by (simp add: ch1)
    obtain n where n_def:"\<forall>c::'c. (Y n) \<^enum> c \<noteq> \<epsilon>"
      using False finiteIn by auto
    then have shd_eq:"\<And>i. i\<ge>n \<Longrightarrow> (\<lambda>c::'c. shd (Y i  \<^enum>  c)) = (\<lambda>c::'c. shd (Y n  \<^enum>  c))"
      apply(subst fun_eq_iff)
      apply auto
      apply(rule below_shd_alt,auto)
      by (simp add: ch1 monofun_cfun_arg po_class.chain_mono)
    have h1:"\<forall>i\<ge>n. (if \<exists>c::'c. Y i  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y i  \<^enum>  c)))))
                = Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c))))"
      apply(auto)
      apply (metis ch1 minimal monofun_cfun_arg n_def po_class.chain_mono po_eq_conv)
      using shd_eq by presburger
    have h2:"(if \<exists>c::'c. (\<Squnion>i::nat. Y i)  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd ((\<Squnion>i::nat. Y i)  \<^enum>  c))))) \<sqsubseteq> Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c))))"
      apply(simp add: False)
      by (metis below_shd ch1 is_ub_thelub monofun_cfun_arg n_def)
    have h3:"(if \<exists>c::'c. Y n  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c))))) \<sqsubseteq> (\<Squnion>i::nat. if \<exists>c::'c. Y i  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y i  \<^enum>  c)))))"
      using below_lub ch2 by blast
    have h3_h:"(if \<exists>c::'c. Y n  \<^enum>  c = \<epsilon> then \<bottom> else Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c))))) = Iup (Abs_sbElem (Some (\<lambda>c::'c. shd (Y n  \<^enum>  c))))"
      by(simp add: n_def)
    then show ?thesis
      using h2 h3 by auto
  qed
qed

subsection\<open>sb\_cases definition\<close>

definition sb_case::"('cs\<^sup>\<surd> \<Rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'a::pcpo) \<rightarrow> 'cs\<^sup>\<Omega> \<rightarrow> 'a" where
"sb_case \<equiv> \<Lambda> k sb. fup\<cdot>(\<Lambda> sbe. k sbe\<cdot>(sbRt\<cdot>sb))\<cdot>(sbHdElem_h_cont\<cdot>sb)"

lemma sb_case_cont:"cont (\<lambda>sb. \<Lambda> k. fup\<cdot>(\<Lambda> sbe. k\<cdot>sbe\<cdot>(sbRt\<cdot>sb))\<cdot>(sbHdElem_h_cont\<cdot>sb))"
  by simp


lemma sb_cases_bot:"\<not>(chIsEmpty (TYPE ('cs))) \<Longrightarrow> sb_case\<cdot>f\<cdot>\<bottom> = \<bottom>"
  sorry

lemma sb_cases_sbe[simp]:"sb_case\<cdot>f\<cdot>(sbECons sbe\<cdot>sb) = f sbe\<cdot>sb"
  sorry

section\<open>Datatype Konstruktor\<close>

(* FYI: the old approach from v2 to create the datatype is not really reusable, 
  because: 
      lift_definition elem_raw_i :: "int \<Rightarrow> ndaExampleMessage sbElem" is
  Thats an old "single-channel" setter...
  One has to replace the "ndaExampleMessage" with a "chan"... but which?
  There can only be ONE channel in the replacement! ! !
  But what if the channel-datatype of the component has 2 or more channels?
*)

text \<open>Motivation: I HATE freemarker and other templates. 
  And the workflow sucks. The generator people have no idea about isabelle, 
  feature-request take FOREVER and then it might not work in every case\<close>

text\<open>Goal: Move the heavy-stuff from the Generator to Isabelle.
  Pretty much every proof should be done in Isabelle, the generator
  can still create datatypes, functions and so on\<close>

text\<open>Implementation: Is using Locales... \<close>


text \<open>\<open>'a\<close> should be interpreted as a tuple. The goal of this local is to create a
  bijective mapping from \<open>'a\<close> to \<open>'cs\<close>.
  The user can freely choose \<open>'a\<close>, hence he will not use the datatype \<open>M\<close>. 
  for example \<open>'a = (nat \<times> bool)\<close> which maps to a bundle with one bool-channel and one nat-channel\<close>
locale sbeGen =
  fixes lConstructor::"'a::countable \<Rightarrow> 'cs::{chan, finite} \<Rightarrow> M"
  assumes c_well: "\<And>a. \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> sbElem_well (Some (lConstructor a))"
      and c_inj: "\<not>chIsEmpty TYPE ('cs) \<Longrightarrow> inj lConstructor" 
      and c_surj: "\<And>sbe. \<not>chIsEmpty TYPE ('cs) \<Longrightarrow> sbElem_well (Some sbe) \<Longrightarrow> sbe\<in>range lConstructor" (* Schöner? *)
      and c_empty: "chIsEmpty TYPE ('cs) \<Longrightarrow> is_singleton(UNIV::'a set)"
begin

lift_definition setter::"'a \<Rightarrow> 'cs\<^sup>\<surd>" is 
  "if(chIsEmpty TYPE ('cs)) then (\<lambda>_. None) else Some o lConstructor"
  using c_well sbtypeempty_sbewell by auto

definition getter::"'cs\<^sup>\<surd> \<Rightarrow> 'a" where
"getter sbe = (case (Rep_sbElem sbe) of None \<Rightarrow> (SOME x. True) | 
      Some f \<Rightarrow> (inv lConstructor) f)" (* geht was anderes als "SOME x"? *)

lemma get_set[simp]: "getter (setter a) = a"
  unfolding getter_def
  apply (simp add: setter.rep_eq c_inj c_empty)
  by (metis UNIV_I c_empty is_singletonE singleton_iff)

lemma set_inj: "inj setter"
  by (metis get_set injI)

lemma set_surj: "surj setter"
  unfolding setter_def
  apply(cases "\<not>(chIsEmpty(TYPE('cs)))")
proof(simp add: surj_def,auto)
  fix y::"'cs\<^sup>\<surd>"
  assume chnEmpty:"\<not> chIsEmpty TYPE('cs)"
  obtain f where f_def:"Rep_sbElem y=(Some f)"
    using chnEmpty sbtypenotempty_fex by auto
  then obtain x where x_def:"f = lConstructor x"
    by (metis c_inj c_surj f_the_inv_into_f sbelemwell2fwell chnEmpty)
  then show "\<exists>x::'a. y = Abs_sbElem (Some (lConstructor x))"
    by (metis Rep_sbElem_inverse f_def)
qed 

lemma set_bij: "bij setter"
  by (metis bijI inj_onI sbeGen.get_set sbeGen_axioms set_surj)

lemma get_inv_set: "getter = (inv setter)"
  by (metis get_set set_surj surj_imp_inv_eq)

lemma set_get[simp]: "setter (getter sbe) = sbe"
  apply(simp add: get_inv_set)
  by (meson bij_inv_eq_iff set_bij)

lemma "getter A = getter B \<Longrightarrow> A = B"
  by (metis set_get)

fixrec setterSB::"'a stream \<rightarrow> 'cs\<^sup>\<Omega>" where
"setterSB\<cdot>((up\<cdot>l)&&ls) = (setter (undiscr l)) \<bullet>\<^sup>\<surd> (setterSB\<cdot>ls)" 

lemma settersb_unfold:"setterSB\<cdot>(\<up>a \<bullet> s) = (setter a) \<bullet>\<^sup>\<surd> setterSB\<cdot>s"
  unfolding setterSB_def
  apply(subst fix_eq)
  apply simp 
  apply(subgoal_tac "\<exists>l. \<up>a \<bullet> s = (up\<cdot>l)&&s")
  apply auto 
  apply (metis (no_types, lifting) lshd_updis stream.sel_rews(4) undiscr_Discr up_inject)
  by (metis lscons_conv)

lemma settersb_emptyfix:"chIsEmpty (TYPE ('cs)) \<Longrightarrow> setterSB\<cdot>s = \<bottom>"
  by simp

lemma settersb_epsbot:"setterSB\<cdot>\<epsilon> = \<bottom>"
  apply(simp add: setterSB_def)
  apply(subst fix_eq)
  by auto

(* TODO : Dokumentireen! *)
definition getterSB::"'cs\<^sup>\<Omega> \<rightarrow> 'a stream" where
"getterSB \<equiv> fix\<cdot>(\<Lambda> h. sb_case\<cdot>(\<lambda>sbe. \<Lambda> sb. updis (getter sbe) && h\<cdot>sb))"

lemma gettersb_unfold:"getterSB\<cdot>(sbe \<bullet>\<^sup>\<surd> sb) = \<up>(getter sbe) \<bullet> getterSB\<cdot>sb"
  unfolding getterSB_def
  apply(subst fix_eq)
  apply simp
  by (simp add: lscons_conv)

lemma gettersb_emptyfix:"chIsEmpty (TYPE ('cs)) \<Longrightarrow> getterSB\<cdot>sb = \<up>(getter (Abs_sbElem None)) \<bullet> getterSB\<cdot>sb"
  by (metis(full_types) gettersb_unfold sbtypeepmpty_sbbot)

lemma gettersb_realboteps:"\<not>(chIsEmpty (TYPE ('cs))) \<Longrightarrow> getterSB\<cdot>\<bottom> = \<epsilon>"
  unfolding getterSB_def
  apply(subst fix_eq)
  by (simp add: sb_cases_bot)

lemma assumes "chIsEmpty (TYPE ('cs))"
  shows "(getterSB\<cdot>sb) = (sinftimes(\<up>(a)))"
  apply(insert assms,subst gettersb_emptyfix,simp) 
  using gettersb_emptyfix s2sinftimes c_empty
  by (metis (mono_tags) get_set sbtypeepmpty_sbenone)
  
 (* TODO; warning entfernen. abbreviation-prioritäten für \<infinity>?*)

lemma "sbLen (setterSB\<cdot>s) = #s"
  oops(* gilt nicht für chIsEmpty *)

lemma "a \<sqsubseteq> getterSB\<cdot>(setterSB\<cdot>a)"
  apply(induction a rule: ind)
  apply(auto)
  apply (simp add: gettersb_unfold settersb_unfold)
  by (simp add: monofun_cfun_arg)

lemma getset_eq:"\<not>chIsEmpty (TYPE ('cs)) \<Longrightarrow> getterSB\<cdot>(setterSB\<cdot>a) = a"
  apply(induction a rule: ind)
  apply(auto)
  apply (simp add: gettersb_realboteps settersb_epsbot)
  by (simp add: gettersb_unfold settersb_unfold)

lemma "setterSB\<cdot>(getterSB\<cdot>sb) \<sqsubseteq> sb"
  apply(induction sb)
  apply auto
  apply(cases "chIsEmpty(TYPE('cs))")
  apply (metis (full_types)minimal sbtypeepmpty_sbbot)
  apply(simp add: sbIsLeast_def)
  oops
 
lemma setget_eq:"(\<forall>c. #(sb \<^enum> c) = k) \<Longrightarrow>setterSB\<cdot>(getterSB\<cdot>sb) = sb"
  apply(induction sb arbitrary: k)
  apply auto
  apply(rule adm_imp)
     apply auto 
  apply(rule admI)
  defer
  apply(case_tac "chIsEmpty (TYPE ('cs))")
  apply (metis (full_types)sbtypeepmpty_sbbot)
    apply(simp add: sbIsLeast_def)
  apply(subgoal_tac "k = 0",auto)
     apply (metis gettersb_realboteps sb_eqI sbgetch_bot settersb_epsbot)
    defer
    apply(subst gettersb_unfold)
    apply(subst settersb_unfold,simp)
  apply(subgoal_tac "\<And>c. #(sb \<^enum> c) \<le> #(sbe \<bullet>\<^sup>\<surd> sb  \<^enum>  c)",auto)
  oops  (* Nur für gleichlange ströme *)

fun setterList::"'a list \<Rightarrow> 'cs\<^sup>\<Omega>" where
"setterList [] = \<bottom>" |
"setterList (l#ls) = (setter l) \<bullet>\<^sup>\<surd> (setterList ls)" 


end

locale sbGen = 
  fixes lConstructor::" 'a::pcpo \<Rightarrow> 'cs::chan  \<Rightarrow> M stream"
  assumes c_type: "\<And>a c. sValues (lConstructor a c) \<subseteq> ctype (Rep c)"
    and c_inj: "inj lConstructor"
    and c_surj: "\<And>f. sb_well f \<Longrightarrow> f\<in>range lConstructor" (* Schöner? *)
begin

lift_definition setter::"'a \<Rightarrow> ('cs::chan)\<^sup>\<Omega>"is"lConstructor"
  by (simp add: c_type sb_well_def)

definition getter::"'cs\<^sup>\<Omega> \<Rightarrow> 'a" where
"getter= (inv lConstructor) o  Rep_sb"

lemma get_set[simp]: "getter (setter a) = a"
  unfolding getter_def
  by (simp add: setter.rep_eq c_inj)  

lemma set_inj: "inj setter"
  by (metis get_set injI)

lemma set_surj: "surj setter"
  unfolding setter_def
proof(simp add: surj_def,auto)
  fix y::"'cs\<^sup>\<Omega>"
 obtain f where f_def:"Rep_sb y=f"
   by simp
 then obtain x where x_def:"f = lConstructor x"
    by (metis c_inj c_surj f_the_inv_into_f sbwell2fwell)
  then show "\<exists>x::'a. y = Abs_sb (lConstructor x)" 
    by (metis Rep_sb_inverse f_def)
qed

lemma set_bij: "bij setter"
  using bij_betw_def set_inj set_surj by auto

lemma get_inv_set: "getter = (inv setter)"
  by (metis get_set set_surj surj_imp_inv_eq)

lemma set_get[simp]: "setter (getter sbe) = sbe"
  apply(simp add: get_inv_set)
  by (meson bij_inv_eq_iff set_bij)

lemma "getter A = getter B \<Longrightarrow> A = B"
  by (metis set_get)

end

end
