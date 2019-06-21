theory sbElemv3_alt

imports SBv3
begin

(****************
    Wird nicht verwendet, stattdessen "sbeq" 
******************)

section \<open>sbElem Definition \<close>

fun sbElem_well :: "('c::chan \<Rightarrow> M discr u) \<Rightarrow> bool" where
"sbElem_well f = (\<forall>c. case f c of Iup m \<Rightarrow> (undiscr m)\<in>(ctype (Rep c)) | _ \<Rightarrow> True)"

(*sbElems*)
pcpodef 'c::chan sbElem  ("(_\<^sup>\<surd>)" [1000] 999) = "{f:: ('c::chan \<Rightarrow> M discr u). sbElem_well f}"
  apply auto
  apply (simp add: inst_up_pcpo)  (* TODO: wichtig *)
  sorry


instantiation sbElem:: ("{chan,finite}") chfin
begin
instance
  apply(standard)
  oops
(* end *)

setup_lifting type_definition_sbElem

section \<open>sbElem functions \<close>

(* Magic? *)
definition sbeGetch::"'c \<Rightarrow> 'c\<^sup>\<surd> \<rightarrow> M discr u" where
"sbeGetch c = (\<Lambda> sbe. (Rep_sbElem sbe) c)"

lemma sbhdelem_well:"sbElem_well (\<lambda>c. lshd\<cdot>(sb \<^enum> c))"
  apply(auto)
  apply(case_tac "(sb \<^enum> c) = \<bottom>")
  apply auto
  apply (simp add: inst_up_pcpo)
  sorry

lemma sbhdelem_chain_well:"chain Y \<Longrightarrow> sbElem_well (\<Squnion>i::nat.(\<lambda>c. lshd\<cdot>(Y i  \<^enum>  c)))"
  apply auto
  apply(case_tac "\<exists> i.(Y i \<^enum> c) \<noteq> \<bottom>")
  using sbgetch_ctype_notempty apply auto[1] 
  apply auto
  apply(subgoal_tac "chain (\<lambda>i.(\<lambda>c::'b. lshd\<cdot>(Y i  \<^enum>  c)) )")
  apply (simp add: lub_fun)   
  apply(rule chainI)
  apply(simp add: below_fun_def,auto)
  by (simp add: monofun_cfun_arg po_class.chain_def)

lemma sbhdelem_chain_well:"chain Y \<Longrightarrow> sbElem_well (\<Squnion>i::nat. Rep_sbElem(Abs_sbElem(\<lambda>c. lshd\<cdot>(Y i  \<^enum>  c))))"
  apply auto
  apply(subst Abs_sbElem_inverse)
  apply(case_tac "\<exists> i.(Y i \<^enum> c) \<noteq> \<bottom>")
  using sbgetch_ctype_notempty apply auto[1] 
  apply auto
  apply(subgoal_tac "chain (\<lambda>i.(\<lambda>c::'b. lshd\<cdot>(Y i  \<^enum>  c)) )")
  sorry


lift_definition sbHdElem::"('c)\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<surd>"is
"(\<lambda> sb. Abs_sbElem(\<lambda>c. lshd\<cdot>(sb \<^enum> c)))"
  apply(simp add: cfun_def)
  apply(rule Cont.contI2)
   apply(rule monofunI)
   apply(simp add: below_sbElem_def)
  apply(subst Abs_sbElem_inverse)
  apply simp
  apply(simp add: sbgetch_ctype_notempty) 
  apply(subst Abs_sbElem_inverse)
  apply simp
  apply(simp add: sbgetch_ctype_notempty)
  apply(simp add: below_fun_def)
proof(auto)
  fix x::"'c\<^sup>\<Omega>" and y::"'c\<^sup>\<Omega>" and xa::'c
  assume below:"x\<sqsubseteq> y"
  then have "(x  \<^enum>  xa) \<sqsubseteq> (y  \<^enum>  xa)"
    by (simp add: monofun_cfun_arg)
  then show "lshd\<cdot>(x  \<^enum>  xa) \<sqsubseteq> lshd\<cdot>(y  \<^enum>  xa)" 
    using lshd_eq by fastforce
next
  fix Y::"nat \<Rightarrow> 'c\<^sup>\<Omega>"
  assume chain1:"chain Y"
  assume chain2:"chain(\<lambda>i::nat. Abs_sbElem (\<lambda>c::'c. lshd\<cdot>(Y i  \<^enum>  c)))"
  show "Abs_sbElem (\<lambda>c::'c. lshd\<cdot>((\<Squnion>i::nat. Y i)  \<^enum>  c)) \<sqsubseteq> (\<Squnion>i::nat. Abs_sbElem (\<lambda>c::'c. lshd\<cdot>(Y i  \<^enum>  c)))"
    apply(simp add: below_sbElem_def chain1 contlub_cfun_arg)
    apply(rule fun_belowI)
    apply(subst Abs_sbElem_inverse)
    apply auto
    apply (smt Rep_cfun_strict1 chain1 contlub_cfun_arg lub_eq sbgetch_ctype_notempty stream.sel_rews(1))
    apply(subst lub_sbElem)
    apply (simp add: chain2)
    apply(subst Abs_sbElem_inverse)
    sorry
qed

lift_definition sbe2sb::" 'c\<^sup>\<surd> \<rightarrow> 'c\<^sup>\<Omega>" is
"(\<lambda> sbe. if  (Rep_sbElem sbe) =None then \<bottom> else Abs_sb(\<lambda>c. \<up>((the (Rep_sbElem sbe)) c))) "
  by(simp add: cfun_def)

lift_definition sbEConc::"'c\<^sup>\<surd> \<rightarrow> 'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>" is
"(\<lambda> sbe. sbConc (sbe2sb\<cdot>sbe))"
  by (simp add: cfun_def)

abbreviation sbEConc_abbr :: "'c\<^sup>\<surd> \<Rightarrow> 'c\<^sup>\<Omega> \<Rightarrow> 'c\<^sup>\<Omega>" (infixr "\<bullet>\<^sup>\<surd>" 100) where 
"sbe \<bullet>\<^sup>\<surd> sb \<equiv> sbEConc\<cdot>sbe\<cdot>sb"

section \<open>sbElem lemmata \<close>

lemma assumes "sbLen sb \<noteq> 0" shows "sbEConc\<cdot>(sbHdElem sb)\<cdot>(sbRt\<cdot>sb) = sb"
  oops

end