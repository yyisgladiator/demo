theory SB_CaseStudy
imports  "../SB"

begin                               




(* ----------------------------------------------------------------------- *)
  section \<open>Definition of some Stream Bundles\<close>
(* ----------------------------------------------------------------------- *)


(* first the Datatype definition *)

datatype M = Nat nat ("\<N> _" )  | Bool bool ("\<bool> _")

abbreviation abrev_invNat :: "M \<Rightarrow> nat" ("\<inverse>\<N>") where
"\<inverse>\<N> m \<equiv> inv Nat m"

abbreviation abrev_invBool :: "M \<Rightarrow> bool" ("\<inverse>\<bool>") where
"\<inverse>\<bool> m \<equiv> inv Bool m"

instance M :: countable
by countable_datatype

instantiation M :: message 
begin
  fun ctype_M where 
  "ctype_M c1 = range Nat" |
  "ctype_M c2 = range Nat" |
  "ctype_M c3 = range Nat"


  instance
  by(intro_classes)
end
setup_lifting datatype_definition_M
(* empty 'm SB *)
lift_definition stB0 :: "'m SB" is "empty"
by (simp add: sb_well_def)

lift_definition stB1 :: "M SB" is "([c1\<mapsto><[\<N> 1,\<N> 2,\<N> 3,\<N> 4]>, c2\<mapsto><[\<N> 5,\<N> 6,\<N> 7,\<N> 8]>])"
by(simp add: sb_well_def)

lift_definition stB2 :: "M SB" is "([c2\<mapsto><[\<N> 42]>, c3\<mapsto>\<epsilon>])"
by(simp add: sb_well_def)

(* stB3 is the union of stB1 and stB2 *)
lift_definition stB3:: "M SB" is  
  "([c1\<mapsto><[\<N> 1,\<N> 2,\<N> 3,\<N> 4]>, c2\<mapsto><[\<N> 5,\<N> 6,\<N> 7,\<N> 8]>, c3\<mapsto>\<epsilon>])"
by(simp add: sb_well_def)



(* ----------------------------------------------------------------------- *)
  section \<open>Use Cases with M SB definitions\<close>
(* ----------------------------------------------------------------------- *)


(* ----------------------------------------------------------------------- *)
  subsection \<open>sbDom\<close>
(* ----------------------------------------------------------------------- *)

lemma "sbDom\<cdot>stB0 = {}"
  apply(simp add: sbdom_insert stB0.rep_eq)
done

lemma "sbDom\<cdot>stB1 = {c1, c2}"
apply(simp add:stB1.rep_eq sbdom_insert)
by blast




(* ----------------------------------------------------------------------- *)
  subsection \<open>sbGetCh\<close>
(* ----------------------------------------------------------------------- *)

lemma "(stB0 . c) = the None"
by (simp add: sbgetch_insert stB0.rep_eq)

lemma "(stB1 . c1) = <[\<N> 1,\<N> 2,\<N> 3,\<N> 4]>" 
by(simp add: sbgetch_insert stB1.rep_eq)




(* ----------------------------------------------------------------------- *)
  subsection \<open>sbUp\<close>
(* ----------------------------------------------------------------------- *)


lemma "\<up>stB1 . c1 = <[\<N> 1, \<N> 2, \<N> 3, \<N> 4]>"
apply(simp add: sbdom_insert stB1.rep_eq )
by(simp add: sbgetch_insert stB1.rep_eq)

lemma "\<up>stB1 . c3 = \<epsilon>"
by(simp add: sbup_insert sbdom_insert stB1.rep_eq sbgetch_insert sb_well_def)



(* sbRemCh *)

lemma "sbRemCh\<cdot>stB1\<cdot>c1 = ([c2\<mapsto><[\<N> 5,\<N> 6,\<N> 7,\<N> 8]>])\<Omega>"
by(simp add: sbremch_insert stB1.rep_eq sbrestrict_insert)

lemma "sbRemCh\<cdot>stB1\<cdot>c4 = stB1"
apply(simp add: sbremch_insert stB1.rep_eq sbrestrict_insert)
by(simp add: stB1_def)


(* sbSetCh *)
lemma "((sbSetCh\<cdot>stB1) c1 (<[\<N> 1]>)) = ([c1\<mapsto><[\<N> 1]>, c2\<mapsto><[\<N> 5,\<N> 6,\<N> 7,\<N> 8]>])\<Omega> "
by (simp add: fun_upd_twist sbsetch_insert sbunion_insert stB1.rep_eq sb_well_def)

lemma "((sbSetCh\<cdot>stB1) c3 (<[\<N> 1]>)) = ([c1\<mapsto><[\<N> 1,\<N> 2,\<N> 3,\<N> 4]>, c2\<mapsto><[\<N> 5,\<N> 6,\<N> 7,\<N> 8]>, c3\<mapsto><[\<N> 1]>])\<Omega> "
by (simp add: sbsetch_insert sbunion_insert stB1.rep_eq sb_well_def)


(* sbUnion *)
lemma "b \<uplus> b = b"
by simp

lemma "stB0 \<uplus> stB1 = stB1 "
by(simp add: sbUnion_def Rep_SB_inverse stB0.rep_eq)

lemma "stB1 \<uplus> stB0 = stB1 "
apply(simp add: sbunion_insert stB1.rep_eq stB0.rep_eq)
by(simp add: stB1_def)

(* sbRestrict *)

lemma "stB1 \<bar> {} = stB0"
by(simp add: sbrestrict_insert stB0_def)

lemma "stB3 \<bar> {c1, c2} = ([c1\<mapsto><[\<N> 1,\<N> 2,\<N> 3,\<N> 4]>, c2\<mapsto><[\<N> 5, \<N> 6, \<N> 7, \<N> 8]>])\<Omega>"
by(simp add: sbRestrict_def sbdom_insert stB3_def sb_well_def)

lemma "stB3 \<bar> {c1, c4} = ([c1\<mapsto><[\<N> 1,\<N> 2,\<N> 3,\<N> 4]>])\<Omega>"
by(simp add: sbRestrict_def sbdom_insert stB3_def sb_well_def)


thm stB3_def
(* sbHd *)
lemma "sbHd\<cdot>stB3 =  [c1 \<mapsto> <[\<N> 1]>, c2 \<mapsto> <[\<N> 5]>, c3 \<mapsto> \<epsilon>]\<Omega>" (is "?L=?R")
  apply(rule sb_eq)
   apply simp
   apply (simp add: sbdom_insert stB3.rep_eq sb_well_def)
  apply(simp add: sbHd_def )
  apply(simp add: sbdom_insert stB3.rep_eq stB3_def sb_well_def sbgetch_insert)
  by auto




(* sbLen *)

  (* Length of the selected stream. *)
definition mysbLen:: " 'm SB \<Rightarrow> lnat " where
"mysbLen b \<equiv> LEAST ln. ln\<in>{#(b. c) | c. c\<in>sbDom\<cdot>b}" 

definition mysbLen2:: " 'm SB \<Rightarrow> lnat " where
"mysbLen2 b \<equiv> Min {#(b. c) | c. c\<in>sbDom\<cdot>b}" 

thm lnat_ind


instance lnat ::wellorder
sorry

lemma assumes "c\<in>sbDom\<cdot>b"
  shows "mysbLen b \<le>  #(b . c)"
by (metis (mono_tags, lifting) Least_le assms mem_Collect_eq mysbLen_def)


lemma sblen_monofun [simp]: "monofun mysbLen"
proof(rule monofunI)
  fix x y :: "'m SB"
  assume "x\<sqsubseteq>y"
  hence dom_eq: "sbDom\<cdot>x = sbDom\<cdot>y" using sbdom_eq by auto 
  hence "\<forall>c \<in>sbDom\<cdot>x. #(x .c) \<sqsubseteq> #(y. c)"
    by (metis (no_types, lifting) \<open>x \<sqsubseteq> y\<close> below_SB_def below_option_def eq_imp_below fun_below_iff monofun_cfun_arg option.sel sbgetchE)

  thus "mysbLen x \<sqsubseteq> mysbLen y"
  proof (cases "sbDom\<cdot>x={}")
    case True thus ?thesis
      by (metis \<open>sbDom\<cdot>x = sbDom\<cdot>y\<close> empty_iff po_eq_conv sb_eq) 
  next
    case False
    hence "{#(x. c) | c. c\<in>sbDom\<cdot>x} \<noteq> {}" using Collect_empty_eq all_not_in_conv by blast
    have "{#(y. c) | c. c\<in>sbDom\<cdot>y} \<noteq> {}" using False dom_eq by auto
    obtain mx where "mx = (LEAST ln. ln\<in>{#(x. c) | c. c\<in>sbDom\<cdot>x})" by simp
    hence "\<And> ln. ln\<in>{#(x. c) | c. c\<in>sbDom\<cdot>x}  \<Longrightarrow> mx \<le>ln" by (simp add: Least_le)
    hence "\<And> ln. ln\<in>{#(y. c) | c. c\<in>sbDom\<cdot>y}  \<Longrightarrow> mx \<le>ln" 
      using \<open>\<forall>c\<in>sbDom\<cdot>x. #(x . c) \<sqsubseteq> #(y . c)\<close> dom_eq by fastforce 
    hence "\<And> ln. ln\<in>{#(y. c) | c. c\<in>sbDom\<cdot>y}  \<Longrightarrow> mysbLen x \<le>ln"
      by (simp add: \<open>mx = (LEAST ln. ln \<in> {#(x . c) |c. c \<in> sbDom\<cdot>x})\<close> mysbLen_def) 
    thus ?thesis
      by (metis (mono_tags, lifting) LeastI_ex \<open>{#(y . c) |c. c \<in> sbDom\<cdot>y} \<noteq> {}\<close> all_not_in_conv lnle_def mysbLen_def) 
  qed
qed



lemma mysblen_chain1: assumes "chain Y" shows "chain (\<lambda>i. mysbLen (Y i))"
proof(rule chainI)
  fix i
  have "Y i \<sqsubseteq> Y (Suc i)" using assms po_class.chainE by blast
  thus "mysbLen (Y i) \<sqsubseteq> mysbLen (Y (Suc i))" using monofunE sblen_monofun by blast 
qed


lemma sblen_cont [simp]: "cont mysbLen"
  apply(rule contI2)
   apply(simp)
  apply(rule+)
  apply auto
  apply(simp add: mysbLen_def)
oops


lemma sblen_cont: "cont (\<lambda> b. LEAST x. \<exists>c\<in>sbDom\<cdot>b. #(b. c) = x)" (is "cont (?T)")
sorry

lemma "sbLen stB2 = Fin 0 "
  apply(simp add: sbLen_def)
  apply(simp add: stB2.rep_eq sbdom_insert sbgetch_insert)
  apply(simp add: Least_def)
  apply rule
   by auto






(* Tupel filtering Operator Test *)
lemma sbleast_adm: fixes cs
  shows "adm (\<lambda>x. x \<in> cs^\<Omega>)"
by (simp add: SB_def)


lift_definition  tupelIn :: "M SB" is "[c1 \<mapsto> <[\<N> 1, \<N> 2, \<N> 1, \<N> 4]>, c2 \<mapsto> <[\<N> 5, \<N> 6, \<N> 7, \<N> 8]>]"
by(simp add: sb_well_def)

lift_definition tupelOut :: "M SB" is "[c1 \<mapsto> <[\<N> 1]>, c2 \<mapsto> <[\<N> 5]>]"
by(simp add: sb_well_def)

definition filterSet :: "M SB set" where 
"filterSet \<equiv> { [c1 \<mapsto> <[\<N> 1]>, c2 \<mapsto> <[\<N> 5]>]\<Omega>}"


lemma "myiterate 0 filterSet tupelIn = sbLeast {c1,c2}"
apply(simp add: myiterate_def)
by (simp add: insert_commute sbdom_insert sbtake_zero tupelIn.rep_eq)

lemma [simp]: "sbDom\<cdot>(myiterate i bs b) = sbDom\<cdot>b"
  apply(induction i arbitrary: bs b)
   apply(simp_all add: Let_def)
done

lemma miter_chain: "myiterate i bs b \<sqsubseteq> myiterate (Suc i) bs b"
  apply(induction i arbitrary: bs b)
   apply (simp only: myiterate.simps(1))
   apply(subst sbleast_least)
    apply(simp del: myiterate.simps)
   apply simp
  apply (simp add: Let_def)
  apply auto
   apply (smt monofun_cfun_arg)
  apply (smt monofun_cfun_arg)
done



lemma "myiterate 7 filterSet tupelIn = sbLeast {c1,c2}"
apply(simp add: myiterate_def Let_def sbRt_def)
oops

lemma assumes "sbHd\<cdot>b \<in> A"
  shows "myiterate (Suc i) A b = sbHd\<cdot>b \<bullet> (myiterate i A (sbRt\<cdot>b))"
by (simp add: assms)

lemma assumes "sbHd\<cdot>b \<notin> A"
  shows "myiterate (Suc i) A b = (myiterate i A (sbRt\<cdot>b))"
by (simp add: assms)

lemma assumes "sbHd\<cdot>b \<in> A"
  shows "sbFilterTupel A b = sbHd\<cdot>b \<bullet> (sbFilterTupel A (sbRt\<cdot>b))"
oops

lemma "sbFilterTupel filterSet tupelIn = tupelOut"
oops





end