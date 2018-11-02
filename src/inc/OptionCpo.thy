(*  Title:        OptionCpo
    Author:       Sebastian Stüber
    Author:       Jens Christoph Bürger
    e-mail:       sebastian.stueber@rwth-aachen.de
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  Defines "option" as CPO 
                   + Lemmas about partial functions
*)

theory OptionCpo
  imports SetPcpo Prelude (* "~~/src/HOL/HOLCF/Library/Option_Cpo" *)
begin

(* Some packages set a custom default type (eg cpo). This is overwritten. *)
default_sort type

(* Abbreviation for special if-then-else command to create an "option" *)
abbreviation if_then_abbr :: "bool \<Rightarrow> 'a \<rightharpoonup> 'a" ("(_\<leadsto>_)" [1000] 999) where
"A \<leadsto> B \<equiv> if A then Some B else None"

(* Abbreviation for applying a partial function f to argument s and retrieving the value *)
abbreviation the_abbrv:: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> 'b " ("_\<rightharpoonup>_") where
"f \<rightharpoonup> s \<equiv> the (f s)"





(* ----------------------------------------------------- *)
  section \<open>Option is po\<close>
(* ----------------------------------------------------- *)




(* A class defining symetric equality. *)
class myEQ =
  fixes myEQ :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "myEQ x y \<longleftrightarrow> myEQ y x"
begin
end

instantiation nat::myEQ
begin
  definition myEQ_nat:: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "myEQ_nat a b = (a = b)"

  instance
  apply(intro_classes)
  by(auto simp add: myEQ_nat_def)
end

(* Defines a partial order about options if the base type 'a is already a partial order. *)
instantiation option :: (po) po
begin  
  (* Define the ordering. "None" is only comparable with "None". *)
  (* If both arguments are \<noteq>None then the ordering of 'a is used. *)
  definition below_option_def: "b1 \<sqsubseteq> b2 \<equiv>  b1=b2  \<or> (b1 \<noteq> None \<and> b2 \<noteq> None \<and> the b1\<sqsubseteq>the b2)"

  (* Show that the ordering definition defines a correct partial order. *)
  instance
  apply intro_classes
    apply(simp add:below_option_def)
   apply (smt below_option_def below_trans)
  by (metis below_antisym below_option_def option.expand)
end





(* ----------------------------------------------------- *)
  section \<open>Option is CPO\<close>
(* ----------------------------------------------------- *)




(* Defines a complete partial order (cpo) about options if the base type 'a is already a cpo. *)
instantiation option :: (cpo) cpo
begin

  (* An option chain is either completely "Some 'a" or completely "None" *)
  lemma chain_NotNone: assumes "chain S" and "S i \<noteq> None"
    shows "S j \<noteq> None"
  by (metis assms below_option_def chain_tord)
      
  lemma chain_None[simp]: assumes "chain S" and "S i = None"
    shows "S j = None"
  using assms chain_NotNone by blast

  (* Definition of the Lub for option-chains *)
  (* If the chain contains only "None" then the Lub is "None" else the Lub is the lub of 'a *)
  definition optionLub :: "(nat \<Rightarrow> 'a::cpo option) \<Rightarrow> 'a option" where
  "optionLub S \<equiv> (S 0 \<noteq> None) \<leadsto> (\<Squnion>i. the (S i))"

  (* Show optionLub upper bound of the chain. Used for instance proof. *)
  lemma optionLub_max: assumes "chain S" shows "S i \<sqsubseteq> optionLub S"
  by (smt assms below_option_def chain_NotNone is_ub_thelub option.sel option.simps(3) optionLub_def po_class.chainI po_class.chain_def po_eq_conv)
  
  (* Show optionLub below every upper bound. Used for instance proof. *)
  lemma optionLub_least: assumes "chain S" and "range S <| u" 
    shows "optionLub S \<sqsubseteq> u"
  by (smt assms(1) assms(2) below_option_def is_ub_def lub_below option.sel option.simps(3) optionLub_def po_class.chain_def po_eq_conv rangeI)
  
  (* Show optionLub is the Lub of each chain. Used for instance proof. *)
  lemma optionLub_isLub: assumes "chain S" shows "range S <<| optionLub S"
  by (simp add: assms is_lub_def optionLub_least optionLub_max ub_rangeI)

instance
  apply intro_classes
  using optionLub_isLub by blast
end





(* ----------------------------------------------------- *)
  section \<open>Lemmas about Options \<close>
(* ----------------------------------------------------- *)




(* "the" is a monotonic function. Used in "op_the_cont" proof. *)
lemma op_the_mono[simp]: "monofun the"
  by (metis below_option_def below_refl monofunI)

(* Wrapping a chain in the option type preserves the chain property *)
lemma op_the_chain: assumes "chain Y" shows "chain (\<lambda>i. the (Y i))"
  by (metis assms below_option_def below_refl ch2ch_monofun monofunI)

(* "the" is a continuous function *)
lemma op_the_cont [simp]: "cont the"
  by (smt ch2ch_monofun chain_NotNone contI eq_imp_below is_lub_maximal lub_eq lub_eqI op_the_mono option.sel optionLub_def optionLub_isLub rangeI thelubE ub_rangeI)

(* "optionLub" is the lub *)
lemma op_is_lub: assumes "chain S"
  shows "(\<Squnion>i. S i) = optionLub S"
  using assms cpo_lubI is_lub_unique optionLub_isLub by blast

(* Retrieving the element inside the option before or after calculating the lub is the same *)
lemma op_the_lub: fixes S:: "nat \<Rightarrow> 'a::cpo option"
  assumes "chain S"
  shows "the (\<Squnion>i. S i) = (\<Squnion>i. the (S i))"
  using assms cont2contlubE op_the_cont by blast

(* "Some" is a continuous function *)
lemma some_cont[simp]: "cont Some"
  by (smt below_option_def contI cpo_lubI lub_eq op_is_lub option.sel option.simps(3) optionLub_def po_class.chain_def)

(* If the below-relation holds on the orig. elements, it also holds on their option counterpart *)
lemma some_below: assumes "x\<sqsubseteq>y"
  shows "Some x \<sqsubseteq> Some y"
  by (simp add: assms below_option_def)

(* If the below-relation holds on option elements, it also holds on the base elements *)
lemma some_below2: assumes "Some x \<sqsubseteq> Some y"
  shows "x \<sqsubseteq> y"
  by (metis assms below_option_def option.sel po_eq_conv)





(* ----------------------------------------------------- *)
  section \<open>Lemmas about partial functions \<close>
(* ----------------------------------------------------- *)




(* Rule for =: If the domain and their behaviour on said domain is =, they are = *)
lemma part_eq: assumes "dom x = dom y" and "\<And>i. i\<in>dom x \<Longrightarrow> the (x i) = the (y i)"
  shows "x = y"
  by (metis assms(1) assms(2) domIff map_le_antisym map_le_def option.collapse)

(* Rule for \<sqsubseteq>: If the domain is equal and every image over said domain is \<sqsubseteq>, they are \<sqsubseteq> *)
lemma part_below: assumes "dom x = dom y" and "\<And>i. i\<in>dom x \<Longrightarrow> the (x i) \<sqsubseteq> the (y i)"
  shows "x \<sqsubseteq> y"
  by (metis assms(1) assms(2) below_option_def domIff fun_belowI)




(* If two partial functions are in the "below" relation, their domain is identical. *)
lemma part_dom_eq: assumes "a\<sqsubseteq>b" 
  shows "dom a = dom b"
  by (smt Collect_cong assms below_option_def dom_def fun_below_iff)

(* In a chain all elements have the same domain *)
lemma part_dom_eq1: assumes "chain S" 
  shows "dom (S i) = dom (S j)"
  using assms chain_tord part_dom_eq by blast

(* Lub has the same domain as all elements in the chain *)
lemma part_dom_lub: fixes S::"nat \<Rightarrow> ('a \<rightharpoonup> 'b::cpo)"
  assumes "chain S"
  shows "dom (S i) = dom (\<Squnion>i. S i)"
  by (simp add: assms is_ub_thelub part_dom_eq)

(* Applying Some on both side does not change the below-relation *)
lemma part_some_below[simp]: assumes "g\<sqsubseteq>h"
  shows "(\<lambda>x. Some (g x)) \<sqsubseteq> (\<lambda>x. Some (h x))"
  by (meson assms below_fun_def some_below)


(* "the" in use with partial functions. *)

(* For any chain Y of partial functions, fixing the input to c results in another chain *)
lemma part_the_chain: assumes "chain Y" shows "chain (\<lambda>i. the (Y i c))"
  by (simp add: assms ch2ch_fun op_the_chain)

(* For any chain Y of partial functions, whose range is a cpo, fixing the input to c results in 
   another chain in a cpo on which the continuity of "the" can be used *)
lemma part_the_cont2: fixes Y :: "nat \<Rightarrow> ('a \<rightharpoonup> 'b::cpo)"
  assumes "chain Y"
  shows "the (\<Squnion>i. Y i c) = (\<Squnion>i. the (Y i c))"
  by (simp add: assms ch2ch_fun op_the_lub)

(* First Lub, then fixing the input, then retrieving the value = First fixing, retrieving, lub *)
lemma part_the_lub: fixes S :: "nat \<Rightarrow> ('a \<rightharpoonup> 'b::cpo)"
  assumes "chain S"
  shows "the ((\<Squnion>i. S i) a) = (\<Squnion>i. the (S i a)) "
  using assms ch2ch_fun lub_fun op_the_lub by fastforce


(* uses SetPcpo *)

(* Used to show that "dom" is cont. *)
lemma subset_cont: assumes "chain Y" and "\<forall>i. g\<cdot>(Y i) \<subseteq> cs"
  shows "g\<cdot>(\<Squnion>i. Y i) \<subseteq> cs"
  by (metis SetPcpo.less_set_def assms(1) assms(2) ch2ch_Rep_cfunR contlub_cfun_arg lub_below)

(* Used to show that "dom" is cont. *)
lemma the_subset_cont: fixes Y :: "nat \<Rightarrow> ('a \<rightharpoonup> 'b::cpo)"
  assumes "chain Y" and "\<forall>i. g\<cdot>(the ((Y i) c)) \<subseteq> cs"
  shows "g\<cdot>(the (\<Squnion>i. Y i c)) \<subseteq> cs"
  by (simp add: assms(1) assms(2) part_the_chain subset_cont part_the_cont2)




(* Domain of a function created with the special if-then-else command is the same as in if-expr. *)
lemma if_then_dom [simp]: "dom (\<lambda>c. (c \<in> cs)\<leadsto>g c) = cs"
  using po_eq_conv by fastforce

(* A chain of partial functions that contains "empty" contains only "empty" *)
lemma part_allempty[simp]: assumes "chain Y" and "Map.empty \<in> range Y"
  shows "(Y i) = Map.empty"
  by (metis assms(1) assms(2) domIff part_dom_eq1 rangeE)


(* ----------------------------------------------------- *)
  subsection \<open>map dom\<close>
(* ----------------------------------------------------- *)

(* "dom" is a monotonic function *)
lemma dom_monofun[simp]: "monofun dom"
  by (simp add: monofunI part_dom_eq)

(* "dom" is a continuous function*)
lemma dom_cont [simp]: "cont dom"
  by (simp add: contI part_dom_lub thelubE)


(* ----------------------------------------------------- *)
  subsection \<open>map add \<close>
(* ----------------------------------------------------- *)

(* Alternative definition of (op ++). In case you don't like "case". *)
lemma mapadd2if_then: "(a ++ b) c = (if (b c)=None then (a c) else (b c))"
  by (simp add: domIff map_add_dom_app_simps(1) map_add_dom_app_simps(3))

(* Show that both sides are monotonic. Used in cont proof. *)
lemma part_add_monofunL[simp]: "monofun  (\<lambda>a. a ++ b)"
  by (smt below_refl fun_below_iff map_add_dom_app_simps(1) map_add_dom_app_simps(3) monofunI part_dom_eq)

lemma part_add_monofunR[simp]: "monofun  (\<lambda>b. a ++ b)"
  by (smt below_refl fun_below_iff map_add_dom_app_simps(1) map_add_dom_app_simps(3) monofunI part_dom_eq)

(* Used in cont proof *)
(* Since the part of the domain that gets mapped to None remains unchanged for any chain Y of partial
   functions, it doesn't matter whether one overrides this part with the function a before or after
   taking the lub. *)
lemma map_add_lessR: fixes Y :: "nat \<Rightarrow> ('a \<rightharpoonup> 'b :: cpo)"
  assumes "chain Y"
  shows "a ++ (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. a ++ Y i)" (is "?L \<sqsubseteq> ?R")
  proof (rule part_below)
    show "dom ?L = dom ?R" by (metis assms dom_map_add monofunE part_add_monofunR part_dom_lub po_class.chain_def)
  next
    fix c
    assume "c\<in> dom ?L"
    thus "the ((a ++ (\<Squnion>i. Y i)) c) \<sqsubseteq> the ((\<Squnion>i. a ++ Y i) c)"
    by (smt assms part_the_lub is_ub_thelub lub_eq map_add_dom_app_simps(1) map_add_dom_app_simps(3) monofunE not_below2not_eq part_add_monofunR part_dom_lub po_class.chain_def)
  qed

lemma map_add_lessL: fixes Y :: "nat \<Rightarrow> ('a \<rightharpoonup> 'b :: cpo)"
  assumes "chain Y"
  shows "(\<Squnion>i. Y i)++a \<sqsubseteq> (\<Squnion>i. Y i ++ a)" (is "?L \<sqsubseteq> ?R")
by (smt assms below_lub dom_map_add lub_eq mapadd2if_then not_below2not_eq part_below part_dom_lub part_the_chain part_the_lub po_class.chain_def)

(* Both sides are continuous *)
lemma part_add_contR [simp]: "cont (\<lambda>b. a ++ b)"
  by (simp add: Cont.contI2 map_add_lessR part_add_monofunR)

lemma part_add_contL [simp]: "cont (\<lambda>a. a ++ b)"
  by (simp add: Cont.contI2 map_add_lessL part_add_monofunL)

(* Adding a to a continuous function b is continuous *)
lemma part_add_cont[simp]: "cont (\<lambda>a . \<Lambda> b . a ++ b)"
  using cont2cont_LAM part_add_contL part_add_contR by blast

(* If the domain of the added function b1 is a subset of b2's domain, the adding leaves b2 unaltered *)
lemma part_add_id [simp]: assumes "dom b1\<subseteq>dom b2" shows "b1 ++ b2 = b2"
  by (metis assms dom_map_add map_le_def map_le_map_add part_eq sup.orderE)


(* ----------------------------------------------------- *)
  subsection \<open>map restrict \<close>
(* ----------------------------------------------------- *)

(* Restricting partial functions with a fixed set cs is monotone *)
lemma part_restrict_monofun[simp]: "monofun (\<lambda>b. b |` cs)" 
  by (simp add: fun_belowD fun_belowI monofunI restrict_map_def)

(* Restricting partial functions with a fixed set cs is continuous *)
lemma part_restrict_cont [simp]: "cont (\<lambda>b . b |` cs)"
  proof (rule contI2)
   show "monofun (\<lambda>b. b |` cs)" by (simp add: part_restrict_monofun)
  next
  show "\<forall>Y:: nat \<Rightarrow> ('a \<rightharpoonup> 'b::cpo). chain Y \<longrightarrow> (\<Squnion>i. Y i) |` cs \<sqsubseteq> (\<Squnion>i. Y i |` cs)"
  by (smt domIff eq_imp_below fun_below_iff lub_eq lub_fun part_dom_lub po_class.chain_def restrict_map_def)
qed

(* Restricting x ++ y to a domain cs2 disjoint from dom y results in a restricted x *)
lemma map_union_restrict[simp]: assumes "(dom y)\<inter>cs2 = {}"
  shows "((x ++ y) |` cs2) = x |` cs2"
  apply(rule part_eq)
   apply (simp add: Int_Un_distrib2 assms)
  by (metis assms disjoint_iff_not_equal map_add_dom_app_simps(3) restrict_in restrict_out)

(* Restricting x ++ y to dom y results in y *)
lemma map_union_restrict2[simp]: "(x ++ y) |` dom y = y"
  by (smt Int_absorb1 dom_restrict map_le_def map_le_implies_dom_le map_le_map_add part_eq restrict_in)




(* Up partial functions: Instead of mapping to None, map to Some \<bottom> *)
definition part_up:: "('a \<rightharpoonup> 'b::pcpo) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
"part_up f \<equiv> \<lambda> a. if a\<in>dom f then f a else Some \<bottom>"

(* Upping preserves chain properties *)
lemma part_up_chain: assumes "chain Y"
  shows "chain (\<lambda>i. part_up (Y i))"
  by (smt assms part_up_def below_option_def fun_belowD fun_belowI part_dom_eq1 po_class.chain_def)

(* Upping is monotonic *)
lemma part_up_monofun: "monofun part_up"
  by (smt below_option_def fun_belowD fun_belowI monofunI part_dom_eq part_up_def)

(* Upping is continuous *)
lemma part_up_cont: "cont part_up"
  by (smt Cont.contI2 cont2cont_lambda is_ub_thelub lub_eq lub_fun mono2mono_fun part_dom_lub part_up_def part_up_monofun po_eq_conv)








(* Testing Stuff *)

lemma "monofun (\<lambda>s. [c \<mapsto> s])"
  by (simp add: monofun_def part_below)

(* If S is a chain, the sequence of constant total mappings mapping to the resp. elem. in S is too *)
lemma part_map_chain: assumes "chain S" shows "chain (\<lambda>i. [c \<mapsto> S i])"
  by (smt assms dom_empty dom_fun_upd fun_upd_same option.sel option.simps(3) part_below po_class.chain_def singletonD)




(* Stuff used in SPF *)

(* The mapping from empty to empty is continuous *)
lemma part_emptys_cont[simp]: "cont [Map.empty \<mapsto> Map.empty]"
proof (rule contI)
  fix Y:: "nat \<Rightarrow> ('a \<rightharpoonup> 'b)"
  assume chY: "chain Y"
  thus "range (\<lambda>i. [Map.empty \<mapsto> Map.empty] (Y i)) <<| [Map.empty \<mapsto> Map.empty] (\<Squnion>i. Y i)"
  proof (cases "Map.empty \<in> range (Y)")
    case True
    thus ?thesis by (simp add: chY is_lub_maximal lub_maximal part_allempty po_eq_conv rangeI ub_rangeI)
  next
    case False
    hence "\<forall>i. (dom(Y i) \<noteq> {})" by (smt dom_eq_empty_conv rangeI)
    hence "(\<Squnion>i. Y i) \<noteq> Map.empty" by (simp add: chY part_dom_lub)
    thus ?thesis by (smt False fun_upd_apply image_cong image_iff is_lub_const)
  qed
qed 




(* Converts a set into an indicator function, returning Some \<bottom> for elements in the set and None otherwise *)
definition optionLeast :: "'a set \<Rightarrow> ('a \<rightharpoonup> 'b :: pcpo)" where
"optionLeast as \<equiv> \<lambda>a. (a\<in>as) \<leadsto> \<bottom>"

(* The domain of the resulting indicator function is defined by the input set *)
lemma optionleast_dom [simp]: "dom(optionLeast cs) = cs"
  by (simp add: optionLeast_def)

(* In all channels "c" in the channel set "cs" flows the stream "\<epsilon>" *)
lemma optionleast_getch [simp]: assumes "c \<in> cs" shows "((optionLeast cs) \<rightharpoonup> c) = \<bottom>"
  by (simp add: assms optionLeast_def)

(* sbLeast returns the smallest stream bundle with the given domain *)
lemma optionleast_least [simp]: assumes "cs = dom b"
  shows "optionLeast cs \<sqsubseteq> b"
  by (metis assms minimal optionleast_dom optionleast_getch part_below)

(* The smallest function with empty domain ist the empty function *)
lemma optionleast_empty: "optionLeast {} = Map.empty"
  by (simp add: optionLeast_def)

(* If sbLeast{} (or empty\<Omega>) is in a chain, all elements are equal *)
lemma optionleast_range: assumes "chain Y" and "optionLeast {} \<in> range Y"
  shows "\<And>i. (Y i) = optionLeast {}"
  by (smt assms(1) assms(2) dom_eq_empty_conv optionleast_dom part_allempty)

(* For non-empty sets, the indicator function's range contains \<bottom> *)
lemma optionLeast_ran [simp]: "cs \<noteq> {} \<Longrightarrow> \<bottom> \<in> ran (optionLeast cs)"
by (meson all_not_in_conv optionLeast_def ranI)

(* The range of the indicator function consists of only \<bottom> *)
lemma optionLeast_ran_2 [simp]: "x \<in> ran (optionLeast cs) \<Longrightarrow> x=\<bottom>"
by (smt domI domIff mem_Collect_eq option.inject optionLeast_def ran_def)



(* The range is not always empty *)
lemma ran_exists: assumes "b\<in>ran f"
  shows "\<exists> d. (f\<rightharpoonup>d) = b"
  by (smt CollectD assms option.sel ran_def)

(* The if-part of the special if-then-else command and the lub are commutative *)
lemma if_then_lub [simp]: assumes "chain Y" 
  shows "True\<leadsto>(g\<cdot>(\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. (True)\<leadsto>(g\<cdot>(Y i)))"
  by (smt assms ch2ch_monofun contlub_cfun_arg lub_eq monofun_Rep_cfun2 op_is_lub option.sel option.simps(3) optionLub_def po_class.chain_def po_eq_conv some_below)

lemma if_then_lub2 [simp]: assumes "chain Y" and "cont g"
  shows "True\<leadsto>(g (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. (True)\<leadsto>(g (Y i)))"
  by (metis (mono_tags, lifting) Abs_cfun_inverse2 assms(1) assms(2) if_then_lub lub_eq)

(* If x is below y, then any partial functions obtained via the special if-then-else command are too *)
lemma if_then_below[simp]: assumes "x\<sqsubseteq>y"
  shows "(\<lambda>c. (c \<in> A)\<leadsto>g\<cdot>x) \<sqsubseteq> (\<lambda>c. (c \<in> A)\<leadsto>g\<cdot>y)"
  by (simp add: assms below_option_def fun_belowI monofun_cfun_arg)

(* If Y is a chain, then the seq. of part. func. obtained via the special if-then-else comm. are too *)
lemma if_then_chain [simp]: assumes "chain Y"
  shows "chain (\<lambda>i c. (c \<in> A)\<leadsto>g\<cdot>(Y i))"
  by (smt assms below_option_def fun_belowI monofun_cfun_arg option.distinct(1) option.sel po_class.chain_def)

(* Lub does not alter the domain *)
lemma if_then_lubdom [simp]: assumes "chain Y"
  shows "dom (\<Squnion>i. (\<lambda>c. (c \<in> A)\<leadsto>g\<cdot>(Y i))) = A"
  proof -
  have "dom (\<lambda>c. ((c \<in> A)\<leadsto>(g\<cdot>(Y 0)))) = A" by simp
  thus ?thesis
  proof -
  have "chain (\<lambda>n b. (b \<in> A)\<leadsto>g\<cdot>(Y n))"
  using assms if_then_chain by blast
  then show ?thesis
  using \<open>dom (\<lambda>c. (c \<in> A)\<leadsto>g\<cdot>(Y 0)) = A\<close> part_dom_lub by blast
    qed 
  qed

lemma if_then_chain2: "chain Y \<Longrightarrow> chain (\<lambda>i.  (\<lambda>c. (c \<in> A)\<leadsto>((Y i) c)))"
  by (simp add: below_fun_def below_option_def po_class.chain_def)

lemma if_then_cont_inner:"(\<And>x y. x\<sqsubseteq>y \<Longrightarrow> P x = P y) \<Longrightarrow> cont (\<lambda>c. (P c)\<leadsto>f\<cdot>c)"
  apply(rule contI2, rule monofunI)
  apply (simp add: domIff monofun_cfun_arg some_below)
  by (smt if_then_lub is_ub_thelub lub_eq po_class.chain_def po_eq_conv)


lemma if_then_cont [simp]: "cont (\<lambda>f.  (\<lambda>c. (c \<in> A)\<leadsto>(f c)))"
  apply(rule contI2, rule monofunI)
  apply (simp add: below_fun_def some_below)
  apply auto
  apply(rule fun_belowI)
  apply auto
  apply (smt ch2ch_fun cont2contlubE contlub_lambda lub_eq not_below2not_eq po_class.chain_def some_below some_cont)
  by (smt below_option_def domIff fun_belowD fun_belowI option.distinct(1) option.sel part_dom_lub po_class.chain_def)

lemma if_then_cont2 [simp]: "cont (\<lambda>f.  (\<lambda>c. (P c)\<leadsto>(f c)))"
proof - 
  obtain A where "\<And>c. P c \<longleftrightarrow> c\<in>A"
    by auto
  hence h: "\<And>f. (\<lambda>c. (P c)\<leadsto>(f c)) =  (\<lambda>c. (c \<in> A)\<leadsto>(f c))"
    by simp
  show ?thesis unfolding h by simp
qed


lemma if_then_cont3 [simp]: "cont (\<lambda>f.  (\<lambda>c. (P c)\<leadsto>(f\<cdot>c)))"
proof(rule contI)
  fix Y::"nat \<Rightarrow> 'a \<rightarrow> 'b"
  assume "chain Y"
  obtain K where k_chain: "chain K" and k_def: "\<And>i. K i = Rep_cfun (Y i)"
    by (simp add: \<open>chain (Y::nat \<Rightarrow> 'a \<rightarrow> 'b)\<close> ch2ch_lambda)
  hence k_lub_eq: "(\<Squnion>i. K i) = (Rep_cfun (\<Squnion>i. Y i))"
    proof -
      obtain nn :: "(nat \<Rightarrow> 'b) \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> nat" where
        "\<forall>f fa. f (nn f fa) \<noteq> fa (nn f fa) \<or> Lub f = Lub fa"
    by moura
      then have "\<forall>a f. Lub f = (\<Squnion>n. Y n\<cdot>a) \<or> f (nn f (\<lambda>n. Y n\<cdot>a)) \<noteq> K (nn f (\<lambda>n. Y n\<cdot>a)) a"
        by (metis \<open>\<And>i::nat. (K::nat \<Rightarrow> 'a \<Rightarrow> 'b) i = Rep_cfun ((Y::nat \<Rightarrow> 'a \<rightarrow> 'b) i)\<close>)
      then have "\<forall>a. Lub Y\<cdot>a = (\<Squnion>n. K n a)"
        by (metis \<open>chain (Y::nat \<Rightarrow> 'a \<rightarrow> 'b)\<close> contlub_cfun_fun)
      then show ?thesis
    by (simp add: \<open>chain (K::nat \<Rightarrow> 'a \<Rightarrow> 'b)\<close> fun_belowI lub_fun po_eq_conv)
qed
  have h1: "range (\<lambda>(i::nat) c::'a. (P c)\<leadsto>((Y i)\<cdot>c)) = range (\<lambda>(i::nat) c::'a. (P c)\<leadsto>((K i)c))"
    using k_def by presburger
  have h2: "(\<lambda>c::'a. (P c)\<leadsto>(\<Squnion>i::nat. Y i)\<cdot>c) = (\<lambda>c::'a. (P c)\<leadsto>(\<Squnion>i::nat. K i)c)"
    using k_lub_eq by auto
  hence "chain K \<Longrightarrow> range (\<lambda>(i::nat) c::'a. (P c)\<leadsto>((K i) c)) <<| (\<lambda>c::'a. (P c)\<leadsto>(\<Squnion>i::nat. K i) c)"
    using contE if_then_cont2 k_chain by blast
  thus "range (\<lambda>(i::nat) c::'a. (P c)\<leadsto>((Y i)\<cdot>c)) <<| (\<lambda>c::'a. (P c)\<leadsto>(\<Squnion>i::nat. Y i)\<cdot>c)" 
    by (metis h1 k_chain k_lub_eq)
qed

lemma if_then_mono4 [simp]: "(\<And>x y. x\<sqsubseteq>y \<Longrightarrow> P x = P y) \<Longrightarrow> monofun (\<lambda>f.  (\<Lambda> c. (P c)\<leadsto>(f\<cdot>c)))"
  apply(rule monofunI)
  apply(simp add: below_cfun_def if_then_cont_inner)
  by (simp add: below_option_def fun_belowD fun_belowI)

lemma if_then_cont4 [simp]: "(\<And>x y. x\<sqsubseteq>y \<Longrightarrow> P x = P y) \<Longrightarrow> cont (\<lambda>f.  (\<Lambda> c. (P c)\<leadsto>(f\<cdot>c)))"
  using if_then_cont_inner if_then_mono4 
  oops

(* The domain of the special if-then-else command ist determined by the if-clause and vice versa *)
lemma domIff2: "b\<in>dom (\<lambda>b2. ((P b2) \<leadsto> h b2)) \<longleftrightarrow> P b"
  using domIff by force

(* "Some" can be pulled out when applied to a chain *)  
lemma some_lub_chain_eq: fixes Y :: "nat \<Rightarrow> 'a::cpo"
            assumes "chain Y"
            shows " Some (\<Squnion> i. Y i) = (\<Squnion> i. Some (Y i))"
  using assms cont2contlubE some_cont by blast
    
lemma some_lub_chain_eq3: fixes Y :: "nat \<Rightarrow> 'a::cpo"
            assumes "chain Y"
            shows "(\<Squnion> i. Some (Y i)) = Some (\<Squnion> i. Y i)"
 by (simp add: some_lub_chain_eq assms)

(* "Some" can be pulled out when applied to a function which is applied to a chain *)   
lemma some_lub_chain_eq2: fixes Y:: "nat \<Rightarrow> 'a::cpo"
             fixes f:: "'a \<Rightarrow> 'b::cpo"
             assumes "chain (\<lambda>i. f (Y i))"
             shows " Some (\<Squnion> i. f (Y i)) = (\<Squnion> i. Some (f (Y i)))"
  using assms(1) some_lub_chain_eq by blast

lemma option_one_cont: "cont (\<lambda>x. [c \<mapsto> f\<cdot>x])"
  apply(rule contI2, rule monofunI)
   apply (simp add: below_option_def fun_belowI monofun_cfun_arg)
  apply (auto simp add: below_fun_def below_option_def)
  apply (smt below_option_def chain_monofun domIff fun_belowI fun_upd_apply option.exhaust_sel part_dom_lub po_class.chain_def some_below)
  apply (simp add: contlub_cfun_arg part_map_chain part_the_lub)
  by (smt below_option_def cont_pref_eq1I domIff fun_belowI fun_upd_apply option.sel option.simps(3) part_dom_lub po_class.chain_def)

  
  

subsection \<open>Lub\<close>     
    
(* Two lubs can be merged together if a function F is cont in x for every i *)
lemma cont2lub_lub_eq: assumes cont: "\<And>i. cont (\<lambda>x. F i x)" 
  shows "chain Y\<longrightarrow>  (\<Squnion>i. F i (\<Squnion>i. Y i)) = (\<Squnion>i ia. F i (Y ia))"
proof -
  { assume "\<exists>a. (\<Squnion>n. F a (Y n)) \<noteq> F a (Lub Y)"
    have ?thesis
      by (simp add: cont cont2contlubE) }
  thus ?thesis
    by force
qed
  
(* The lub is not affected by index shift *)
lemma lub_suc_shift: fixes Y:: "nat \<Rightarrow> 'a::cpo" assumes "chain Y"
  shows "(\<Squnion>i. Y (Suc i)) = (\<Squnion>i. Y i)"
proof-
  have f1: "(\<Squnion>i. Y (Suc i)) = (\<Squnion>i. Y (i + 1))"
    by auto
  thus ?thesis
    apply (subst f1)
    by (subst lub_range_shift, simp_all add: assms)
qed
     
(* Two chain lubs are equal if one is the shifted-by-one version of the other *)
lemma lub_suc_shift_eq: fixes Y:: "nat \<Rightarrow> 'a::cpo" fixes Z:: "nat \<Rightarrow> 'a::cpo" 
              assumes "chain Y" and "chain Z" 
              and "\<And> i. (Y (Suc i) = Z (Suc (Suc(i))))"
shows "(\<Squnion>i. (Y i)) = (\<Squnion>i. (Z i))"
proof -  
  have f1: "(\<Squnion>i. (Y (Suc(i)))) = (\<Squnion>i. (Z i))"
    apply (simp only: assms(3))
    apply (subst lub_suc_shift)
    using assms(2) po_class.chain_def 
    apply blast
    by (subst lub_suc_shift, simp_all add: assms)
      
  have f2: "(\<Squnion>i. Y (Suc i)) = (\<Squnion>i. Y i)"
    by (simp add: assms(1) lub_suc_shift)
  thus ?thesis
    by (simp add: f1)
qed
  
(* Two interleaved chains have the same least upper bound *)
lemma lub_interl_chain_eq:  fixes Y:: "nat \<Rightarrow> 'a::cpo" fixes Z:: "nat \<Rightarrow> 'a::cpo" 
  assumes "\<And> i. Y i \<sqsubseteq> Z i" and "\<And> i. Z i \<sqsubseteq> Y (Suc i)"
  shows "(\<Squnion>i. (Y i)) = (\<Squnion>i. (Z i))"
proof -
  have f1: "(\<Squnion>i. (Y i)) \<sqsubseteq> (\<Squnion>i. (Z i))"
    by (meson assms(1) assms(2) below_trans lub_mono po_class.chain_def)
  moreover 
  have f2: "(\<Squnion>i. (Z i)) \<sqsubseteq> (\<Squnion>i. (Y i))"
  proof (rule ccontr)
    assume "\<not> ((\<Squnion>i. (Z i)) \<sqsubseteq> (\<Squnion>i. (Y i)))"
    thus False
      by (meson assms(1) assms(2) below_lub lub_below_iff po_class.chain_def rev_below_trans)
  qed
  ultimately    
  show ?thesis
    by (simp add: below_antisym)
qed
 
(* Lubs are equal if chain index is multiplied (only every m-th element taken into consideration) *)
lemma lub_range_mult:  fixes Y:: "nat \<Rightarrow> 'a::cpo" assumes "chain Y" and "m \<ge> 1"
  shows "(\<Squnion>i. Y (i)) = (\<Squnion>i. Y (m * i))"
proof -
  have f1: "\<forall> (i::nat). i \<le> (m * i)"
    using assms(2) by auto
  have f2: "\<forall> i. Y (i) \<sqsubseteq> Y (m * i)"
    by (simp add: assms(1) f1 po_class.chain_mono)
  have f3: "chain (\<lambda>i. Y (m * i))"
    by (metis (no_types, lifting) Suc_n_not_le_n assms mult.commute nat_le_linear 
          nat_mult_le_cancel_disj po_class.chain_def po_class.chain_mono) 
        
  hence "(\<Squnion>i. Y (m * i)) \<sqsubseteq> (\<Squnion>i. Y (i))"
    using assms lub_below_iff by blast    
  thus ?thesis
    by (simp only: assms below_antisym f2 f3 lub_mono)
qed
  
(* Lub equality rule for multiplied indices *)
lemma lub_mult_shift_eq: fixes Y:: "nat \<Rightarrow> 'a::cpo" fixes Z:: "nat \<Rightarrow> 'a::cpo" 
  assumes "chain Y" and "chain Z" and "m \<ge> 1"
  and "\<And> i. Y (i) = Z (m * i)"
shows "(\<Squnion>i. (Y i)) = (\<Squnion>i. (Z i))"
  apply (simp only: assms(4))
  using assms(2) assms(3) lub_range_mult by fastforce
  
lemma lub_mult2_shift_eq: fixes Y:: "nat \<Rightarrow> 'a::cpo" fixes Z:: "nat \<Rightarrow> 'a::cpo" 
  assumes "chain Y" and "chain Z"
  and "\<And> i. Y (i) = Z (2 * i)"
shows "(\<Squnion>i. (Y i)) = (\<Squnion>i. (Z i))"
  apply (simp add: assms)
  by (metis assms(2) lub_range_mult one_le_numeral)
    

(* Copied from the HOLCF library *)

(* Case distinction for chains *)
lemma option_chain_cases:
  assumes Y: "chain Y"
  obtains "Y = (\<lambda>i. None)" | A where "chain A" and "Y = (\<lambda>i. Some (A i))"
 apply (cases "Y 0")
  apply (rule that(1))
  apply (rule ext)
  apply (cut_tac j=i in chain_mono [OF Y le0], simp)
  apply (simp add: below_option_def)
 apply (rule that(2))
  apply (rule ch2ch_monofun [OF op_the_mono Y])
 apply (rule ext)
 apply (cut_tac j=i in chain_mono [OF Y le0], simp)
 apply (case_tac "Y i", simp_all)
  by (simp add: below_option_def)

(* If the lub is x, then all elements in the chain are \<noteq>None and "Some" can be inserted *)
lemma is_lub_Some: "range S <<| x \<Longrightarrow> range (\<lambda>i. Some (S i)) <<| Some x"
 apply (rule is_lubI)
  apply (rule ub_rangeI)
  apply (simp add: is_lubD1 some_below ub_rangeD)
 apply (frule ub_rangeD [where i=arbitrary])
 apply (case_tac u, simp_all)
  apply (simp add: below_option_def)
  by (meson is_lub_def some_below some_below2 ub_rangeD ub_rangeI)

(* Rules for continuity proofs of case distinctions *)
lemma cont2cont_case_option:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  assumes h1: "\<And>a. cont (\<lambda>x. h x a)"
  assumes h2: "\<And>x. cont (\<lambda>a. h x a)"
  shows "cont (\<lambda>x. case f x of None \<Rightarrow> g x | Some a \<Rightarrow> h x a)"
apply (rule cont_apply [OF f])
apply (rule contI)
apply (erule option_chain_cases)
apply (simp add: is_lub_const)
  apply (smt cont_def cpo_lubI h2 image_cong is_lub_Some lub_eqI option.simps(5))
apply (case_tac y, simp_all add: g h1)
done

lemma cont2cont_case_option' [simp, cont2cont]:
  assumes f: "cont (\<lambda>x. f x)"
  assumes g: "cont (\<lambda>x. g x)"
  assumes h: "cont (\<lambda>p. h (fst p) (snd p))"
  shows "cont (\<lambda>x. case f x of None \<Rightarrow> g x | Some a \<Rightarrow> h x a)"
using assms by (simp add: cont2cont_case_option prod_cont_iff)
    

subsection \<open>Using option types with Fixrec\<close>

(* Matches None, fails otherwise *)
definition
  "match_None = (\<Lambda> x k. case x of None \<Rightarrow> k | Some a \<Rightarrow> Fixrec.fail)"

(* Matches Some, fails otherwise *)
definition
  "match_Some = (\<Lambda> x k. case x of None \<Rightarrow> Fixrec.fail | Some a \<Rightarrow> k\<cdot>a)"

(* Simp rules for match_None *)
lemma match_None_simps [simp]:
  "match_None\<cdot>None\<cdot>k = k"
  "match_None\<cdot>(Some a)\<cdot>k = Fixrec.fail"
unfolding match_None_def by simp_all

(* Simp rules for match_Some *)
lemma match_Some_simps [simp]:
  "match_Some\<cdot>None\<cdot>k = Fixrec.fail"
  "match_Some\<cdot>(Some a)\<cdot>k = k\<cdot>a"
unfolding match_Some_def by simp_all

(* Setup Fixrec *)
setup \<open>
  Fixrec.add_matchers
    [ (@{const_name None}, @{const_name match_None}),
      (@{const_name Some}, @{const_name match_Some}) ]
\<close>
 
end
