(*  Title:        TSBTheorie.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  Definition of "Timed Stream Bundles"
                    in 3 different versions, a general "TSB"  
                                             one over infinite TStreams "TSB_inf"
                                             and one over finite TStreams "TSB_fin"
*)


chapter {* Timed Streams *} 

theory TSBTheorie
imports Channel OptionCpo TStreamTheorie TStreamCase_Study
begin



default_sort message

(* ----------------------------------------------------------------------- *)
  section \<open>Timed Stream Bundle \<close>
(* ----------------------------------------------------------------------- *)

 (* Definition: Welltyped. "a \<rightharpoonup> b" means "a => b option" *)
  (* Every TStream may only contain certain elements *)
  (* and alle tstreams must have the same number of \<surd> *)
definition tsb_well :: "(channel \<rightharpoonup> 'm tstream) => bool" where
"tsb_well f \<equiv> (\<forall>c \<in> dom f. tsDom\<cdot>(f\<rightharpoonup>c) \<subseteq> ctype c) 
        \<and> (\<exists>n. \<forall>c \<in> dom f.  #\<surd>(f\<rightharpoonup>c) = n)"

lemma tstick_count_help: assumes "chain Y" and "\<not>finite_chain Y" 
    and "\<And>i. \<exists>n. \<forall>c \<in> dom (Y i). #\<surd>((Y i)\<rightharpoonup>c) = n" and "c\<in>dom (Y 0)"
  shows "\<not>finite_chain (\<lambda>i. ((Y i) \<rightharpoonup> c))"
proof(rule ccontr, simp)
  assume fin_y: "finite_chain (\<lambda>i. (Y i)\<rightharpoonup>c)"
  hence ch_y: "chain (\<lambda>i. (Y i)\<rightharpoonup>c)" using finite_chain_def by blast
  obtain j where j_def: "max_in_chain j (\<lambda>i. (Y i)\<rightharpoonup>c)" using fin_y finite_chainE by auto
  hence "\<And>c2. c2\<in>dom (Y 0) \<Longrightarrow>  max_in_chain j (\<lambda>i. (Y i)\<rightharpoonup>c2)" 
  proof -
    fix c2
    assume c2_as: "c2\<in>dom (Y 0)" 
    hence c2_dom: "\<And>i. c2\<in>dom (Y i)" using assms(1) part_dom_eq1 by blast
    hence "\<And>i. #\<surd> (Y i)\<rightharpoonup>c = #\<surd>(Y i)\<rightharpoonup>c2" by (metis assms(1) assms(3) assms(4) part_dom_eq1)
    hence f1: "\<And>i. j\<le>i \<Longrightarrow> #\<surd>(Y i)\<rightharpoonup>c2 =  #\<surd> (Y j)\<rightharpoonup>c2" by (metis j_def max_in_chainD)
    hence "\<And>i. j\<le>i \<Longrightarrow> (Y j)\<rightharpoonup>c2 \<sqsubseteq> (Y i)\<rightharpoonup>c2" by (metis assms(1) part_the_chain po_class.chain_mono)
    hence "\<And>i. j\<le>i \<Longrightarrow> (Y i)\<rightharpoonup>c2 =  (Y j)\<rightharpoonup>c2" using local.f1 tstake_below_eq by fastforce 
    thus "max_in_chain j (\<lambda>i. (Y i)\<rightharpoonup>c2)" by (metis (no_types, lifting) max_in_chainI)
  qed 
  hence "max_in_chain j Y" by (metis (no_types, lifting) assms(1) max_in_chainD max_in_chainI part_dom_eq1 part_eq) 
  thus False using assms(1) assms(2) finite_chainl1 by blast 
qed


(* checking whether every stream in the range of a partial function f has the same number of ticks 
   is an admissible predicate *)
lemma tstick_count_adm: "adm (\<lambda> f. \<exists>n. \<forall>c::channel \<in> dom f. #\<surd>(f\<rightharpoonup>c) = n)"
  apply(rule admI)
  apply(rename_tac Y)
  apply (case_tac "finite_chain Y \<or> dom (\<Squnion>i. Y i) = {}")
   apply (metis equals0D l42)
  by (metis (mono_tags, lifting) part_dom_lub part_the_chain part_the_lub ts_infinite_lub tstick_count_help)


lemma tsb_welltyped_adm [simp]: "adm (\<lambda>f. \<forall>c \<in> dom f. tsDom\<cdot>(f\<rightharpoonup>c) \<subseteq> ctype c)"
  by (simp add: adm_def lub_fun part_dom_lub the_subset_cont)


lemma tsb_well_adm [simp]: "adm (\<lambda>f. tsb_well f)"
  apply(subst tsb_well_def)
  apply (rule adm_conj)
   using tsb_welltyped_adm apply blast
  by (simp add: tstick_count_adm)


(* Definition: Timed Stream Bundle. *)
cpodef 'm :: message TSB = "{b :: channel \<rightharpoonup> 'm tstream . tsb_well b }"
   using tsb_well_def apply fastforce
  by auto

setup_lifting type_definition_TSB


(* ----------------------------------------------------------------------- *)
  subsection \<open>Definitions on TSB \<close>
(* ----------------------------------------------------------------------- *)

definition tsbDom :: "'m TSB \<rightarrow> channel set" where
"tsbDom \<equiv> \<Lambda> tb. dom (Rep_TSB tb)"

definition TSB :: "channel set \<Rightarrow> 'm TSB set" where
"TSB cs \<equiv> {b. tsbDom\<cdot>b = cs}"


(* returns the tstream flowing in given channel *)
definition tsbGetCh :: "'m TSB \<rightarrow> channel \<rightarrow> 'm tstream" where
"tsbGetCh \<equiv> \<Lambda> tb c. ((Rep_TSB tb) \<rightharpoonup> c)"

abbreviation tsbGetCh_abbr :: "'m TSB \<Rightarrow> channel \<Rightarrow>  'm tstream" (infix " . " 65)
where "b . c \<equiv> tsbGetCh\<cdot>b\<cdot>c"


 (* Channels not in the channel set are set to "None". *)
definition tsbRestrict:: "channel set \<Rightarrow> 'm TSB \<rightarrow> 'm TSB" where
"tsbRestrict cs \<equiv>  \<Lambda> b. Abs_TSB (Rep_TSB b |` cs)"

abbreviation tsbRestrict_abbr :: "'m TSB \<Rightarrow> channel set \<Rightarrow> 'm TSB" (infix "\<bar>" 65)
where "b\<bar>cs \<equiv> tsbRestrict cs\<cdot>b"


(* returns the first n blocks of the TSB *)
definition tsbTTake :: "nat \<Rightarrow> 'm TSB \<Rightarrow> 'm TSB" where 
"tsbTTake n tb = Abs_TSB (\<lambda>c. (c\<in>tsbDom\<cdot>tb) \<leadsto> (tsTake n\<cdot>(tb  .  c)))"

abbreviation tsbTTake_abbrv :: "'m TSB \<Rightarrow> nat \<Rightarrow> 'm TSB" ("_ \<down> _ ")where
"tb \<down> n \<equiv> tsbTTake n tb"


definition tsbLeast :: "channel set \<Rightarrow> 'm TSB" where 
"tsbLeast cs = Abs_TSB (optionLeast cs)"

(*
definition tsbUnion :: "'m TSB \<rightarrow> 'm TSB \<rightarrow> 'm TSB"  where 
"tsbUnion \<equiv> \<Lambda> tb1 tb2 . Abs_TSB ((Rep_TSB tb1) ++ (Rep_TSB tb2))"

abbreviation tsbUnion_abbrv :: "'m TSB \<Rightarrow> 'm TSB \<Rightarrow> 'm TSB" (infixl "\<uplus>" 100) where
"tb1 \<uplus> tb2 \<equiv> tsbUnion\<cdot>tb1\<cdot>tb2"
*)
definition tsbTickCount :: "'m TSB \<rightarrow> lnat" where
"tsbTickCount \<equiv>  \<Lambda> tb. #\<surd>(SOME ts. ts \<in> ran (Rep_TSB tb))"

abbreviation tsbTickCount_abbrv :: "'m TSB \<Rightarrow> lnat "  ("#\<surd>tsb _ ") where
" #\<surd>tsb tsb \<equiv> tsbTickCount\<cdot>tsb"



(* ----------------------------------------------------------------------- *)
  subsection \<open>Lemmas on TSB \<close>
(* ----------------------------------------------------------------------- *)

(* allgemeine *)


lemma rep_tsb_cont [simp]: "cont Rep_TSB"
  by (smt Abs_TSB_inverse adm_TSB adm_def below_TSB_def contI lub_TSB lub_eq po_class.chain_def thelubE type_definition.Rep type_definition_TSB)

lemma rep_chain[simp]: assumes "chain S"
  shows "chain (\<lambda>n. Rep_TSB (S n))"
  by (meson assms below_TSB_def po_class.chain_def)

text {* Equivalence of evaluation of StBundleLub based on lub of function values.*}
lemma lub_eval: assumes "chain S" 
  shows "the (Rep_TSB (\<Squnion>i. S i) c) = (\<Squnion>j. the (Rep_TSB (S j) c))"
  by (smt assms below_TSB_def ch2ch_monofun cont2contlubE lub_eq monofunI part_the_lub rep_tsb_cont)

lemma theRep_chain[simp]: assumes "chain S" 
  shows "chain (\<lambda>n. the (Rep_TSB (S n) c))"
  using assms part_the_chain rep_chain by fastforce

lemma [simp]: assumes "tsb_well f"
  shows "Rep_TSB (Abs_TSB f) = f"
  by (simp add: Abs_TSB_inverse assms)


lemma rep_lub:assumes "chain Y"
  shows "(\<Squnion>i. Rep_TSB (Y i)) = Rep_TSB (\<Squnion>i.  Y i)"
  by (metis assms cont2contlubE lub_eq rep_tsb_cont)

lemma [simp]: assumes "cont g" and "\<forall>x. tsb_well (g x)"
  shows "cont (\<lambda>x. Abs_TSB (g x))"
  by (simp add: assms(1) assms(2) cont_Abs_TSB)

lemma [simp]: "tsb_well (Rep_TSB b1)"
  using Rep_TSB by blast

lemma [simp]: "Abs_TSB (Rep_TSB y) = y"
  by (simp add: Rep_TSB_inverse)

lemma [simp]: "tsb_well empty"
  by(simp add: tsb_well_def)

lemma ts_ex_len [simp]: "\<exists> ln . ( \<forall> c . (c \<in> (dom (Rep_TSB b)) \<longrightarrow> ((#\<surd> ((Rep_TSB b) \<rightharpoonup> c)) = ln)))"
  using Rep_TSB tsb_well_def  using mem_Collect_eq by force

lemma [simp]: assumes "tsb_well f" and "c\<in>dom f"
  shows "tsDom\<cdot>f\<rightharpoonup>c \<subseteq> ctype c"
  using assms(1) assms(2) tsb_well_def by blast

lemma tsb_tick_eq: assumes "tsb_well f" and "c1\<in>dom f" and "c2\<in>dom f"
  shows "#\<surd> f\<rightharpoonup>c1 = #\<surd> f\<rightharpoonup>c2"
  by (metis assms(1) assms(2) assms(3) tsb_well_def)


lemma tsb_wellI: 
  assumes "\<And> c. c\<in>dom f \<Longrightarrow> tsDom\<cdot>f\<rightharpoonup>c \<subseteq> ctype c"
  and "\<exists>ln. (\<forall> c. c\<in>dom f \<longrightarrow>  #\<surd> f\<rightharpoonup>c = ln)"
  shows "tsb_well f"
  apply(simp add: tsb_well_def assms)
  using assms(2) by blast





(* tsbDom *)
thm tsbDom_def


lemma [simp]: "cont (\<lambda> tb. dom (Rep_TSB tb))"
  by (simp add: cont_compose)

lemma tsbdom_insert: "tsbDom\<cdot>tb = dom (Rep_TSB tb)"
  by (simp add: tsbDom_def)

lemma tsbdom_rep_eq: "tsb_well tb \<Longrightarrow> tsbDom\<cdot>(Abs_TSB tb) = dom tb"
by(simp add: tsbdom_insert)


lemma tsbdom_below: assumes "tb1 \<sqsubseteq> tb2"
  shows "tsbDom\<cdot>tb1 = tsbDom\<cdot>tb2"
  by (metis assms below_TSB_def part_dom_eq tsbdom_insert)

lemma tsbChain_dom_eq2[simp]: assumes "chain S"
  shows "tsbDom\<cdot>(S i) = tsbDom\<cdot>(\<Squnion>j. S j)"
  by (simp add: assms is_ub_thelub tsbdom_below)

lemma [simp]: assumes "c\<in>tsbDom\<cdot>tsb"
  shows "tsDom\<cdot>(Rep_TSB tsb)\<rightharpoonup>c \<subseteq> ctype c"
  using assms by(simp add: tsbdom_insert)





(* tsbGetCh *)
thm tsbGetCh_def

lemma tsbgetch_cont1 [simp]: "cont (\<lambda>tb  c . ((Rep_TSB tb) \<rightharpoonup> c))"
by (smt cont2cont_lambda contI cpo_lubI lub_eq lub_eval po_class.chain_def theRep_chain)

lemma [simp]: "cont (\<lambda>tb .\<Lambda>  c . ((Rep_TSB tb) \<rightharpoonup> c))"
using cont2cont_LAM_discrete cont2cont_fun by force


lemma tsbgetch_insert: "tsb  .  c = (Rep_TSB tsb) \<rightharpoonup> c"
by(simp add: tsbGetCh_def)

lemma tsbgetch_rep_eq: "tsb_well tb \<Longrightarrow> (Abs_TSB tb) . c = tb\<rightharpoonup>c"
by(simp add: tsbgetch_insert)


lemma tsb_tick_eq2: assumes "c1\<in>tsbDom\<cdot>f" and "c2\<in>tsbDom\<cdot>f"
  shows "#\<surd> f . c1 = #\<surd> f . c2"
  using assms by(simp add: tsbdom_insert tsbgetch_insert tsb_tick_eq)


lemma tsb_below: assumes "tsbDom\<cdot>x = tsbDom\<cdot>y" and "\<And> c. c\<in>tsbDom\<cdot>x \<Longrightarrow> x . c \<sqsubseteq>y . c"
  shows "x\<sqsubseteq>y"
  by (metis assms(1) assms(2) below_TSB_def part_below tsbdom_insert tsbgetch_insert)

lemma tsb_eq: assumes "tsbDom\<cdot>x = tsbDom\<cdot>y" and "\<And> c. c\<in>tsbDom\<cdot>x \<Longrightarrow> x . c =y . c"
  shows "x=y"
  by (metis Rep_TSB_inject assms(1) assms(2) part_eq tsbdom_insert tsbgetch_insert)









(* tsRestrict *)
thm tsbRestrict_def


lemma tsbrestrict_well[simp] : "tsb_well (Rep_TSB b |` cs)"
  apply(rule tsb_wellI)
   apply (metis Rep_TSB domIff mem_Collect_eq restrict_in restrict_out tsb_well_def)
  by (metis Int_iff dom_restrict restrict_in ts_ex_len)


lemma tsbrestrict_monofun[simp]: "monofun  (\<lambda>b. Rep_TSB b |` cs)"
  by (smt below_TSB_def fun_below_iff monofunI not_below2not_eq restrict_map_def )

lemma tsbrestrict_cont1[simp]: "cont  (\<lambda>b. ((Rep_TSB b) |` cs))"
  apply(rule contI2)
   apply(auto)
  by (smt below_option_def fun_below_iff is_ub_thelub lub_eq lub_fun po_class.chain_def rep_chain rep_lub restrict_in restrict_out)

lemma tsbrestrict_cont [simp]: "cont (\<lambda>b. Abs_TSB (Rep_TSB b |` cs))"
  by (simp add: cont_Abs_TSB)

lemma tsbrestrict_insert : "tsbRestrict cs\<cdot>tb = Abs_TSB (Rep_TSB tb |` cs)"
  by(simp add: tsbRestrict_def)

lemma tsbrestrict_rep_eq : "tsb_well tb \<Longrightarrow> tsbRestrict cs\<cdot>(Abs_TSB tb) = Abs_TSB (tb |` cs)"
  by(simp add: tsbRestrict_def)


lemma tsbrestrict_dom [simp]: "tsbDom\<cdot>(tb \<bar> cs) \<subseteq> cs"
  by(simp add: tsbrestrict_insert tsbdom_insert)

lemma tsresrict_dom2 [simp]: assumes "cs \<subseteq> tsbDom\<cdot>tb"
  shows "tsbDom\<cdot>(tb \<bar> cs) = cs"
  by (metis Abs_TSB_inverse Int_absorb1 assms dom_restrict mem_Collect_eq tsbdom_insert tsbrestrict_insert tsbrestrict_well)

lemma tsresrict_dom3 [simp]: shows "tsbDom\<cdot>(tb \<bar> cs) = tsbDom\<cdot>tb \<inter> cs"
  by(simp add: tsbrestrict_insert tsbdom_insert)


lemma [simp]: "(tb \<bar> cs1) \<bar> cs2 = tb \<bar> (cs1\<inter>cs2)"
  by(simp add: tsbrestrict_insert)

lemma tsbgetch_restrict [simp]: assumes "c \<in>cs"
  shows "(tb \<bar> cs)  .  c = tb  .  c"
  by(simp add: tsbgetch_insert tsbrestrict_insert assms)





(* tsbLeast *)
lemma [simp]: "tsb_well (optionLeast cs)"
  by(simp add: tsb_well_def)

lemma tsbleast_tsdom[simp]: "tsbDom\<cdot>(tsbLeast cs) = cs"
  by(simp add: tsbLeast_def tsbDom_def)

lemma [simp]:  assumes "c\<in>cs"
  shows "tsbLeast cs  .  c = \<bottom>"
  by(simp add: tsbLeast_def tsbgetch_insert assms)




(* TSB *)
lemma tsb_tsbleast [simp]:  "tsbLeast cs \<in> TSB cs"
  by (simp add: TSB_def)

lemma tsb_exists [simp]: "\<exists>tb. tb\<in>(TSB cs)"
  using tsb_tsbleast by blast

lemma [simp]: assumes "tb\<in>(TSB cs)" shows "tsbDom\<cdot>tb = cs"
  using TSB_def assms by auto






(* tsbTickCount *)

(*Experimentell ... *)

thm tsbTickCount_def

lemma [simp]: "cont ((\<lambda> tb. #\<surd> SOME ts. ts \<in> ran (Rep_TSB tb)))"
apply(rule contI2)
apply(rule monofunI)
oops

lemma "cs \<noteq> {} \<Longrightarrow> #\<surd>tsb (tsbLeast cs) = Fin 0"
apply(simp add: tsbTickCount_def)
apply(simp add:  tsbLeast_def, simp add: optionLeast_def)
apply auto
oops





(* ----------------------------------------------------------------------- *)
  subsection \<open>tsbUnion \<close>
(* ----------------------------------------------------------------------- *)

(* tsbUnion wurde geschrieben bevor alle channels gleich viele ticks haben müssen. 
    Daher viel anpassen nötig *)

(*
(* tsbUnion produces a welltyped partial-function *)
lemma tsbunion_well[simp]: assumes "tsb_well b1" and "tsb_well b2"
  shows "tsb_well (b1 ++ b2)"
  sorry

(* helper function for continuity proof *)
lemma tsbunion_contL[simp]: "cont (\<lambda>b1. (Rep_TSB b1) ++ (Rep_TSB b2))"
  using cont_compose part_add_contL rep_tsb_cont by blast

(* helper function for continuity proof *)
lemma tsbunion_contR[simp]: "cont (\<lambda>b2. (Rep_TSB b1) ++ (Rep_TSB b2))"
  using cont_compose part_add_contR rep_tsb_cont by blast

(* sbUnion is an coninuous function *)
lemma tsbunion_cont[simp]: "cont (\<lambda> b1. \<Lambda> b2.(Abs_TSB (Rep_TSB b1 ++ Rep_TSB b2)))"
  by(simp add: cont2cont_LAM cont_Abs_TSB)

(* insert rule for sbUnion *)
lemma tsbunion_insert: "(tb1 \<uplus> tb2) = (Abs_TSB (Rep_TSB tb1 ++ Rep_TSB tb2))"
  by(simp add: tsbUnion_def)

(* if all channels in b1 are also in b2 the union produces b2 *)
lemma tsbunion_idL [simp]: assumes "tsbDom\<cdot>tb1\<subseteq>tsbDom\<cdot>tb2" shows "tb1 \<uplus> tb2 = tb2"
  by (metis Rep_TSB_inverse assms part_add_id tsbdom_insert tsbunion_insert)

lemma tsbunion_idR [simp]: "b \<uplus> (tsbLeast {}) = b"
  by (metis Int_absorb1 Rep_TSB_inverse empty_subsetI map_add_comm part_add_id tsbdom_insert tsbleast_tsdom tsbunion_insert)

(* if b1 and b2 have no common channels, sbUnion is commutative *)
lemma tsbunion_commutative: assumes "tsbDom\<cdot>b1 \<inter> tsbDom\<cdot>b2 = {}"
  shows "b1\<uplus>b2 = b2\<uplus>b1"
  apply(simp add: tsbunion_insert)
  by (metis assms map_add_comm tsbdom_insert)

(* the second argument has priority in sbUnion *)
lemma tsbunion_getchR [simp]: assumes "c\<in>tsbDom\<cdot>b2"
  shows "b1\<uplus>b2  .  c = b2  .  c"
  apply(simp add: tsbunion_insert tsbgetch_insert)
  by (metis assms map_add_dom_app_simps(1) tsbdom_insert)

lemma tsbunion_getchL [simp]: assumes "c\<notin>tsbDom\<cdot>b2"
  shows "b1\<uplus>b2  .  c = b1  .  c"
  apply(simp add: tsbunion_insert tsbgetch_insert)
  by (metis assms map_add_dom_app_simps(3) tsbdom_insert)

lemma tsbunion_restrict3 [simp]: assumes "(tsbDom\<cdot>y)\<inter>(tsbDom\<cdot>x) = {}" 
  shows "(x\<uplus>y) \<bar> tsbDom\<cdot>x = x"
  apply(simp add: tsbunion_insert tsbdom_insert)
  by (metis Abs_TSB_inverse Rep_TSB Rep_TSB_inverse assms map_add_comm map_union_restrict2 mem_Collect_eq tsbdom_insert tsbrestrict_insert tsbunion_well)

lemma tsbunion_restrict2 [simp]:"(x\<uplus>y) \<bar> tsbDom\<cdot>y = y"
  by(simp add: tsbunion_insert tsbdom_insert tsbrestrict_insert)

lemma tsbunion_restrict [simp]: assumes "(tsbDom\<cdot>y)\<inter>cs2 = {}" 
  shows "(x\<uplus>y) \<bar> cs2 = x \<bar> cs2"
  using assms by(simp add: tsbunion_insert tsbrestrict_insert tsbDom_def)

lemma tsbunion_dom [simp]: "tsbDom\<cdot>(tb1 \<uplus> tb2) = tsbDom\<cdot>tb1 \<union> tsbDom\<cdot>tb2"
  by(simp add: tsbdom_insert tsbunion_insert Un_commute)

*)


(* tsbTTake *)
thm tsbTTake_def
lemma tsbttake_well[simp]: "tsb_well (\<lambda>c. (c \<in> tsbDom\<cdot>tb)\<leadsto> ((tb  .  c) \<down> n ))"
  apply(simp add: tsb_well_def)
  apply rule
   apply (metis (full_types) Rep_TSB dual_order.trans mem_Collect_eq tsb_well_def tsbdom_insert tsbgetch_insert tsttake_dom)
  by (metis Rep_TSB mem_Collect_eq tsb_well_def tsbdom_insert tsbgetch_insert)

lemma tsbttake_dom [simp]: "tsbDom\<cdot>(tb \<down> i) = tsbDom\<cdot>tb"
  by(simp add: tsbTTake_def tsbdom_rep_eq)

lemma tsbttake2least: "tb \<down> 0 = tsbLeast (tsbDom\<cdot>tb)"
  apply(rule tsb_eq)
   apply(simp)
  apply simp
  by(simp add: tsbTTake_def tsbgetch_insert)

lemma [simp]: assumes "c\<in>tsbDom\<cdot>tb"
  shows "tb \<down> 0  .  c = \<bottom>"
  by(simp add: tsbttake2least assms)

lemma [simp]: "c\<in>tsbDom\<cdot>tb \<Longrightarrow> tb \<down> n  .  c = tb  .  c \<down>n"
by(simp add: tsbTTake_def tsbgetch_insert)

lemma tsbttake_below [simp]: fixes tb:: "'m TSB"
  shows "(tb \<down> i) \<sqsubseteq> tb"
  by(rule tsb_below, auto)
 

lemma tsbttake_lub [simp] : fixes tb:: "'m TSB"
  shows "(\<Squnion>i. (tb \<down> i)) = tb"
    apply(rule tsb_eq)
    
    oops
    






lemma tsb_newMap_well[simp]: assumes "c\<in>tsbDom\<cdot>b"
  shows "tsb_well [c \<mapsto> b  .  c]"
  apply(simp add: tsbgetch_insert)
  apply (rule tsb_wellI)
   apply (metis (mono_tags) Rep_TSB assms dom_def fun_upd_apply mem_Collect_eq option.sel tsb_well_def tsbdom_insert)
  by auto

lemma tsb_newMap_id[simp]: assumes "{c}=tsbDom\<cdot>b" shows "Abs_TSB [c \<mapsto> b  .  c] = b"
  by (metis Rep_TSB_inverse assms domIff dom_eq_singleton_conv fun_upd_same option.collapse tsbdom_insert tsbgetch_insert)

lemma tsb_newMap_restrict [simp]: assumes "c\<in>tsbDom\<cdot>b"
  shows "Abs_TSB [c \<mapsto> b  .  c] = b \<bar> {c}"
  by (smt Abs_TSB_inverse assms domIff dom_eq_empty_conv dom_eq_singleton_conv fun_upd_upd mem_Collect_eq option.collapse restrict_map_insert subset_singletonD tsbdom_insert tsbgetch_insert tsbrestrict_dom tsbrestrict_insert tsbrestrict_well)








definition tsb_fin_well :: "(channel \<rightharpoonup> 'm tstream) \<Rightarrow> bool" where
"tsb_fin_well f \<equiv> (\<forall>c \<in> dom f. tsDom\<cdot>(f\<rightharpoonup>c) \<subseteq> ctype c) 
           \<and> (\<exists>n. \<forall>c \<in> dom f.  #\<surd>(f\<rightharpoonup>c) = Fin n)"

lemma tsb_fin_exists [simp]: "tsb_fin_well empty"
  by(simp add: tsb_fin_well_def)

typedef ('m :: message) TSB_fin = "{b :: channel \<rightharpoonup> 'm tstream . tsb_fin_well b }"
  using tsb_fin_exists by blast









definition tsb_inf_well :: "(channel \<rightharpoonup> 'm tstream) \<Rightarrow> bool" where
"tsb_inf_well f \<equiv> (\<forall>c \<in> dom f. tsDom\<cdot>(f\<rightharpoonup>c) \<subseteq> ctype c) 
                \<and> (\<forall>c \<in> dom f. #\<surd>(f\<rightharpoonup>c) = \<infinity>)"


lemma tsb_inf_exists [simp]: "tsb_inf_well empty"
  by(simp add: tsb_inf_well_def)

lemma tsb_inf_adm[simp]: "adm (\<lambda>x. \<forall>c\<in>dom x. #\<surd> x\<rightharpoonup>c = \<infinity>)"
  apply(rule admI)
  apply rule+
  by (simp add: contlub_cfun_arg part_dom_lub part_the_chain part_the_lub)


cpodef ('m :: message) TSB_inf = "{b :: channel \<rightharpoonup> 'm tstream . tsb_inf_well b }"
   using tsb_inf_exists apply blast
  by(simp add: tsb_inf_well_def)

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
"tsb2tsbInf tb \<equiv> Abs_TSB_inf (\<lambda>c. (c\<in>tsbDom\<cdot>tb)\<leadsto>(tb  .  c) \<bullet> tsInfTick)"

definition tsbInf2tsb :: "'m TSB_inf \<rightarrow> 'm TSB" where
"tsbInf2tsb \<equiv> \<Lambda> tbi.  Abs_TSB (Rep_TSB_inf tbi)"







(* Allgemeine Lemmas *)
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
  apply(intro_classes)
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
  by (smt assms below_antisym below_option_def fun_below_iff tsbi_blow_eq)

lemma tsbi_option_chain_max_in [simp]: 
  fixes Y:: "nat \<Rightarrow> ('a TSB_inf \<rightharpoonup> 'b TSB_inf)"
  assumes "chain Y"
  shows "max_in_chain 0 Y"
  apply(rule max_in_chainI)
  by (smt assms is_ub_thelub part_dom_lub part_eq part_the_chain tsbi_blow_eq)

lemma tsbi_option_chain_finite [simp]: 
  fixes Y:: "nat \<Rightarrow> ('a TSB_inf \<rightharpoonup> 'b TSB_inf)"
  assumes "chain Y"
  shows "finite_chain Y"
  using assms finite_chainl1 tsbi_option_chain_max_in by blast


lemma tsbi_option_adm [simp]:
  fixes g:: "('a TSB_inf \<rightharpoonup> 'b TSB_inf) \<Rightarrow> bool"
  shows "adm g"
  apply(rule admI)
  by (metis l42 tsbi_option_chain_finite)




(* tsbiDom *)
thm tsbiDom_def

lemma tsbidom_insert: "tsbiDom\<cdot>x = dom (Rep_TSB_inf x)"
  by(simp add: tsbiDom_def)

lemma tsbidom_rep_eq: "tsb_inf_well tbi \<Longrightarrow> tsbiDom\<cdot>(Abs_TSB_inf tbi) = dom tbi"
by(simp add: tsbidom_insert)


lemma [simp]: "tsb_inf_well (\<lambda>c.(c\<in>cs) \<leadsto> tsInfTick)"
by(simp add: tsb_inf_well_def)

lemma tsbiLeast_dom [simp]: "tsbiDom\<cdot>(Abs_TSB_inf (\<lambda>c.(c\<in>cs) \<leadsto> tsInfTick)) = cs"
by(simp add: tsbiDom_def)

lemma tsbi_dom_ex[simp]: "\<exists>tbi. tsbiDom\<cdot>tbi = cs"
using tsbiLeast_dom by blast

lemma tsbi_dom_ex2 [simp]: "\<exists>b. dom (Rep_TSB_inf b) = cs"
using tsbi_dom_ex tsbidom_insert by fastforce


lemma tsbi_ex[simp]: "TSBi cs \<noteq> {}"
by(simp add: TSBi_def)


(* tsbiGetCh *)
thm tsbiGetCh_def

lemma tsbigetch_insert: "tbi  .  c = (Rep_TSB_inf tbi) \<rightharpoonup> c"
by(simp add: tsbiGetCh_def)

lemma tsbigetch_rep_eq: "tsb_inf_well tbi \<Longrightarrow> (Abs_TSB_inf tbi)  .  c = tbi \<rightharpoonup> c"
by(simp add: tsbiGetCh_def)


lemma tsbi_getch_inf [simp]: 
  shows "c\<in>tsbiDom\<cdot>tbi \<Longrightarrow> #\<surd> tbi . c = \<infinity>"
  by(simp add: tsbiGetCh_def tsbiDom_def)

lemma tsbi_getch_type[simp]: "c\<in>tsbiDom\<cdot>tbi \<Longrightarrow> tsDom\<cdot>(tbi  .  c) \<subseteq> ctype c"
apply(simp add: tsbiGetCh_def)
using tsb_inf_well_def tsbidom_insert by fastforce



lemma tsbi_eq: "tsbiDom\<cdot>x = tsbiDom\<cdot>y \<Longrightarrow> (\<And> c. c\<in>tsbiDom\<cdot>x \<Longrightarrow> x . c =y . c) \<Longrightarrow> x=y"
  by (metis (no_types, lifting) Abs_cfun_inverse2 Rep_TSB_inf_inject cont_discrete_cpo part_eq tsbiGetCh_def tsbidom_insert)

lemma tsbi_below: "tsbiDom\<cdot>x = tsbiDom\<cdot>y \<Longrightarrow> (\<And> c. c\<in>tsbiDom\<cdot>x \<Longrightarrow> x . c \<sqsubseteq> y . c) \<Longrightarrow> x\<sqsubseteq>y"
by (metis below_TSB_inf_def part_below tsbidom_insert tsbigetch_insert)





(* tsbiUnion *)

(* tsbUnion produces a welltyped partial-function *)
lemma tsbiunion_well[simp]: assumes "tsb_inf_well b1" and "tsb_inf_well b2"
  shows "tsb_inf_well (b1 ++ b2)"
  apply(simp add: tsb_inf_well_def)
  apply (rule, rule)
   apply (metis (no_types, lifting) Un_iff assms(1) assms(2) map_add_dom_app_simps(1) map_add_dom_app_simps(3) tsb_inf_well_def)
  apply rule
  by (metis (no_types, lifting) Un_iff assms(1) assms(2) map_add_dom_app_simps(1) map_add_dom_app_simps(3) tsb_inf_well_def)


(* insert rule for sbUnion *)
lemma tsbiunion_insert: "(tb1 \<uplus> tb2) = (Abs_TSB_inf (Rep_TSB_inf tb1 ++ Rep_TSB_inf tb2))"
  by(simp add: tsbiUnion_def)

(* if all channels in b1 are also in b2 the union produces b2 *)
lemma tsbiunion_idL:  "tsbiDom\<cdot>tb1\<subseteq>tsbiDom\<cdot>tb2 \<Longrightarrow> tb1 \<uplus> tb2 = tb2"
  by (simp add: Rep_TSB_inf_inverse tsbidom_insert tsbiunion_insert)

(* if b1 and b2 have no common channels, sbUnion is commutative *)
lemma tsbiunion_commutative: "tsbiDom\<cdot>b1 \<inter> tsbiDom\<cdot>b2 = {} \<Longrightarrow> b1\<uplus>b2 = b2\<uplus>b1"
  apply(simp add: tsbiunion_insert)
  by (metis assms map_add_comm tsbidom_insert)


(* the second argument has priority in sbUnion *)
lemma tsbiunion_getchR [simp]:
  shows "c\<in>tsbiDom\<cdot>b2 \<Longrightarrow> b1\<uplus>b2  .  c = b2  .  c"
  apply(simp add: tsbiunion_insert tsbiGetCh_def )
  by (simp add: map_add_dom_app_simps(1) tsbidom_insert)

lemma tsbiunion_getchL [simp]: "c\<notin>tsbiDom\<cdot>b2 \<Longrightarrow> b1\<uplus>b2  .  c = b1  .  c"
  apply(simp add: tsbiunion_insert tsbiGetCh_def)
  by (metis assms map_add_dom_app_simps(3) tsbidom_insert)

lemma tsbiunion_dom [simp]: "tsbiDom\<cdot>(tb1 \<uplus> tb2) = tsbiDom\<cdot>tb1 \<union> tsbiDom\<cdot>tb2"
  by(simp add: tsbidom_insert tsbiunion_insert Un_commute)

lemma tsbiunion_assoc [simp]: fixes x y z :: "'m TSB_inf"
  shows "(x \<uplus> y) \<uplus> z = x \<uplus> (y \<uplus> z)"
by(simp add: tsbiunion_insert)






(* tsbiRestrict *)
lemma [simp]: "tsb_inf_well (Rep_TSB_inf b |` cs)"
  apply(simp add: tsb_inf_well_def)
  by (metis IntD1 Rep_TSB_inf mem_Collect_eq tsb_inf_well_def)

lemma tsbirestrict_insert: "tbi \<bar> cs = Abs_TSB_inf (Rep_TSB_inf tbi |` cs)"
  by(simp add: tsbiRestrict_def)

lemma tsbirestrict_dom [simp]: "tsbiDom\<cdot>(tb \<bar> cs) \<subseteq> cs"
  by(simp add: tsbiRestrict_def tsbidom_insert)

lemma tsbiresrict_dom2 [simp]: "cs \<subseteq> tsbiDom\<cdot>tb \<Longrightarrow> tsbiDom\<cdot>(tb \<bar> cs) = cs"
  apply(simp add: tsbidom_insert tsbiRestrict_def)
  by blast

lemma tsbirestrict_dom3: "tsbiDom\<cdot>(tb \<bar> cs) = tsbiDom\<cdot>tb \<inter> cs"
  by(simp add: tsbidom_insert tsbiRestrict_def)

lemma [simp]: fixes tb :: "'m TSB_inf"
  shows "(tb \<bar> cs1) \<bar> cs2 = tb \<bar> (cs1\<inter>cs2)"
  by(simp add: tsbiRestrict_def)

lemma tsbirestrict_dom2 [simp]: "tsbiDom\<cdot>(tb \<bar> cs) = cs \<Longrightarrow> cs \<subseteq> tsbiDom\<cdot>tb"
  by(auto simp add: assms tsbidom_insert tsbiRestrict_def)

lemma tsbiRestrict_getch [simp]:  "c \<in> cs \<Longrightarrow> tbi \<bar> cs . c   = tbi . c " 
by (simp add: tsbirestrict_insert tsbiGetCh_def)


lemma tsbiunion_restrict3 [simp]: "(tsbiDom\<cdot>y)\<inter>(tsbiDom\<cdot>x) = {} \<Longrightarrow> (x\<uplus>y) \<bar> tsbiDom\<cdot>x = x"
  apply(simp add: tsbidom_insert tsbiRestrict_def tsbiunion_insert)
  by (metis Int_absorb Rep_TSB_inf_inverse map_union_restrict2 restrict_restrict)

lemma tsbiunion_restrict2 [simp]:"(x\<uplus>y) \<bar> tsbiDom\<cdot>y = y"
  by(simp add: tsbiunion_insert tsbidom_insert tsbiRestrict_def)

lemma tsbiunion_restrict [simp]:"(tsbiDom\<cdot>y)\<inter>cs2 = {} \<Longrightarrow> (x\<uplus>y) \<bar> cs2 = x \<bar> cs2"
  using assms by(simp add: tsbiunion_insert tsbirestrict_insert tsbiDom_def)











(* tsbiTTake *)
thm tsbiTTake_def
lemma tsbittake_well[simp]: "tsb_well (\<lambda>c. (c \<in> tsbiDom\<cdot>tbi)\<leadsto>tbi . c \<down> n )"
  apply(rule tsb_wellI)
   apply simp
   apply (meson order.trans tsbi_getch_type tsttake_dom)
  by (simp add: tsbiGetCh_def tsbidom_insert)


lemma tsbittake_getch [simp]: fixes tsbi:: "'m TSB_inf"
  shows "c\<in>tsbiDom\<cdot>tsbi \<Longrightarrow> tsbi \<down> n  .  c = tsbi . c \<down>n"
by(simp add: tsbiTTake_def tsbgetch_insert)

lemma tsbiGetCh_rep_eq: "tsb_inf_well tbi \<Longrightarrow> (Abs_TSB_inf tbi)  .  c = tbi \<rightharpoonup> c "
by(simp add: tsbiGetCh_def)


lemma [simp]: "tsbDom\<cdot>(tbi \<down> n) = tsbiDom\<cdot>tbi"
by(simp add: tsbiTTake_def tsbdom_insert)


lemma tsbiTtake_chain [simp]: fixes tbi :: "'a TSB_inf"
  shows "chain (\<lambda>i. tbi \<down> i)"
  apply(rule chainI)
  apply(rule tsb_below)
   apply simp
  by simp









(* tsb2tsbInf *)
thm tsb2tsbInf_def

lemma [simp]: "tsb_inf_well (\<lambda>c. (c\<in>tsbDom\<cdot>tb)\<leadsto>(tb  .  c) \<bullet> tsInfTick)"
  by(simp add: tsb_inf_well_def tsbgetch_insert)

lemma tsb2tsbInf_dom [simp]: "tsbiDom\<cdot>(tsb2tsbInf tb) = tsbDom\<cdot>tb"
  by(simp add: tsb2tsbInf_def tsbidom_insert)

lemma rep_tsbi_tsb_well [simp]: "tsb_well (Rep_TSB_inf tbi)"
  using Rep_TSB_inf tsb_inf_well_def tsb_well_def by fastforce

lemma tsbinf2tsb_insert: "tsbInf2tsb\<cdot>tbi = Abs_TSB (Rep_TSB_inf tbi)"
  by(simp add: tsbInf2tsb_def)

lemma [simp]: "tsbDom\<cdot>(tsbInf2tsb\<cdot>tbi) =tsbiDom\<cdot>tbi"
  by(simp add: tsbdom_insert tsbinf2tsb_insert tsbidom_insert)

lemma tsbInf2tsb_getch [simp]: "tsbInf2tsb\<cdot>tb  . c = tb .  c"
by(simp add: tsbInf2tsb_def tsbgetch_insert tsbigetch_insert)


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
  hence "b1  .  c \<down> n = b2  . c \<down> n" using c_def c_def2 by(subst tsSucTake; auto) 
  thus " b1\<down>n  .  c = b2\<down>n  .  c" by (simp add: c_def dom_eq c_def2)
qed




end





