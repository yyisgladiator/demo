theory If_Else_Continuity
imports Main Cfun SetPcpo
begin

lemma bool_cont_implies_lub : "cont pred \<Longrightarrow> chain Y \<Longrightarrow> (\<And>i. pred (Y i)) \<Longrightarrow> pred (Lub Y)" by (smt cont_def fun.set_map imageE lub_const lub_eq lub_eqI)

lemma bool_cont_implies_not_lub : "cont pred \<Longrightarrow> chain Y \<Longrightarrow> (\<And>i. \<not> pred (Y i)) \<Longrightarrow> \<not> pred (Lub Y)" by (simp add: cont2contlubE is_lub_const is_lub_rangeD1 lub_chain_maxelem)

lemma bool_mono_implies_adm : "monofun pred \<Longrightarrow> adm pred" 
proof -
  assume asm : "monofun pred"
  have "\<And>Y. chain Y \<Longrightarrow> (\<forall>i. pred (Y i)) \<Longrightarrow> pred (Lub Y)"
  proof -
    fix Y :: "nat \<Rightarrow> 'a"
    assume chainY : "chain Y"
    and "(\<forall>i. pred (Y i))"
    then obtain true_i where true_i_def : "pred (Y true_i)" by simp
    hence "Y true_i \<sqsubseteq> Lub Y" using chainY is_ub_thelub by blast
    hence "pred (Y true_i) \<sqsubseteq> pred (Lub Y)" by (simp add: asm monofunE)
    thus "pred (Lub Y)" by (simp add: SetPcpo.less_bool_def true_i_def)
  qed
  thus "adm pred" by (simp add: adm_def)
qed

lemma bool_cont_implies_adm : "cont pred \<Longrightarrow> adm pred" by (simp add: bool_mono_implies_adm cont2mono)


instantiation nat :: po
begin

definition below_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool"  where
"below_nat \<equiv> op \<le>"

instance by intro_classes (simp_all add: below_nat_def)
end

definition set_below :: "'a::po set \<Rightarrow> 'a set \<Rightarrow> bool" where
"set_below S1 S2 = (\<forall>x\<in>S1. \<forall>y\<in>S2. x \<sqsubseteq> y)"

lemma ubS2_is_ubS1 : "\<lbrakk>set_below S1 S2; \<exists>x. x \<in> S2; S2 <| l\<rbrakk> \<Longrightarrow> S1 <| l"
proof (rule ccontr)
  assume below : "set_below S1 S2"
  and S2_not_empty : "\<exists>x. x \<in> S2"
  and ubS2 : "S2 <| l"
  and contr : "\<not> S1 <| l"
  then obtain greater_x where greater_x_def : "greater_x \<in> S1 \<and> \<not> greater_x \<sqsubseteq> l" using is_ubI by blast
  obtain inS2 where inS2_def : "inS2 \<in> S2" using S2_not_empty by auto
  hence "greater_x \<sqsubseteq> inS2" using below greater_x_def set_below_def by blast
  thus False using box_below greater_x_def inS2_def is_ubD ubS2 by blast
qed

lemma lubS2_is_lub_union : "\<lbrakk>set_below S1 S2; \<exists>x. x \<in> S2; S2 <<| x\<rbrakk> \<Longrightarrow> S1 \<union> S2 <<| x"
by (smt HOLCF_trans_rules(1) Un_iff is_lub_def is_ub_def set_below_def)

primrec restr :: "(nat \<Rightarrow> 'a::cpo) \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a" where
"restr Y S 0 = Y (LEAST i. Y i \<in> S)" |
"restr Y S (Suc n) = (if Y (Suc n) \<in> S then Y (Suc n) else restr Y S n)"

lemma restr_unchanged_on_S : "Y j \<in> S \<Longrightarrow> restr Y S j = Y j" by (metis Least_eq_0 old.nat.exhaust restr.simps(1) restr.simps(2))

theorem restr_ends_in_Y : "chain Y \<Longrightarrow> (\<And>i. \<exists>j. restr Y S i = Y j)" 
proof -
  assume chainY : "chain Y"
  fix i :: nat
  show "\<exists>j. restr Y S i = Y j"
  proof (induct i)
    show "\<exists>j. restr Y S 0 = Y j" by auto
    show "\<And>i. \<exists>j. restr Y S i = Y j \<Longrightarrow> \<exists>j. restr Y S (Suc i) = Y j" by auto
  qed
qed

theorem restr_ends_in_S : "chain Y \<Longrightarrow> \<exists>x. x \<in> range Y \<inter> S \<Longrightarrow> range (restr Y S) \<subseteq> S"
proof -
  assume chainY : "chain Y"
  and intersection_not_empty : " \<exists>x. x \<in> range Y \<inter> S "
  have "\<And>i. (restr Y S) i \<in> S" 
  proof -
    fix i :: nat
    show "restr Y S i \<in> S"
    proof (induct i)
      show "restr Y S 0 \<in> S"  by (metis restr.simps(1) Int_iff LeastI imageE intersection_not_empty)
      
      fix i :: nat
      show "restr Y S i \<in> S \<Longrightarrow> restr Y S (Suc i) \<in> S"
      proof (cases "Y i \<in> S")
        case True
        thus ?thesis by (simp add: restr_unchanged_on_S)
        next

        assume inductive_asm : "restr Y S i \<in> S"
        case False
        thus ?thesis by (simp add: inductive_asm)
      qed
    qed
  qed
  thus ?thesis by blast
qed

lemma restr_range : "chain Y \<Longrightarrow> \<exists>x. x \<in> range Y \<inter> S \<Longrightarrow> range (restr Y S) = range Y \<inter> S" 
proof -
  assume chainY : "chain Y"
  and intersection_not_empty : " \<exists>x. x \<in> range Y \<inter> S "
  have restr_subs_inter : "range (restr Y S) \<subseteq> range Y \<inter> S" using chainY intersection_not_empty restr_ends_in_S restr_ends_in_Y by fastforce
  have "range Y \<inter> S \<subseteq> range (restr Y S)" by (smt image_iff inf_le1 inf_le2 restr_unchanged_on_S subsetCE subsetI)
  thus ?thesis using restr_subs_inter by blast
qed

theorem below_least : "chain Y \<Longrightarrow> i \<sqsubseteq> (LEAST i. Y i \<in> S) \<Longrightarrow> restr Y S i = restr Y S 0" 
proof (induct i)
  show "chain Y \<Longrightarrow> 0 \<sqsubseteq> (LEAST i. Y i \<in> S) \<Longrightarrow> restr Y S 0 = restr Y S 0" by blast
  
  fix i :: nat
  assume inductive_asm : "chain Y \<Longrightarrow> i \<sqsubseteq> (LEAST i. Y i \<in> S) \<Longrightarrow> restr Y S i = restr Y S 0"
  show "chain Y \<Longrightarrow> Suc i \<sqsubseteq> (LEAST i. Y i \<in> S) \<Longrightarrow> restr Y S (Suc i) = restr Y S 0"
  proof (cases "Y (Suc i) \<in> S")
    assume chainY : "chain Y"
    and least : "Suc i \<sqsubseteq> (LEAST i. Y i \<in> S)"
    case True
    hence "Suc i = (LEAST i. Y i \<in> S)" using least by (simp add: Least_le below_nat_def po_eq_conv)
    thus ?thesis by (metis True restr.simps(1) restr.simps(2))
    next

    assume chainY : "chain Y"
    and least : "Suc i \<sqsubseteq> (LEAST i. Y i \<in> S)"
    case False
    thus ?thesis using below_nat_def below_refl below_trans chainY inductive_asm le_Suc_eq local.least restr.simps(2) by auto
  qed
qed

theorem above_least : 
  assumes "chain Y" and "\<exists>x. x \<in> (range Y) \<inter> S"
  shows "(LEAST i. Y i \<in> S) \<sqsubseteq> i \<Longrightarrow> restr Y S i \<sqsubseteq> Y i"
proof (induct i)
  show "(LEAST i. Y i \<in> S) \<sqsubseteq> 0 \<Longrightarrow> restr Y S 0 \<sqsubseteq> Y 0" by (simp add: below_nat_def)

  fix i :: nat
  assume inductive_asm : "((LEAST i. Y i \<in> S) \<sqsubseteq> i \<Longrightarrow> restr Y S i \<sqsubseteq> Y i)"
  show "(LEAST i. Y i \<in> S) \<sqsubseteq> Suc i \<Longrightarrow> restr Y S (Suc i) \<sqsubseteq> Y (Suc i)"
  proof (cases "Y (Suc i) \<in> S")
    assume asm : "(LEAST i. Y i \<in> S) \<sqsubseteq> Suc i"
    case False
    hence "(LEAST i. Y i \<in> S) \<sqsubseteq> i" by (metis Int_iff LeastI asm assms(2) below_nat_def imageE le_Suc_eq)
    thus ?thesis using assms(1) box_below inductive_asm po_class.chainE by fastforce
    next
    
    case True
    thus ?thesis by (simp add: po_eq_conv restr_unchanged_on_S)
  qed
qed

theorem restr_increases : 
  assumes "chain Y" and "\<exists>x. x \<in> (range Y) \<inter> S"
  shows "Y j \<sqsubseteq> restr Y S i \<Longrightarrow> Y j \<sqsubseteq> restr Y S (Suc i)" 
proof (induct i)
  show "Y j \<sqsubseteq> restr Y S 0 \<Longrightarrow> Y j \<sqsubseteq> restr Y S (Suc 0)" by (smt assms(1) below_least below_nat_def below_trans nat_le_linear po_class.chain_mono restr.simps(1) restr.simps(2))
  
  fix i :: nat
  assume inductive_asm : "Y j \<sqsubseteq> restr Y S i \<Longrightarrow> Y j \<sqsubseteq> restr Y S (Suc i)"
  show "Y j \<sqsubseteq> restr Y S (Suc i) \<Longrightarrow> Y j \<sqsubseteq> restr Y S (Suc (Suc i))"
  proof (cases "(LEAST i. Y i \<in> S) \<sqsubseteq> (Suc (Suc i))")
    assume asm : "Y j \<sqsubseteq> restr Y S (Suc i)"
    case True
    show ?thesis
    proof (cases "Y (Suc (Suc i)) \<in> S")
      case True
      thus ?thesis by (smt above_least asm assms(1) assms(2) below_least below_nat_def box_below nat_le_linear po_class.chainE po_class.chain_mono restr.simps(1) restr.simps(2))
      next
      
      case False
      thus ?thesis using asm restr.simps(2) by auto
    qed
    next
    
    assume asm : "Y j \<sqsubseteq> restr Y S (Suc i)"
    case False 
    show ?thesis
    proof (cases "Y (Suc (Suc i)) \<in> S")
      case True
      thus ?thesis using False Least_le below_nat_def by fastforce
      next
      
      case False
      thus ?thesis using asm restr.simps(2) by auto
    qed
  qed
qed

lemma restr_is_chain :
  assumes "chain Y" and "\<exists>x. x \<in> (range Y) \<inter> S"
  shows "chain (restr Y S)"
by (metis assms(1) assms(2) below_refl po_class.chainI restr_ends_in_Y restr_increases)

lemma restr_finite_is_finite : "finite_chain Y \<Longrightarrow> \<exists>x. x \<in> (range Y) \<inter> S \<Longrightarrow> finite_chain (restr Y S)"
by (metis finch_imp_finite_range finite_Int finite_chain_def finite_range_imp_finch restr_is_chain restr_range)



definition non_finite_subchain :: "(nat \<Rightarrow> 'a::cpo) \<Rightarrow> (nat \<Rightarrow> 'a::cpo) \<Rightarrow> bool" where
"non_finite_subchain X Y \<equiv> chain X \<and> chain Y \<and> (range X \<subseteq> range Y) \<and> \<not> finite_chain X"

definition unbounded_subchain :: "(nat \<Rightarrow> 'a::cpo) \<Rightarrow> (nat \<Rightarrow> 'a::cpo) \<Rightarrow> bool" where
"unbounded_subchain X Y \<equiv> chain X \<and> chain Y \<and> (range X \<subseteq> range Y) \<and> (\<forall>i. \<exists>j. Y i \<sqsubseteq> X j)"

lemma "chain X \<and> \<not> finite_chain X \<Longrightarrow> (\<And>i. \<exists>j. X i \<noteq> X j \<and> X i \<sqsubseteq> X j)"
using finite_chain_def max_in_chain_def po_class.chain_mono by blast

theorem non_finite_is_unbounded_subchain : "non_finite_subchain X Y \<Longrightarrow> unbounded_subchain X Y"
proof -
  assume asm : "non_finite_subchain X Y"
  have "\<forall>i. \<exists>j. Y i \<sqsubseteq> X j"
  proof (rule allI)
    fix i :: nat
    show  "\<exists>j. Y i \<sqsubseteq> X j"
    proof (induct i)
      show "\<exists>j. Y 0 \<sqsubseteq> X j" by (metis (mono_tags, hide_lams) asm le0 non_finite_subchain_def po_class.chain_mono rangeE rangeI subsetCE)
    
      fix i :: nat
      assume inductive_asm : "\<exists>j. Y i \<sqsubseteq> X j"
      have "(\<And>i. \<exists>j. X i \<noteq> X j \<and> X i \<sqsubseteq> X j)" by (metis asm finite_chain_def max_in_chain_def non_finite_subchain_def po_class.chain_mono)
      then obtain larger_j where larger_j_def :  "Y i \<noteq> X larger_j \<and> Y i \<sqsubseteq> X larger_j" using inductive_asm by metis
      then obtain larger_i where "Y larger_i = X larger_j" by (meson UNIV_I asm f_inv_into_f image_subset_iff non_finite_subchain_def)
      thus "\<exists>j. Y (Suc i) \<sqsubseteq> X j" by (metis Suc_leI asm below_antisym chain_mono_less larger_j_def linorder_neqE_nat non_finite_subchain_def po_class.chain_mono)
    qed
  qed
  thus ?thesis by (meson asm non_finite_subchain_def unbounded_subchain_def)
qed
  
lemma unbounded_subchain_same_lub : "unbounded_subchain X Y \<Longrightarrow> Lub X = Lub Y" 
by (meson below_antisym below_lub lub_below lub_range_mono unbounded_subchain_def)

lemma non_finite_subchain_same_lub : "non_finite_subchain X Y \<Longrightarrow> Lub X = Lub Y" 
by (simp add: non_finite_is_unbounded_subchain unbounded_subchain_same_lub)


definition monotone_on_sets :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"monotone_on_sets f S1 S2 \<equiv> set_below S1 S2 \<and> (\<forall>x\<in>S1. \<forall>y\<in>S2. f x \<sqsubseteq> f y)"

lemma monotone_set_below : "monotone_on_sets f S1 S2 \<Longrightarrow> set_below (f ` S1) (f ` S2)"
by (simp add: monotone_on_sets_def set_below_def)

definition cont_at :: "('a::cpo \<Rightarrow> 'b::cpo) \<Rightarrow> 'a set \<Rightarrow> bool" where
"cont_at f S = (\<forall>Y. chain Y \<and> (\<forall>i. Y i \<in> S) \<longrightarrow> range (f \<circ> Y) <<| f (Lub Y))"

lemma cont_at_univ : "cont_at f (UNIV :: ('a::cpo) set) \<Longrightarrow> cont f"
by (metis UNIV_I cont_def cont_at_def fun.set_map range_composition)

theorem cont_union : 
  fixes f :: "'a::cpo \<Rightarrow> 'b::cpo"
  assumes "cont_at f S1" and "cont_at f S2" and "monotone_on_sets f S1 S2"
  shows "cont_at f (S1 \<union> S2)" unfolding cont_at_def
proof (rule allI)
  fix Y :: "nat \<Rightarrow> 'a::cpo"
  have "chain Y \<and> (\<forall>i. Y i \<in> S1 \<union> S2) \<Longrightarrow> range (f \<circ> Y) <<| f (Lub Y)"
  proof (cases "range Y \<subseteq> S1")
    assume asm : "chain Y \<and> (\<forall>i. Y i \<in> S1 \<union> S2)"
    case True
    thus ?thesis by (meson True UNIV_I asm assms(1) cont_at_def image_subset_iff)
    next

    assume asm : "chain Y \<and> (\<forall>i. Y i \<in> S1 \<union> S2)"
    case False
    def YinS2 \<equiv> "restr Y S2"
    hence chainYinS2 : "chain YinS2" using False Int_iff Un_iff asm image_subsetI rangeI restr_is_chain by fastforce

    have range_of_comp_is_intersection : "range (f \<circ> YinS2) = f ` (range Y \<inter> S2)" by (smt False Int_iff UnE YinS2_def asm fun.set_map imageE restr_range subsetI)

    have map_union_commutes : "f ` (range Y \<inter> S1) \<union> f ` (range Y \<inter> S2) = f ` range Y" using asm by blast

    have "set_below (range Y \<inter> S1) (range Y \<inter> S2)" by (meson Int_lower2 assms(3) monotone_on_sets_def set_below_def set_rev_mp)
    hence YinS1_below_YinS2 : "set_below (f ` (range Y \<inter> S1))  (f ` (range Y \<inter> S2))" by (meson assms(3) inf_sup_ord(2) monotone_on_sets_def monotone_set_below subset_iff)

    have intersection_not_empty : "\<exists>x. x \<in> range Y \<inter> S2" using False asm by blast

    hence YinS2_sub_S2 : "(\<forall>i. YinS2 i \<in> S2)" using YinS2_def asm restr_range by fastforce

    hence cont_at_subst : "range (f \<circ> YinS2) <<| f (Lub YinS2)" using assms(2) chainYinS2 cont_at_def by blast

    have ex_in_S2 : "\<exists>i. YinS2 i \<in> S2" by (metis False UnE YinS2_def asm image_subsetI restr_unchanged_on_S)

    show ?thesis 
    proof (cases "finite_chain Y")
      case True
      hence "Lub Y \<in> S2" by (metis (no_types, lifting) UnE YinS2_def asm assms(3) below_antisym ex_in_S2 is_ub_thelub lub_eqI lub_finch2 monotone_on_sets_def restr_ends_in_Y set_below_def)
      hence "Lub YinS2 = Lub Y" by (smt Int_iff Int_lower1 True YinS2_def asm below_antisym chainYinS2 finch_imp_finite_range finite_range_imp_finch finite_subset is_lubD1 is_ubD lub_eqI lub_finch2 rangeI restr_range)
      thus ?thesis by (metis cont_at_subst YinS1_below_YinS2 fun.set_map lubS2_is_lub_union map_union_commutes rangeI range_of_comp_is_intersection)
      next

      case False
      have "\<not> finite_chain YinS2"
      proof (rule ccontr, simp)
        assume contr : "finite_chain YinS2"
        then obtain lubInS2 where lubInS2_def : "Y lubInS2 = Lub YinS2" by (metis YinS2_def asm lub_eqI lub_finch2 restr_ends_in_Y)
        hence "\<And>i. Y i \<sqsubseteq> Y lubInS2" by (metis UnE YinS2_def YinS2_sub_S2 asm assms(3) chainYinS2 contr is_ub_thelub lub_eqI lub_finch2 monotone_on_sets_def restr_unchanged_on_S set_below_def)
        hence "\<exists>i. \<forall>j. Y j \<sqsubseteq> Y i" by auto
        hence "finite_chain Y" by (metis asm below_antisym finite_chain_def max_in_chain_def po_class.chain_mono)
        thus False using False by auto
      qed
      hence "Lub YinS2 = Lub Y" by (metis YinS2_def asm chainYinS2 image_subsetI non_finite_subchain_def non_finite_subchain_same_lub rangeI restr_ends_in_Y)
      thus ?thesis by (metis cont_at_subst YinS1_below_YinS2 fun.set_map lubS2_is_lub_union map_union_commutes rangeI range_of_comp_is_intersection)
    qed
  qed
  thus "chain Y \<and> (\<forall>i. Y i \<in> S1 \<union> S2) \<longrightarrow> range (f \<circ> Y) <<| f (Lub Y)" by blast
qed

theorem if_else_cont : 
  assumes "cont_at if_branch {x. pred x}"
  and "cont_at else_branch {x. \<not> pred x}"
  and "cont pred"
  and "\<And>x y. (\<not> pred x \<and> pred y) \<Longrightarrow> x \<sqsubseteq> y"
  and "\<And>x y. (\<not> pred x \<and> pred y) \<Longrightarrow>  else_branch x \<sqsubseteq> if_branch y"
  shows "cont (\<lambda>x. if pred x then if_branch x else else_branch x)"
proof -
  def f \<equiv> "\<lambda>x. if pred x then if_branch x else else_branch x"
  have cont_true : "cont_at f {x. pred x}" unfolding cont_at_def by (smt assms(1) assms(3) bool_cont_implies_lub cont_at_def f_def fun.map_cong0 imageE mem_Collect_eq)
  have cont_false : "cont_at f {x. \<not> pred x}" unfolding cont_at_def by (smt assms(2) assms(3) bool_cont_implies_not_lub cont_at_def f_def fun.map_cong0 imageE mem_Collect_eq)
  have "set_below {x. \<not> pred x} {x. pred x}" by (simp add: assms(4) set_below_def)
  hence "monotone_on_sets f {x. \<not> pred x} {x. pred x} " by (simp add: assms(5) f_def monotone_on_sets_def)
  hence cont_at_union : "cont_at f ({x. pred x} \<union> {x. \<not> pred x})"by (metis cont_false cont_true cont_union sup_commute)
  have "{x. pred x} \<union> {x. \<not> pred x} = (UNIV :: 'a set)" by blast
  hence "cont_at f (UNIV :: 'a set)" using cont_at_union by simp
  thus ?thesis using cont_at_univ cont_def f_def image_cong by blast
qed

theorem equalizing_pred_cont :
  assumes "cont_at if_branch {x. pred x}"
  and "cont_at else_branch {x. \<not> pred x}"
  and "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> pred x = pred y"
  shows "cont (\<lambda>x. if pred x then if_branch x else else_branch x)"
proof -
  def f \<equiv> "\<lambda>x. if pred x then if_branch x else else_branch x" 
  have "\<And>Y. chain Y \<Longrightarrow> range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
  proof - 
    fix Y :: "nat \<Rightarrow> 'a"
    assume chainY : "chain Y"
    show "range (\<lambda>i. f (Y i)) <<| f (\<Squnion>i. Y i)"
    proof (cases "\<forall>i. pred (Y i)")
      case True
      hence "range (if_branch \<circ> Y) <<| if_branch (Lub Y)" by (meson assms(1) chainY cont_at_def mem_Collect_eq)
      thus ?thesis by (metis (mono_tags, lifting) True assms(3) chainY comp_apply f_def image_cong is_ub_thelub)
      next

      case False
      have all_false : "\<forall>i. \<not> pred (Y i)" using False assms(3) chainY is_ub_thelub by blast
      hence "range (else_branch \<circ> Y) <<| else_branch (Lub Y)" by (metis assms(2) chainY cont_at_def mem_Collect_eq)
      thus ?thesis by (metis (mono_tags, lifting) all_false assms(3) chainY comp_apply f_def image_cong is_ub_thelub)
    qed
  qed
  thus ?thesis by (smt contI f_def image_cong)
qed

end
