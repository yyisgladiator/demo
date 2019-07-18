section \<open>Prelude\<close>

theory Prelude
imports HOLCF
begin

default_sort type

(* allows to use lift_definition for continuous functions *)
setup_lifting type_definition_cfun

text \<open>SMT-Proofs are not allowed in the AFP, so don't generate them\<close>
sledgehammer_params [smt_proofs=false]

text \<open>Helpful lemmas to work with HOL and HOLCF's definitions.\<close>

lemma trivial[simp]: "(Not \<circ> Not) = id"
  by auto

text \<open>Convert a relation to a map (function with \<open>option\<close>al result).\<close>
definition rel2map ::   "('c * 'm) set \<Rightarrow> ('c \<rightharpoonup> 'm)"
where rel2map_def: "rel2map r \<equiv> \<lambda>x. (if x \<in> Domain r then Some (SOME a. (x,a) \<in> r) else None)"

text \<open>Domain of rel2map.\<close>
lemma [simp]: "Map.dom (rel2map r) = Domain r"
by (simp add: rel2map_def Map.dom_def)

text \<open>Unwrapping an \<open>'a option\<close> value. Result for \<open>None\<close> is undefined.\<close>
definition unsome :: "'a option \<Rightarrow> 'a" where
"unsome x = (case x of Some y \<Rightarrow> y | None \<Rightarrow> undefined)"

text \<open>Unsome is the inverse of Some.\<close>
lemma [simp]: "unsome (Some x) = x"
by (simp add: unsome_def)

text \<open>For natural numbers j and k with @{term "j \<le> k"}, @{term "k - j"} is natural as well\<close>
lemma natl1: "(j::nat) \<le> k \<Longrightarrow> \<exists>i. j + i = k"
apply (simp add: atomize_imp)
apply (rule_tac x="j" in spec)
apply (induct_tac k, auto)
by (case_tac "x", auto)

text \<open>Commutation on natural numbers\<close>
lemma natl2: "(i::nat) + k = k + i"
by auto

text \<open>Removing successive duplicates from a list:\<close>
primrec lrcdups :: "'a list \<Rightarrow> 'a list"
where
  "lrcdups [] = []" |
  "lrcdups (x#xs) = 
     (if xs = [] 
        then [x] 
        else 
          (if x = List.hd xs 
             then lrcdups xs 
             else (x#(lrcdups xs))))"


(* ----------------------------------------------------------------------- *)
section \<open>Some auxiliary HOLCF lemmas\<close>
(* ----------------------------------------------------------------------- *)

subsection \<open>cfun\<close> 
  
text \<open>Introduction of continuity of \<open>f\<close> using monotonicity and lub on chains:\<close>
lemma contI2:
  "\<lbrakk>monofun (f::'a::cpo \<Rightarrow> 'b::cpo); 
        (\<forall>Y. chain Y \<longrightarrow> f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i)))\<rbrakk> \<Longrightarrow> cont f"
apply (rule contI)
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule monofunE [of f], assumption)
apply (rule is_ub_thelub, assumption)
apply (erule_tac x="Y" in allE, drule mp, assumption)
apply (rule_tac y="\<Squnion>i. f (Y i)" in below_trans, assumption)
apply (rule is_lub_thelub)
by (rule ch2ch_monofun [of f], assumption+)

text \<open>The higher-order function, which takes as input f and yields the result of 
the application of on x, is a continous function.\<close>
lemma [simp]: "cont (\<lambda> f. f x)"
apply (rule contI)
apply (subst lub_fun, assumption)
apply (rule thelubE)
apply (rule ch2ch_fun, assumption)
by (rule refl)

text \<open>In a chain, every two elements are comparable\<close>
lemma chain_tord: "chain S \<Longrightarrow> S k \<sqsubseteq> S j \<or> S j \<sqsubseteq> S k"
apply (insert linear [of "j" "k"])
apply (erule disjE)
apply (rule disjI2)
apply (rule chain_mono,simp+)
apply (rule disjI1)
by (rule chain_mono,simp+)

text \<open>Every non-empty set contains an element\<close>
lemma neq_emptyD: "s \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> s"
by auto

(* below lemmata *)   
lemma cont_pref_eq1I: assumes "(a \<sqsubseteq> b)"
  shows "f\<cdot>a \<sqsubseteq> f\<cdot>b"
  by (simp add: assms monofun_cfun_arg)
     
lemma cont_pref_eq2I:  assumes "(a \<sqsubseteq> b)"
  shows "f\<cdot>x\<cdot>a \<sqsubseteq> f\<cdot>x\<cdot>b"
  by (simp add: assms monofun_cfun_arg)
    
(* equality lemmata *)    
lemma cfun_arg_eqI:  assumes "(a = b)"
  shows "f\<cdot>a = f\<cdot>b"
  by (simp add: assms)  

     
(* ----------------------------------------------------------------------- *)
section \<open>More functions\<close>
(* ----------------------------------------------------------------------- *)

text \<open>This section introduces some more functions to work with lists.\<close>

text \<open>Range shifting on least upper bound of chains.\<close>
lemma less_lubl1: 
  "\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); X \<sqsubseteq> (\<Squnion>k. Y (k + j))\<rbrakk> \<Longrightarrow> X \<sqsubseteq> (\<Squnion>k. Y k)"
by (subst lub_range_shift [THEN sym, of "Y" "j"], simp+)

text \<open>Another lemma on range shifting on least upper bound of chains.\<close>
lemma less_lubl2:
"\<lbrakk>chain (Y::nat \<Rightarrow> 'a::cpo); chain f; \<And>x. (\<Squnion>k. f k\<cdot>x) = x; \<And>n. f n\<cdot>x \<sqsubseteq> (f n\<cdot>(Lub Y))\<rbrakk> \<Longrightarrow> x \<sqsubseteq> Lub Y"
by (insert lub_mono [of "\<lambda>n. f n\<cdot>x" "\<lambda>n. f n\<cdot>(Lub Y)"], simp)

text \<open>Using the constructur Suc, show that n + 1 = 1 + n.\<close>
lemma Suc2plus: "Suc n = Suc 0 + n"
by simp

text \<open>Similar lemma as above, using the constructur Suc.\<close>
lemma Suc_def2: "Suc i = i + Suc 0"
by simp

text \<open>If a chain contains its least upper bound as an element, this element is the
  maximum of the chain\<close>
lemma max_in_chainI3: "\<lbrakk>chain (Y::nat\<Rightarrow>'a::cpo); Y i = Lub Y\<rbrakk> \<Longrightarrow> max_in_chain i Y"
apply (simp add: max_in_chain_def)
apply (rule allI, rule impI)
apply (rule po_eq_conv [THEN iffD2])
apply (rule conjI)
apply (drule sym, simp)
apply (rule chain_mono, assumption+)
by (rule is_ub_thelub)

text \<open>A chain which contains its maximum is finite\<close>
lemma finite_chainI: "\<lbrakk>chain Y; max_in_chain i Y\<rbrakk> \<Longrightarrow> finite_chain Y"
by (auto simp add: finite_chain_def)

text \<open>'zipping' two chains together also zips their least upper bounds\<close>
lemma lub_prod2: "\<lbrakk>chain (X::nat \<Rightarrow> 'a::cpo); chain (Y::nat \<Rightarrow> 'b::cpo)\<rbrakk> \<Longrightarrow>
                        (\<Squnion>k. (X k,Y k)) = (Lub X, Lub Y)"
by (subst lub_prod, simp+)

text \<open>The least upper bound of a chainelement in a chain
is the least upper bound of the chainelement plus another element\<close>
lemma lub_range_shift2: "chain Y \<Longrightarrow> (\<Squnion>i. Y i) = (\<Squnion>i. Y (i+j))"
  apply(simp add: lub_def)
  using is_lub_range_shift lub_def by fastforce
  

text\<open>The least upper bound of any finite chain is a member of the chain\<close>
lemma l42: "chain S \<Longrightarrow> finite_chain S \<Longrightarrow> \<exists>t. (\<Squnion> j. S j) = S t"
using lub_eqI lub_finch2 by auto

text\<open>The least upper bound of a monotone function applied on a finite chain is the
function applied to the least upper bound of the finite chain\<close>
lemma finite_chain_lub: fixes Y :: "nat \<Rightarrow> 'a ::cpo"
  assumes "finite_chain Y" and "chain Y" and "monofun f"
  shows "f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y i))"
proof -
  obtain nn :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat" where
    f1: "Lub Y = Y (nn Y)"
    by (meson assms(1) assms(2) l42)
  then have "\<forall>n. f (Y n) \<sqsubseteq> f (Y (nn Y))"
    by (metis (no_types) assms(2) assms(3) is_ub_thelub monofun_def)
  then show ?thesis
    using f1 by (simp add: lub_chain_maxelem)
qed 

(* If you like admissibility proofs you will love this one. Never again "contI" ! *)
(* Dieses Lemma wurde nach langer suche von Sebastian entdeckt. Möge er ewig leben *)
lemma adm2cont: 
  fixes f:: "'a::cpo \<Rightarrow> 'b::cpo"
  assumes "monofun f" and "\<And>k. adm (\<lambda>Y. (f Y)\<sqsubseteq>k)" 
  shows "cont f"
  apply(rule contI2)    
   apply(auto simp add: assms)
proof -
  fix Y:: "nat \<Rightarrow> 'a"
  assume "chain Y"
  obtain k where k_def: "k=(\<Squnion>i. (f (Y i)))" by simp 
      (* komischer zwischenschritt, aber anders schafft sledgi das nicht *)
  have "\<And>j. f (Y j) \<sqsubseteq> (\<Squnion>i. (f (Y i)))"
    using \<open>chain Y\<close> assms(1) below_lub ch2ch_monofun by blast  
  hence "\<And>j. f (Y j) \<sqsubseteq> k" by(simp add: k_def)
  hence "f (\<Squnion>j. Y j) \<sqsubseteq> k"
    by (metis (no_types, lifting) \<open>chain Y\<close> adm_def assms(2))
  thus "f (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f (Y i)) "
    using k_def by blast 
qed     

text \<open>Creating a list from iteration a function \<open>f\<close> 
  \<open>n\<close>-times on a start value \<open>s\<close>.\<close>
primrec literate :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  literate_0:  "literate 0 f s = []" |
  literate_Suc:"literate (Suc n) f s = s#(literate n f (f s))"

text \<open>Iterative conversion of @{term literate} result to a set\<close>
lemma literate_Suc2:
  "set (literate (Suc n) f s) = {s} \<union> set (literate n f (f s))"
by auto

text \<open>A set of successive natural numbers can be split into the smallest
  number and the rest\<close>
lemma natl3: "{i. x \<le> i \<and> i < Suc n + x} = {x} \<union> {i. Suc x \<le> i \<and> i < Suc n + x}"
by auto

text \<open>Create set of natural numbers from k to n+k-1 by @{term literate}\<close>
lemma literatel1 [simp]: 
  "set (literate n Suc k) = {i. k \<le> i \<and> i < (n + k)}"
apply (rule_tac x="k" in spec)
apply (induct_tac n, simp)
apply (subst literate_Suc2)
apply (rule allI)
apply (erule_tac x="Suc x" in allE)
by (subst natl3, simp)

text \<open>A list of length @{term n} contains at most @{term n} different elements\<close>
lemma card_set_list_le_length: "card (set x) \<le> length x"
apply (induct_tac x, simp+)
by (simp add: card_insert_if)

text \<open>@{term "literate n"} creates lists with length @{term n}\<close>
lemma [simp]: "length (literate n f k) = n"
apply (rule_tac x="k" in spec)
by (induct_tac n, simp+)

text \<open>Zipping and unzipping on lists\<close>
lemma [simp]: "map snd (map (Pair k) a) = a"
by (induct_tac a, simp+)

text \<open>For a list @{term x}, each element in @{term "set x"} appears at some position in
  @{term x}\<close>
lemma from_set_to_nth: "xa \<in> set x \<Longrightarrow> \<exists>k. x!k = xa \<and> k < length x"
apply (simp add: atomize_imp)
apply (induct_tac x, simp+) 
apply (rule conjI, rule impI)
apply (rule_tac x="0" in exI, simp)
apply (rule impI, simp)
apply (erule exE)
by (rule_tac x="Suc k" in exI, simp)

text \<open>Replacing a filter on lists by a stronger filter\<close>
lemma filterl4: "\<lbrakk>\<And>x. Q x \<Longrightarrow> P x; filter P x = []\<rbrakk> \<Longrightarrow> filter Q x = []"
by (simp add: atomize_imp, induct_tac x, auto)

text \<open>Induction on lists from the right\<close>
lemma list_rinduct_lemma: "\<forall>y. length y = k \<and> (P [] \<and> (\<forall>x xs. P xs \<longrightarrow> P (xs @ [x]))) \<longrightarrow> P y"
apply (induct_tac k, simp)
apply (rule allI)
apply (rule impI)
apply (erule conjE)+
apply (erule_tac x="butlast y" in allE, auto)
apply (erule_tac x="last y" in allE)
apply (erule_tac x="butlast y" in allE, auto)
by (case_tac "y = []", auto)


(* ----------------------------------------------------------------------- *)
section \<open>Some more lemmas about sets\<close>
(* ----------------------------------------------------------------------- *)

text \<open>All subsets of a finite set are finite themselves\<close>
lemma finite_subset1: "finite Y \<Longrightarrow> (\<forall>X. X \<subseteq> Y \<longrightarrow> finite X)"
  by (simp add: finite_subset)

text \<open>Given an infinite and a finite set, the infinite one contains an element
  which is not in the finite one\<close>
lemma ex_new_if_finitel1:
  "\<lbrakk>finite Y; \<not> finite X\<rbrakk> \<Longrightarrow> \<exists>a. a \<in> X \<and> a \<notin> Y"
apply (rule ccontr, auto)
apply (subgoal_tac "X \<subseteq> Y")
by (frule_tac Y="Y" in finite_subset1, auto)

text \<open>Create a finite set with \<open>n\<close> distinct continuously 
  numbered entries from set \<open>A\<close>.\<close>
primrec
  getinj:: "'a set \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a) set"
where
  "getinj A 0 = {(0,SOME x. x \<in> A)}" |
  "getinj A (Suc n) = {(Suc n, SOME x. x \<in> A \<and> x \<notin> (snd ` (getinj A n)))} \<union> getinj A n"

text \<open>The result of @{term "getinj A n"} and its projections on the first or
  second attribute are finite\<close>

lemma finite_getinjs[simp]: "finite (getinj A n)"
by (induct_tac n, simp+)

lemma finite_snd_getinjs[simp]: "finite (snd ` (getinj A n))"
by (induct_tac n, simp+)

lemma finite_fst_getinjs[simp]: "finite (fst ` (getinj A n))"
by (induct_tac n, simp+)

text \<open>@{term "getinj A n"} only contains entries for numbers up to @{term n}\<close>
lemma getinjs_l1: "\<forall>k. n < k \<longrightarrow> (k, x) \<notin> getinj A n"
by (induct_tac n, simp+)

text \<open>...especially, it contains no entry for @{term "n+1"}\<close>
lemma [simp]: "(Suc n,x) \<notin> getinj A n"
by (insert getinjs_l1 [of n x A], auto)

text \<open>Projecting to the second component is an injective function on results
  of @{term getinj}\<close>
lemma card_getinj_lemma[simp]: "\<not> finite A \<Longrightarrow> card (snd ` (getinj A n)) = card (getinj A n)"
apply (induct_tac n, simp+)
apply (rule someI2_ex)
apply (rule ex_new_if_finitel1)
by (rule finite_snd_getinjs, simp+)

lemma inj_on_getinj: "\<not> finite A \<Longrightarrow> inj_on snd (getinj A n)"
by (rule eq_card_imp_inj_on, simp+)

text \<open>@{term "getinj X n"} maps @{term n} to something\<close>
lemma getinj_ex[simp]: "\<exists>a. (n,a) \<in> getinj X n"
by (induct_tac n, simp+)

text \<open>For a fixed set @{term "A"}, @{term "getinj A i"} is a chain\<close>
lemma getinj_chain:
  "\<lbrakk>\<not> finite A; (j, x) \<in> getinj A j; j \<le> k\<rbrakk> \<Longrightarrow> (j, x) \<in> getinj A k"
apply (simp add: atomize_imp)
apply (induct_tac k, auto)
by (case_tac "j = Suc n", auto)

(* ----------------------------------------------------------------------- *)
section \<open>updis\<close>
(* ----------------------------------------------------------------------- *)

text \<open>The @{term "updis"} command lifts an arbitrary type to a
  discrete pointed partial order.\<close>
abbreviation
  updis :: "'a \<Rightarrow> 'a discr u"
    where "updis \<equiv> (\<lambda>a. up\<cdot>(Discr a))" 

definition upApply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a discr u \<rightarrow> 'b discr u" where
"upApply f \<equiv> \<Lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))"

definition upApply2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a discr\<^sub>\<bottom> \<rightarrow> 'b discr\<^sub>\<bottom> \<rightarrow> 'c discr\<^sub>\<bottom>" where 
"upApply2 f \<equiv> \<Lambda> a b. (if a=\<bottom>\<or>b=\<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x)))"


(* updis lemma *)
lemma updis_exists: assumes "x\<noteq>\<bottom>"
  obtains n where "updis n = x"
  by (metis Discr_undiscr Exh_Up assms)
    
    
    
(* upApply *)    
lemma upapply_mono [simp]: "monofun (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
apply (rule monofunI, auto)
by (metis (full_types, hide_lams) discrete_cpo upE up_below)

lemma upapply_lub: assumes "chain Y"
  shows "((\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))) (\<Squnion>i. Y i))
=(\<Squnion>i. (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))) (Y i))"
apply (rule finite_chain_lub)
by (simp_all add: assms chfin2finch)

lemma upapply_cont [simp]: "cont (\<lambda> a. (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b))))"
using chfindom_monofun2cont upapply_mono by blast

lemma upapply_rep_eq [simp]: "upApply f\<cdot>(updis a) = updis (f a)"
by (simp add: upApply_def)

lemma upapply_insert: "upApply f\<cdot>a = (if a=\<bottom> then \<bottom> else updis (f (THE b. a = updis b)))"  
by(simp add: upApply_def)
    
lemma upapply_strict [simp]: "upApply f\<cdot>\<bottom> = \<bottom>"
by(simp add: upApply_def)

lemma upapply_nbot [simp]: "x\<noteq>\<bottom> \<Longrightarrow> upApply f\<cdot>x\<noteq>\<bottom>"
by(simp add: upApply_def)
    
lemma upapply_up [simp]: assumes "x\<noteq>\<bottom>" obtains a where "up\<cdot>a = upApply f\<cdot>x"
by(simp add: upApply_def assms)
  
lemma chain_nbot: assumes "chain Y" and  "(\<Squnion>i. Y i) \<noteq>\<bottom>"
  obtains n::nat where "(\<And>i. ((Y (i+n)) \<noteq>\<bottom>))"
  by (metis assms(1) assms(2) bottomI le_add2 lub_eq_bottom_iff po_class.chain_mono)

lemma upapply2_mono [simp]: 
  "monofun (\<lambda> b. (if a=\<bottom>\<or>b=\<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x))))"
apply (rule monofunI, auto)
by (metis discrete_cpo upE up_below)

lemma upapply2_cont [simp]:
  "cont (\<lambda>b. if a = \<bottom> \<or> b = \<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x)))"
by (simp add: chfindom_monofun2cont)

lemma upapply2_mono2 [simp]: 
  "monofun (\<lambda>a. \<Lambda> b. if a = \<bottom> \<or> b = \<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x)))"
apply (rule monofunI)
apply (subst cfun_belowI, auto)
by (metis discrete_cpo upE up_below)

lemma upapply2_cont2 [simp]:
  "cont (\<lambda>a. \<Lambda> b. if a = \<bottom> \<or> b = \<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x)))"
by (simp add: chfindom_monofun2cont)

lemma upapply2_rep_eq [simp]: "upApply2 f\<cdot>(updis a)\<cdot>(updis b) = updis (f a b)"
by (simp add: upApply2_def)

lemma upapply2_insert: 
  "upApply2 f\<cdot>a\<cdot>b = (if a=\<bottom>\<or>b=\<bottom> then \<bottom> else updis (f (THE x. a = updis x) (THE x. b = updis x)))"
by (simp add: upApply2_def)

lemma upapply2_strict [simp]: "upApply2 f\<cdot>\<bottom> = \<bottom>"
by(simp add: upApply2_def)

lemma upapply2_nbot [simp]: "x\<noteq>\<bottom> \<Longrightarrow> y\<noteq>\<bottom> \<Longrightarrow> upApply2 f\<cdot>x\<cdot>y\<noteq>\<bottom>"
by(simp add: upApply2_def)

lemma upapply2_up [simp]: assumes "x\<noteq>\<bottom>" and "y\<noteq>\<bottom>" obtains a where "up\<cdot>a = upApply2 f\<cdot>x\<cdot>y"
by(simp add: upApply2_def assms)
 
lemma cont2lub_lub_eq: assumes cont: "\<And>i. cont (\<lambda>x. F i x)" 
  shows "chain Y\<longrightarrow>  (\<Squnion>i. F i (\<Squnion>i. Y i)) = (\<Squnion>i ia. F i (Y ia))"
proof -
  { assume "\<exists>a. (\<Squnion>n. F a (Y n)) \<noteq> F a (Lub Y)"
    have ?thesis
      by (simp add: cont cont2contlubE) }
  thus ?thesis
    by force
qed  
  
lemma[simp]: "x \<sqsubseteq> y \<Longrightarrow> (\<Lambda> ya. f\<cdot>x\<cdot>ya) \<sqsubseteq> (\<Lambda> ya. f\<cdot>y\<cdot>ya)"
  by (simp add: cont_pref_eq1I eta_cfun)

lemma[simp]:"\<forall>Y. chain Y \<longrightarrow> (\<Lambda> y. f\<cdot>(\<Squnion>i. Y i)\<cdot>y) \<sqsubseteq> (\<Squnion>i. \<Lambda> y. f\<cdot>(Y i)\<cdot>y)"
  apply(simp add: contlub_cfun_fun contlub_cfun_arg,auto)
  apply(subst contlub_lambda,auto)
  by (simp add: cfun.lub_cfun cont_pref_eq1I)

lemma cont_lam2cont[simp]:"cont (\<lambda>x. \<Lambda> y. f\<cdot>x\<cdot>y)"
  by(rule contI2, rule monofunI, simp+)

section \<open>add lemmas to cont2cont\<close>

lemma cont2cont_lambda [cont2cont]:
  assumes f: "\<And>y. cont (\<lambda>x. f x y)"
  shows "cont f"
  by (simp add: f) (* TODO: hat es einen grund, dass das nicht schon in cont2cont ist? HOLCF11-Doku lesen *)

lemma [cont2cont]:"cont f \<Longrightarrow> f\<in> cfun"
  by (simp add: cfun_def)

lemma discr_cont: "monofun f \<Longrightarrow> cont (\<lambda>x. g ((f x)::'a:: discrete_cpo))"
  apply(rule Cont.contI2)
  apply(rule monofunI, insert monofunE[of f],auto)
  by (metis is_ub_thelub)

lemma discr_cont2: "cont f \<Longrightarrow> cont (\<lambda>x. g ((f x)::'a:: discrete_cpo))" (*Not cont2cont, problem with domain definitions, i.e. lnat*)
  by (simp add: cont2mono discr_cont)

(*monofun f should be enough*)
lemma discr_cont3: "cont h \<Longrightarrow> cont f \<Longrightarrow> cont (\<lambda>x. ((h x)) ((f x)::'a:: discrete_cpo))"
  by (simp add: cont2cont_fun cont_apply)
end
