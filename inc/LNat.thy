section {* The Datatype of Lazy Natural Numbers *} 

theory LNat
imports Prelude
begin

(* ----------------------------------------------------------------------- *)
section {* Type definition and the basics *}
(* ----------------------------------------------------------------------- *)

text {*
  Defined using the 'domain' command. Generates a bottom element (@{text "\<bottom>"}) and an order (@{text "\<sqsubseteq>"}),
  which are used to define zero and @{text "\<le>"}.
*}
domain lnat = lnsuc (lazy lnpred::lnat)

instantiation lnat :: "{ord, zero}"
begin
  definition lnzero_def: "(0::lnat) \<equiv> \<bottom>"
  definition lnless_def: "(m::lnat) < n \<equiv> m \<sqsubseteq> n \<and> m \<noteq> n"
  definition lnle_def:   "(m::lnat) \<le> n \<equiv> m \<sqsubseteq> n"
instance ..
end

text {* define @{term lntake} as an abbreviation for @{term lnat_take},
  which is generated by the @{text domain} command *}
abbreviation
  lntake :: "nat \<Rightarrow> lnat \<rightarrow> lnat"
    where "lntake \<equiv> lnat_take"

text {* eliminate double successors in @{term lntake} arguments *}
lemma lntake_more[simp]:
  "lntake (Suc n)\<cdot>(lnsuc\<cdot>k) = lnsuc\<cdot>(lntake n\<cdot>k)"
by (induct_tac n, auto)

(* ----------------------------------------------------------------------- *)
section {* Definitions *} 
(* ----------------------------------------------------------------------- *)
text {* @{text "\<infinity>"} is the maximum of all @{term lnat}s *}
definition Inf'  ::  "lnat"   ("\<infinity>") where
"Inf' \<equiv> fix\<cdot>lnsuc"

text {* A natural number @{term n} is represented by @{term "Fin n"} *}
definition Fin   ::  "nat \<Rightarrow> lnat" where
"Fin k \<equiv> lntake k\<cdot>\<infinity>" 

text {* Determine the minimum of the given two @{term lnat}s *}
definition lnmin ::  "lnat \<rightarrow> lnat \<rightarrow> lnat" where
"lnmin \<equiv> fix\<cdot>(\<Lambda> h. strictify\<cdot>(\<Lambda> m. strictify\<cdot>(\<Lambda> n. 
                     lnsuc\<cdot>(h\<cdot>(lnpred\<cdot>m)\<cdot>(lnpred\<cdot>n)))))"

abbreviation lnatGreater :: "lnat \<Rightarrow> lnat \<Rightarrow> bool" (infix ">\<^sup>l" 65) where
"n >\<^sup>l m \<equiv>  n \<ge> lnsuc\<cdot>m"

abbreviation lnatLess :: "lnat \<Rightarrow> lnat \<Rightarrow> bool" (infix "<\<^sup>l" 65) where
"n <\<^sup>l m \<equiv>  lnsuc\<cdot>n \<le> m"

instantiation lnat :: plus
begin  
  definition plus_lnat:: "lnat \<Rightarrow> lnat \<Rightarrow> lnat"  where 
    "plus_lnat ln1 ln2 \<equiv> if (ln1 = \<infinity> \<or> ln2=\<infinity>) then \<infinity> else Fin ((inv Fin) ln1 + (inv Fin) ln2)"

  (*definition lnat_plus2:: "lnat \<rightarrow> lnat \<rightarrow> lnat" where
    "lnat_plus2 \<equiv> \<Lambda> ln1 ln2. (if (ln1 = \<infinity> \<or> ln2=\<infinity>) then \<infinity> else Fin ((inv Fin) ln1 + (inv Fin) ln2))"
    
  definition lnat_plus_moreIdiotic :: "lnat \<rightarrow> lnat \<rightarrow> lnat" where
    "lnat_plus_moreIdiotic = fix\<cdot>(\<Lambda> h. (\<Lambda> m. ( \<Lambda> n. 
                           if m = 0 then n else h\<cdot>(lnpred\<cdot>m)\<cdot>(lnsuc\<cdot>n))))"*)   
instance 
  by(intro_classes)
end
      
(* ----------------------------------------------------------------------- *)
section {* Some basic lemmas *}
(* ----------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------- *)
subsection 
  {* Brief characterization of 
     @{text "Fin"}, @{text "\<infinity>"}, @{text "\<le>"} and @{text "<"}
  *}
(* ----------------------------------------------------------------------- *)

text {* x is smaller then lnsuc x. *}
lemma less_lnsuc[simp]: "x \<le> lnsuc\<cdot>x"
apply (subst lnle_def)
by (rule lnat.induct [of _ x], auto)

text {* @{text "\<infinity>"} is a fix point of @{term lnsuc} *}
lemma fold_inf[simp]: "lnsuc\<cdot>\<infinity> = \<infinity>"
by (unfold Inf'_def, subst fix_eq2 [THEN sym], simp+)

text {* x is smaller then \<infinity>. *}
lemma inf_ub[simp]: "x \<le> \<infinity>"
apply (subst lnle_def)
apply (rule lnat.induct [of _ x], auto)
apply (subst fold_inf [THEN sym])
by (rule monofun_cfun_arg)

text {* 0 is the bottom element. *}
lemma Fin_02bot: "Fin 0 = \<bottom>"
by (simp add: Fin_def)

text {* @{text "\<le>"} on lnats is antisymmetric *}
lemma lnat_po_eq_conv:
  "(x \<le> y \<and> y \<le> x) = ((x::lnat) = y)"
apply (auto simp add: lnle_def)
by (rule po_eq_conv [THEN iffD2], simp)

text {* lnsuc of x is not equal 0. *}
lemma lnsuc_neq_0[simp]: "lnsuc\<cdot>x \<noteq> 0"
by (simp add: lnzero_def)

text {* Similar to the lemma above. *}
lemma lnsuc_neq_0_rev[simp]: "0 \<noteq> lnsuc\<cdot>x"
by (simp add: lnzero_def)

text {* 0 is not equal \<infinity>. *}
lemma Inf'_neq_0[simp]: "0 \<noteq> \<infinity>"
apply (subst fold_inf [THEN sym])
by (rule notI, simp del: fold_inf)

text {* Similar to the lemma above. *}
lemma Inf'_neq_0_rev[simp]: "\<infinity> \<noteq> 0"
by (rule notI, drule sym, simp)

text {* Successors are equal, so are the numbers themselves. *}
lemma inject_lnsuc[simp]: "(lnsuc\<cdot>x = lnsuc\<cdot>y) = (x = y)"
by (rule lnat.injects)

text {* Take lemma. *}
lemma [simp]: "lntake (Suc k)\<cdot>\<infinity> = lnsuc\<cdot>(lntake k\<cdot>\<infinity>)"
apply (subst fold_inf [THEN sym])
by (simp only: lntake_more)

text {* A property of lnsuc. *}
lemma Fin_Suc[simp]: "lnsuc\<cdot>(Fin k) = Fin (Suc k)"
by (simp add: Fin_def)

text {* A property of 0. *}
lemma Fin_0[simp]: "(Fin k = 0) = (k = 0)"
apply (induct_tac k, auto simp add: lnzero_def)
by (simp add: Fin_def)+

text {* Injectivity of Fin. *}
lemma inject_Fin[simp]: "(Fin n = Fin k) = (n = k)"
apply (rule spec [of _ k], induct_tac n, auto)
by (case_tac x, auto simp add: Fin_def)+

text {* If a lnat cannot be reached by @{term "lnat_take"}, it behaves like @{text "\<infinity>"} *}
lemma nreach_lnat_lemma: 
  "\<forall>x. (\<forall>j. lnat_take j\<cdot>x \<noteq> x) \<longrightarrow> lnat_take k\<cdot>x = lnat_take k\<cdot>\<infinity>"
apply (induct_tac k, auto)
apply (rule_tac y=x in lnat.exhaust, auto simp add: lnzero_def)
apply (erule_tac x="lnat" in allE, auto)
by (erule_tac x="Suc j" in allE, auto)

text {* If a lnat cannot be reached by @{term "lnat_take"}, it
  is @{text "\<infinity>"}. *}
lemma nreach_lnat:
  "(\<forall>j. lntake j\<cdot>x \<noteq> x) \<Longrightarrow> x = \<infinity>"
apply (rule lnat.take_lemma)
by (rule nreach_lnat_lemma [rule_format],simp)

text {* Every finite lnat can be reached by @{term lntake} *}
lemma nreach_lnat_rev:
  "x \<noteq> \<infinity> \<Longrightarrow> \<exists>n. lntake n\<cdot>x = x"
apply (rule ccontr, auto)
by (drule nreach_lnat, simp)

text {* If a lnat is reachable by @{term lntake}, it is finite *}
lemma exFin_take:
  "\<forall>x. lntake j\<cdot>x = x \<longrightarrow> (\<exists>k. x = Fin k)"
apply (induct_tac j, auto)
apply (rule_tac x="0" in exI,simp add: Fin_def)
apply (rule_tac y=x in lnat.exhaust, auto)
by (rule_tac x="0" in exI, simp add: Fin_def)

text {* If a predicate holds for both finite lnats and for @{text "\<infinity>"},
  it holds for every lnat *}
lemma lncases:
  "\<And>x P. \<lbrakk>x = \<infinity> \<Longrightarrow> P; \<And>k. x = Fin k \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (case_tac "x = \<infinity>", auto)
apply (drule nreach_lnat_rev, auto)
by (drule exFin_take [rule_format],auto)

text {* Only @{text "\<infinity>"} is greater or equal to @{text "\<infinity>"} *}
lemma inf_less_eq[simp]: "(\<infinity> \<le> x) = (x = \<infinity>)"
apply (auto, rule lnat_po_eq_conv [THEN iffD1])
by (rule conjI, auto)

text {* Bottom is 0. *}
lemma bot_is_0: "(\<bottom>::lnat) = 0"
by (simp add: lnzero_def)

text {* Fin k \<le> 0 holds only for k = 0. *}
lemma lnle_Fin_0[simp]: "(Fin k \<le> 0) = (k = 0)"
apply (simp add: lnzero_def lnle_def)
by (subst bot_is_0, simp)

text {* @{text "\<le>"} on lnats is antisymmetric *}
lemma less2eq: "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> (x :: lnat) = y"
by (rule lnat_po_eq_conv [THEN iffD1], simp)

text {* If a number is smaller than @{term i}, its predecessor is
  also smaller than @{term i} *}
lemma Fin_leq_Suc_leq: "Fin (Suc n) \<le> i \<Longrightarrow> Fin n \<le> i"
apply (simp add: lnle_def)
apply (rule below_trans, auto)
apply (simp only: Fin_def)
apply (rule monofun_cfun_fun)
by (rule chainE,simp)

text {* @{text "\<le>"} on lnats and on nats*}
lemma less2nat_lemma: "\<forall>k. (Fin n \<le> Fin k) \<longrightarrow> (n \<le> k)"
apply (induct_tac n, auto)
apply (case_tac "n=k", simp)
apply (subgoal_tac "Fin k \<le> Fin (Suc k)")
apply (drule less2eq, auto)
apply (subst lnle_def)
apply (rule chainE)
apply (simp add: Fin_def)
apply (erule_tac x="k" in allE,auto)
by (drule Fin_leq_Suc_leq, simp)

text {* If Fin n \<le> Fin k then n \<le> k. *}
lemma less2nat[simp]: "(Fin n \<le> Fin k) = (n \<le> k)"
apply (rule iffI)
apply (rule less2nat_lemma [rule_format], assumption)
apply (simp add: lnle_def)
apply (rule chain_mono)
by (simp add: Fin_def,auto)

text {* lnsuc x is \<infinity> iff x is \<infinity>. *}
lemma [simp]: "(lnsuc\<cdot>x = \<infinity>) = (x = \<infinity>)"
apply (rule iffI) 
by (rule lnat.injects [THEN iffD1], simp+)

text {* A finite number is not \<infinity>. *}
lemma Fin_neq_inf[simp]: "Fin k \<noteq> \<infinity>"
apply (induct_tac k, auto)
apply (simp add: Fin_def bot_is_0)
by (simp add: Fin_Suc [THEN sym] del: Fin_Suc)

text {* If lnsuc x \<le> lnsuc y then x \<le> y. *}
lemma lnsuc_lnle_emb[simp]:  "(lnsuc\<cdot>x \<le> lnsuc\<cdot>y) = (x \<le> y)"
apply (rule_tac x=x in lncases, simp)
by (rule_tac x=y in lncases, auto)

text {* 0 is the smallest element. *}
lemma [simp]: "0 \<le> (x::lnat)"
by (simp add: lnzero_def lnle_def)

text {* If n \<le> 0 then n = 0. *}
lemma [simp]: "((n::lnat) \<le> 0) = (n = 0)"
by (rule iffI, rule_tac x=n in lncases, auto)

text {* If x \<sqsubseteq> y then x \<le> y. *}
lemma lnle_conv[simp]: "((x::lnat) \<sqsubseteq> y) = (x \<le> y)"
by (subst lnle_def,simp)

text {* transitivity of @{text "\<le>"} *}
lemma trans_lnle:
  "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> (x::lnat) \<le> z"
by (subst lnle_def, rule_tac y = y in below_trans, simp+)

text {* reflexivity of @{text "\<le>"} *}
lemma refl_lnle[simp]: "(x::lnat) \<le> x"
by (subst lnle_def,rule below_refl)

text {* 0 < \<infinity>. *}
lemma Zero_lnless_infty[simp]: "0 < \<infinity>"
by (auto simp add: lnless_def)

text {* Except for 0, every lnat has a predecessor *}
lemma gr_0[simp]: "(0 < j) = (\<exists>k. j = lnsuc\<cdot>k)"
apply (auto simp add: lnless_def)
apply (rule_tac y=j in lnat.exhaust)
by (simp add: lnzero_def, auto)

(*---*)
section {* Some basic lemmas on @{text "<"} *}
(*---*)

text {* 0 < lnsuc\<cdot>k *}
lemma [simp]: "0 < lnsuc\<cdot>k"
by (auto simp add: lnless_def)

text {* 0 < Fin (Suc k) *}
lemma [simp]: "0 < Fin (Suc k)"
by (simp add: Fin_Suc [THEN sym] del: Fin_Suc)

text {* Fin k < \<infinity> *}
lemma [simp]: "Fin k < \<infinity>"
by (auto simp add: lnless_def)

text {* If Fin k < Fin n then k < n. *} 
lemma [simp]: "(Fin k < Fin n) = (k < n)"
by (auto simp add: lnless_def)

lemma trans_lnless:
  "\<lbrakk>x < y; y < z\<rbrakk> \<Longrightarrow> (x::lnat) < z"
apply (auto simp add: lnless_def)
apply (rule trans_lnle, auto)
by (simp add: lnat_po_eq_conv [THEN iffD1])

text {* If lnsuc\<cdot>n < lnsuc\<cdot>k then n < k *}
lemma [simp]: "(lnsuc\<cdot>n < lnsuc\<cdot>k) = (n < k)"
by (auto simp add: lnless_def)

text {* lnsuc k is not smaller then 0. *}
lemma [simp]: "\<not> lnsuc\<cdot>k < 0"
by (simp add: lnless_def)

text {* \<infinity> is not smaller then anything. *}
lemma [simp]: "\<not> \<infinity> < i"
by (auto simp add: lnless_def)

(*---*)
section {* Relationship between Fin and @{text "\<infinity>"} *}
(*---*)


text {* Every non-infinite number is finite *}
lemma ninf2Fin: "x \<noteq> \<infinity> \<Longrightarrow> \<exists>k. x = Fin k"
by (rule_tac x=x in lncases, auto)

lemma assumes "ln = lnsuc\<cdot>ln"
  shows "ln = \<infinity>"
using assms ninf2Fin by force

text {* Every non-finite number is infinite *}
lemma infI: "\<forall>k. x \<noteq> Fin k \<Longrightarrow> x = \<infinity>"
by (rule lncases [of x], auto)

text {* Every number below @{term "Fin k"} is finite *}
lemma below_fin_imp_ninf: "x \<sqsubseteq> Fin k \<Longrightarrow> x \<noteq> \<infinity>"
by (rule lncases [of "x"], simp_all)

text {* @{text "\<infinity>"} is not finite *}
lemma [simp]: "\<infinity> \<noteq> Fin k"
by (rule notI, drule sym, simp)

text {* @{text "\<infinity>"} is strictly greater than all finite lnats *}
lemma [simp]: "\<not> (\<infinity> \<le> Fin k)"
by (rule notI, auto)

text {* An unbounded number is infinite *}
lemma inf_belowI: "\<forall>k. Fin k \<sqsubseteq> x \<Longrightarrow> x = \<infinity>"
proof (rule lncases [of x], simp)
  fix k assume "x = Fin k" and "\<forall>k. Fin k \<sqsubseteq> x"
  hence "Fin (Suc k) \<sqsubseteq> Fin k" by simp
  thus ?thesis by simp
qed

(* ----------------------------------------------------------------------- *)
subsection {* Induction rules *}
(* ----------------------------------------------------------------------- *)

text {* admissibile predicates on lnats can be proved inductively *}
lemma lnat_ind: "\<And>P x. \<lbrakk>adm P; P 0; \<And>l. P l \<Longrightarrow> P (lnsuc\<cdot>l)\<rbrakk> \<Longrightarrow> P x"
apply (rule lnat.induct, simp)
by (simp add: lnzero_def, auto)

(* ----------------------------------------------------------------------- *)
subsection {*Basic lemmas on @{term lmin}  *}
(* ----------------------------------------------------------------------- *)

text {* lnmin\<cdot>0\<cdot>n = 0 *}
lemma strict_lnmin_fst[simp]: "lnmin\<cdot>0\<cdot>n = 0"
apply (subst lnmin_def [THEN fix_eq2])    
by (simp add: lnzero_def)

text {* lnmin\<cdot>m\<cdot>0 = 0*}
lemma strict_lnmin_snd[simp]: "lnmin\<cdot>m\<cdot>0 = 0"
apply (subst lnmin_def [THEN fix_eq2], auto)
apply (rule lnat.induct [of _ m], simp)
by (simp add: lnzero_def)+

text {* Relationship between lnmin and lnsuc.*}
lemma lnmin_lnsuc[simp]: "lnmin\<cdot>(lnsuc\<cdot>m)\<cdot>(lnsuc\<cdot>n) = lnsuc\<cdot>(lnmin\<cdot>m\<cdot>n)"
by (subst lnmin_def [THEN fix_eq2], simp)

text {* lnmin\<cdot>\<infinity>\<cdot>n = n *}
lemma lnmin_fst_inf[simp]: "lnmin\<cdot>\<infinity>\<cdot>n = n"
apply (rule lnat_ind [of _ n], auto)
apply (subst fold_inf [THEN sym])
by (simp del: fold_inf)

text {* lnmin\<cdot>m\<cdot>\<infinity> = m *}
lemma lnmin_snd_inf[simp]: "lnmin\<cdot>m\<cdot>\<infinity> = m"
apply (rule lnat_ind [of _ m], auto)
apply (subst fold_inf [THEN sym])
by (simp del: fold_inf)

text {*Fin 0 = 0 *}
lemma [simp]: "Fin 0 = 0"
by simp

text {*lnmin\<cdot>(Fin j)\<cdot>(Fin k) = Fin (min j k)" *}
lemma lnmin_fin[simp]: "lnmin\<cdot>(Fin j)\<cdot>(Fin k) = Fin (min j k)"
apply (rule_tac x=k in spec)
apply (induct_tac j, auto)
apply (case_tac x, auto)
by (simp add: Fin_def lnzero_def)

lemma lub_mono2: "\<lbrakk>chain (X::nat\<Rightarrow>lnat); chain (Y::nat\<Rightarrow>lnat); \<And>i. X i \<le> Y i\<rbrakk>
    \<Longrightarrow> (\<Squnion>i. X i) \<le> (\<Squnion>i. Y i)"
using lnle_conv lub_mono by blast

text {* In an infinite chain, one can find for every element a bigger element
  in the chain *}
lemma inf_chainl2:
  "\<lbrakk>chain Y; \<not> finite_chain Y\<rbrakk> \<Longrightarrow> \<exists>j. Y k \<sqsubseteq> Y j \<and> Y k \<noteq> Y j"
apply (auto simp add: finite_chain_def max_in_chain_def)
apply (erule_tac x="k" in allE, auto)
apply (frule_tac i=k and j=j in chain_mono, assumption)
by (rule_tac x="j" in exI, simp)

text {* For constant chains, the first element is the maximum *}
lemma max_in_chainI2: "\<lbrakk>chain Y; \<forall>i. Y i = k\<rbrakk> \<Longrightarrow> max_in_chain 0 Y"
by (rule max_in_chainI, simp)

text {* In an infinite chain, there is no maximum *}
lemma finite_chainl1: "\<lbrakk>chain Y; \<not> finite_chain Y\<rbrakk> \<Longrightarrow> \<not> max_in_chain k Y"
apply (rule notI)
by (simp add: finite_chain_def)

text {* In an inifinite lnat chain, one can find for every lnat a bigger element
  in the chain *}
lemma inf_chainl3:
  "\<lbrakk>chain Y; \<not> finite_chain Y\<rbrakk> \<Longrightarrow> \<exists>j. (Fin k) \<sqsubseteq> Y j \<and> Fin k \<noteq> Y j"
apply (induct_tac k, simp+)
apply (case_tac "\<forall>i. Y i = \<bottom>")
apply (frule_tac k="\<bottom>" in max_in_chainI2, assumption)
apply (drule_tac k="0" in finite_chainl1, assumption, clarify)
apply (simp, erule exE)
apply (rule_tac x="i" in exI)
apply (simp add: lnzero_def)
apply (erule exE, erule conjE)
apply (frule_tac k="j" in finite_chainl1, assumption)
apply (simp add: max_in_chain_def)
apply (erule exE, erule conjE)
apply (rule_tac x="ja" in exI)
apply (rule_tac x="Y j" in lncases, simp+)
apply (drule_tac i="j" and j="ja" in chain_mono, assumption, simp+)
apply (rule_tac x="Y ja" in lncases, simp+)
by (drule_tac i="j" and j="ja" in chain_mono, assumption, simp+)

text {* The least upper bound of an infinite lnat chain is @{text "\<infinity>"} *}
lemma unique_inf_lub: "\<lbrakk>chain Y; \<not> finite_chain Y\<rbrakk> \<Longrightarrow> Lub Y = \<infinity>"
apply (rule ccontr, drule ninf2Fin, erule exE)
apply (frule_tac k="k" in inf_chainl3, assumption)
apply (erule exE, simp)
apply (erule conjE)
apply (drule_tac x="j" in is_ub_thelub, simp)
by (rule_tac x="Y j" in lncases, simp+)

text {* Every finite lnat is compact *}
lemma compact_Fin: "compact (Fin k)"
apply (rule compactI)
apply (rule admI)
apply (case_tac "finite_chain Y")
apply (simp add: finite_chain_def)
apply (erule exE)
apply (drule lub_finch1 [THEN lub_eqI], simp, simp)
apply (frule unique_inf_lub, assumption)
apply (subgoal_tac "range Y <| Fin k")
apply (drule_tac x="Fin k" in is_lub_thelub, simp+)
apply (rule ub_rangeI, simp)
apply (erule_tac x="i" in allE)
by (rule_tac x="Y i" in lncases, simp+)

text {* If the outputs of a continuous function for finite inputs are
  bounded, the output for @{text "\<infinity>"} has the same bound *}
lemma lnat_adml1[simp]: "adm (\<lambda>x. f\<cdot>x \<le> Fin n)"
apply (subst lnle_def)
apply (rule admI)
apply (subst contlub_cfun_arg, assumption)
apply (rule is_lub_thelub, rule chain_monofun, assumption)
by (rule ub_rangeI, simp)

text {* If a continuous function returns @{text "\<infinity>"} for all finite
  inputs, it also returns @{text "\<infinity>"} for input @{text "\<infinity>"} *}
lemma lnat_adnl2[simp]: "adm (\<lambda>x. f\<cdot>x = \<infinity>)"
apply (rule admI)
apply (subst contlub_cfun_arg, assumption)
apply (rule po_eq_conv [THEN iffD2])
apply (rule conjI)
apply (rule is_lub_thelub, rule chain_monofun, assumption)
apply (rule ub_rangeI, simp)
apply (erule_tac x="SOME x. True" in allE)
apply (drule sym, erule ssubst)
by (rule is_ub_thelub, rule chain_monofun)

text {*l \<le> Fin k \<Longrightarrow> l \<noteq> \<infinity>*}
lemma notinfI3: "l \<le> Fin k \<Longrightarrow> l \<noteq> \<infinity>"
by (rule_tac x="l" in lncases, simp+)

text {* Lifting to discrete cpo *}

definition lnsucu ::"lnat u \<rightarrow> lnat u" where
"lnsucu \<equiv> strictify\<cdot>(\<Lambda> n. up\<cdot>(fup\<cdot>lnsuc\<cdot>n))"


definition upinf  ::"lnat u" (* ("\<infinity>\<^isub>u") *) where
"upinf \<equiv> up\<cdot>\<infinity>"

text {* lnsucu\<cdot>\<bottom> = \<bottom> *}
lemma [simp]: "lnsucu\<cdot>\<bottom> = \<bottom>"
by (simp add: lnsucu_def)

text {* lnsucu\<cdot>(up\<cdot>(Fin n)) = up\<cdot>(Fin (Suc n)) *}
lemma [simp]: "lnsucu\<cdot>(up\<cdot>(Fin n)) = up\<cdot>(Fin (Suc n))"
by (simp add: lnsucu_def)

text {* lnsucu\<cdot>(upinf) = upinf *}
lemma [simp]: "lnsucu\<cdot>(upinf) = upinf"
by (simp add: lnsucu_def upinf_def)

text {* We prove the cases lemma for the lifted lnat u *}
lemma lnatu_cases:
  "\<And>n P. \<lbrakk>n = upinf \<Longrightarrow> P; \<And>k. n = up\<cdot>(Fin k) \<Longrightarrow> P; n = \<bottom> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
apply (erule upE, auto simp add: upinf_def)
by (rule_tac x="x" in lncases, auto)

text {* up\<cdot>(Fin k) \<noteq> upinf *}
lemma [simp]: "up\<cdot>(Fin k) \<noteq> upinf"
by (simp add: upinf_def)

text {* up\<cdot>(Fin k) \<noteq> \<bottom> *}
lemma [simp]: "up\<cdot>(Fin k) \<noteq> \<bottom>"
by simp

text {* upinf \<noteq> \<bottom> *}
lemma [simp]: "upinf \<noteq> \<bottom>"
by (simp add: upinf_def)

text {* lnsucu\<cdot>lu \<noteq> up\<cdot>0 *}
lemma [simp]: "lnsucu\<cdot>lu \<noteq> up\<cdot>0"
apply (rule_tac n="lu" in lnatu_cases)
apply (auto simp add: upinf_def)
by (simp add: lnsucu_def)

text {*(lnsucu\<cdot>l = up\<cdot>(Fin (Suc n))) = (l = up\<cdot>(Fin n))*}
lemma [simp]: "(lnsucu\<cdot>l = up\<cdot>(Fin (Suc n))) = (l = up\<cdot>(Fin n))"
apply (rule_tac n="l" in lnatu_cases)
apply (simp add: upinf_def)
by (auto simp add: lnsucu_def)

text {*(lnsuc\<cdot>n = Fin (Suc k)) = (n = Fin k)*}
lemma [simp]: "(lnsuc\<cdot>n = Fin (Suc k)) = (n = Fin k)"
by (simp add: Fin_Suc [THEN sym] del: Fin_Suc)

text {*(lnsuc\<cdot>n \<le> Fin (Suc k)) = (n \<le> Fin k)*}
lemma [simp]: "(lnsuc\<cdot>n \<le> Fin (Suc k)) = (n \<le> Fin k)"
by (simp add: Fin_Suc [THEN sym] del: Fin_Suc)

text {*(lnsuc\<cdot>n < Fin (Suc k)) = (n < Fin k)*}
lemma [simp]: "(lnsuc\<cdot>n < Fin (Suc k)) = (n < Fin k)"
by (simp add: Fin_Suc [THEN sym] del: Fin_Suc)

text {*(Fin (Suc n) \<le> lnsuc\<cdot>l) = (Fin n \<le> l)*}
lemma [simp]: "(Fin (Suc n) \<le> lnsuc\<cdot>l) = (Fin n \<le> l)"
by (simp add: Fin_Suc [THEN sym] del: Fin_Suc)

text {*(Fin (Suc n) < lnsuc\<cdot>l) = (Fin n < l)*}
lemma [simp]: "(Fin (Suc n) < lnsuc\<cdot>l) = (Fin n < l)"
by (simp add: Fin_Suc [THEN sym] del: Fin_Suc)

text {*\<not> Fin (Suc n) < 0*}
lemma [simp]: "\<not> Fin (Suc n) < 0"
by (simp add: Fin_Suc [THEN sym] del: Fin_Suc)

text {*\<not> Fin (Suc n) \<le> 0*}
lemma [simp]: "\<not> Fin (Suc n) \<le> 0"
by (simp add: Fin_Suc [THEN sym] del: Fin_Suc)

text {*\<exists>x. Fin x < 0 \<Longrightarrow> False*}
lemma [simp]: "\<exists>x. Fin x < 0 \<Longrightarrow> False"
by (simp add: lnless_def)

text {*l \<noteq> 0 \<Longrightarrow> Fin (Suc 0) \<le> l*}
lemma neq02Suclnle: "l \<noteq> 0 \<Longrightarrow> Fin (Suc 0) \<le> l"
by (rule_tac x="l" in lncases, simp+)

text {*(Fin k) < y \<Longrightarrow> Fin (Suc k) \<le> y*}
lemma less2lnleD: "(Fin k) < y \<Longrightarrow> Fin (Suc k) \<le> y"
by (rule_tac x="y" in lncases, simp+)

(* ----------------------------------------------------------------------- *)
subsection {*Basic lemmas on @{term lmin}  *}
(* ----------------------------------------------------------------------- *)

text{* Instanciate lnat as a linorder to use min/max*}
instantiation lnat :: linorder
begin
  instance
  apply(intro_classes)
  using lnat_po_eq_conv lnle_def lnless_def apply blast
  apply simp
  using trans_lnle apply blast
  using lnat_po_eq_conv apply blast
  by (metis inf_ub less2nat linear ninf2Fin)
end

text{*A lazy natural number is smaller than its successor *}
lemma ln_less[simp]: assumes "ln<\<infinity>"
  shows "ln < lnsuc\<cdot>ln"
proof -
  have "ln \<le> lnsuc\<cdot>ln" by simp
  obtain n where "Fin n = ln" by (metis assms dual_order.strict_implies_not_eq infI)
  have "Fin n < Fin (Suc n)" by force
  thus ?thesis using \<open>Fin n = ln\<close> by auto 
qed

lemma lnle2le: "m < lnsuc\<cdot>n \<Longrightarrow> m \<le> n"
  apply (case_tac "m=\<infinity>", auto)
  by (metis Fin_Suc less2lnleD lncases lnsuc_lnle_emb)

lemma le2lnle: "m < \<infinity> \<Longrightarrow> lnsuc\<cdot>m \<le> n \<Longrightarrow> m < n"
  by (metis dual_order.strict_iff_order dual_order.trans leD ln_less)

(*few lemmas to simp min*)
text{*\<infinity> is greater than or equal to any lazy natural number*}
lemma [simp]: fixes ln :: lnat
  shows "min \<infinity> ln = ln"
by (simp add: min_def)

lemma [simp]: fixes ln :: lnat
  shows "min ln \<infinity> = ln"
by (simp add: min_def)

text{*0 is less than or equal to any lazy natural number*} 
lemma [simp]: fixes ln :: lnat
  shows "min ln 0 = 0"
by (simp add: min_def)

lemma [simp]: fixes ln :: lnat
  shows "min 0 ln = 0"
by (simp add: min_def)

lemma min_rek: assumes  "z = min x (lnsuc\<cdot>z)"
  shows "z = x"
  apply(rule ccontr, cases "x < z")
   apply (metis assms dual_order.irrefl min_less_iff_conj)
  by (metis assms inf_ub ln_less lnle_def lnless_def min_def)
    
lemma lnat_well_h1:
  "[| n < Fin m; \<And>k. n = Fin k ==> k < m ==> P |] ==> P"
by (metis less2nat less_le lncases notinfI3)

lemma lnat_well_h2:
  "[| n < \<infinity>; \<And>k. n = Fin k ==> P |] ==> P"
using lncases by auto 

lemma lnat_well:
  assumes prem: "\<And>n. \<forall>m::lnat. m < n --> P m ==> P n" shows "P n"
proof -
  have P_lnat: "\<And>k. P (Fin k)"
    apply (rule nat_less_induct)
    apply (rule prem, clarify)
    apply (erule lnat_well_h1, simp)
    done
  show ?thesis
  proof (induct n)
    next show "adm P" by (metis P_lnat adm_upward inf_ub lnat_well_h2 less_le_trans prem)
    next show "P \<bottom>" by (metis Fin_02bot P_lnat)
    then show "\<And>n. P n \<Longrightarrow> P (lnsuc\<cdot>n)" by (metis Fin_Suc P_lnat lncases)
  qed
qed

instance lnat :: wellorder
proof
  fix P and n
  assume hyp: "(\<And>n::lnat. (\<And>m::lnat. m < n ==> P m) ==> P n)"
  show "P n" by (blast intro: lnat_well hyp)
qed


(* ----------------------------------------------------------------------- *)
subsection {*Basic lemmas on @{term lnat_plus}  *}
(* ----------------------------------------------------------------------- *) 

text {* Plus on nats behaves the same as on lnats. *}  
lemma lnat_plus_fin [simp]: "(Fin n) + (Fin m) = Fin (n + m)"
  apply(simp add: plus_lnat_def)
  by (metis UNIV_I f_inv_into_f image_eqI inject_Fin)

text {* 0 + 0 = 0. *}    
lemma plus_lnat0_0:"Fin 0 + Fin 0 = Fin 0"
  apply(simp add: plus_lnat_def)
  apply(simp add: Fin_def inv_def)
  apply(rule_tac someI_ex)
  using Fin_def lnle_Fin_0 by auto

text {* 0 is a right neutral element of + on lnats. *}    
lemma plus_lnat0_r[simp]:"(0::lnat) + n = n"
  apply(simp add: plus_lnat_def)
  by (metis Fin_0 Inf'_neq_0_rev add_cancel_right_left plus_lnat_def lnat_plus_fin ninf2Fin)

text {* 0 is a left neutral element of + on lnats. *}       
lemma plus_lnat0_l:"m + (0::lnat) = m"
  apply(simp add: plus_lnat_def)
  by (metis (mono_tags, lifting) Fin_0 UNIV_I add.right_neutral f_inv_into_f image_eqI plus_lnat_def plus_lnat0_r)

text {* m + \<infinity> = \<infinity>. *}       
lemma plus_lnatInf_l[simp]:"m + \<infinity> = \<infinity>"
  by(simp add: plus_lnat_def)  

text {* \<infinity> + n = \<infinity>. *}    
lemma plus_lnatInf_r:"\<infinity> + n = \<infinity>"
  by(simp add: plus_lnat_def)  

text {* + on lnats is commutative. *}    
lemma lnat_plus_commu:"(ln1::lnat) + ln2 = ln2 + ln1"
  by(simp add: plus_lnat_def)

text {* + is associative. *}    
instance lnat:: semigroup_add
  apply(intro_classes)
  apply(simp add: plus_lnat_def)
  by (smt add.left_commute f_inv_into_f inject_Fin natl2 rangeI)

text{* + is commutative. *}
instance lnat:: ab_semigroup_add
  apply(intro_classes)
  by (simp add: lnat_plus_commu)

text{* + is zero neutral.  *}    
instance lnat:: monoid_add
  apply(intro_classes)
  apply (simp)
  by (simp add: plus_lnat0_l)

text{* Define a 1 element in lnat. *}    
instantiation lnat :: one
begin
definition one_lnat:: "lnat" where 
  "one_lnat = Fin 1"
  
  instance ..
end 

text{* This 1 element is the successor of 0. *}  
lemma one_def: "1 = lnsuc\<cdot>0"
   by (metis Fin_02bot Fin_Suc One_nat_def lnzero_def one_lnat_def)

lemma lnat_1_inf [simp]: "1 < \<infinity>"
  unfolding one_lnat_def
  by simp

text{* Adding 1 to an lnat ln1 yields the same result as the successor of ln1. *}     
lemma lnat_plus_suc: "ln1 + 1 = lnsuc\<cdot>ln1"
  apply(simp add: plus_lnat_def)
  by (metis Fin_Suc Inf'_neq_0_rev One_nat_def Suc_def2 f_inv_into_f fold_inf inf_ub inject_Fin inject_lnsuc less_le lnat_well_h2 one_def one_lnat_def rangeI)

text{* Applying lnsuc to the first or second element of the addition yields the same result.  *}    
lemma lnat_plus_lnsuc: "ln1 + (lnsuc\<cdot>ln2) = (lnsuc\<cdot>ln1) + ln2"
  apply(simp add: plus_lnat_def)
  proof -
    have f1: "\<And>f n. f (inv f (f (n::nat)::lnat)) = f n"
      by (simp add: f_inv_into_f)
    have "\<And>l. Fin (inv Fin l) = l \<or> \<infinity> = l"
      by (metis (no_types) f_inv_into_f ninf2Fin rangeI)
    then have f2: "\<And>l. inv Fin (lnsuc\<cdot>l) = Suc (inv Fin l) \<or> \<infinity> = l"
      using f1 by (metis (no_types) Fin_Suc inject_Fin)
    then have "\<And>n l. n + inv Fin (lnsuc\<cdot>l) = inv Fin l + Suc n \<or> \<infinity> = l"
      by simp
    then show "ln1 \<noteq> \<infinity> \<and> ln2 \<noteq> \<infinity> \<longrightarrow> inv Fin ln1 + inv Fin (lnsuc\<cdot>ln2) = inv Fin (lnsuc\<cdot>ln1) + inv Fin ln2"
      using f2 by (metis (no_types) natl2)
  qed
  

lemma min_adm[simp]: fixes y::lnat
  shows "adm (\<lambda>x. min y (g\<cdot>x) \<sqsubseteq> h\<cdot>x)"
proof (rule admI)
  fix Y
  assume Y_ch: "chain Y"  and as: "\<forall>i. min y (g\<cdot>(Y i)) \<sqsubseteq> h\<cdot>(Y i)"
  have h1:"finite_chain Y \<Longrightarrow> min y (g\<cdot>(\<Squnion>i. Y i)) \<sqsubseteq> h\<cdot>(\<Squnion>i. Y i)"
    using Y_ch as l42 by force
  have "\<not>finite_chain Y \<Longrightarrow> min y (g\<cdot>(\<Squnion>i. Y i)) \<sqsubseteq> h\<cdot>(\<Squnion>i. Y i)"
  proof (cases "g\<cdot>(\<Squnion>i. Y i) \<sqsubseteq> y")
    case True
    hence "\<And>i. g\<cdot>(Y i) \<sqsubseteq> y"
      using Y_ch is_ub_thelub monofun_cfun_arg rev_below_trans by blast
    then show ?thesis
      by (metis (no_types, lifting) Y_ch as ch2ch_Rep_cfunR contlub_cfun_arg lnle_conv lub_below_iff lub_mono min_absorb2)
  next
    case False
    then show ?thesis
      by (metis Y_ch as below_lub ch2ch_Rep_cfunR contlub_cfun_arg lnle_conv lub_below min.commute min_def)
  qed
  thus "min y (g\<cdot>(\<Squnion>i. Y i)) \<sqsubseteq> h\<cdot>(\<Squnion>i. Y i)"
    using h1 by blast 
qed

lemma min_adm2[simp]: fixes y::lnat
  shows "adm (\<lambda>x. min (g\<cdot>x) y \<sqsubseteq> h\<cdot>x)"
  apply(subst min.commute)
  using min_adm by blast
    
lemma lub_sml_eq:"\<lbrakk>chain (Y::nat\<Rightarrow>lnat); \<And>i. x \<le> Y i\<rbrakk> \<Longrightarrow> x \<le> (\<Squnion>i. Y i)"
  using l42 unique_inf_lub by force

text{* The lub of a chain in minimum is the minimum of the lub. *}
lemma min_lub:" chain Y \<Longrightarrow> (\<Squnion>i::nat. min (x::lnat) (Y i)) = min (x) (\<Squnion>i::nat. (Y i))"
  apply (case_tac "x=\<infinity>", simp_all)
  apply (case_tac "finite_chain Y")
proof -
  assume a1: "chain Y"
  assume a2: "finite_chain Y"
  then have "monofun (min x)"
    by (metis (mono_tags, lifting) lnle_conv min.idem min.semilattice_order_axioms monofunI
        semilattice_order.mono semilattice_order.orderI)
  then show ?thesis
    using a2 a1 by (metis (no_types) finite_chain_lub)
next
  assume a0:"chain Y"
  assume a1:"\<not> finite_chain Y"
  assume a2:"x \<noteq> \<infinity>"
  have h0:"\<forall>i. \<exists>j\<ge>i. Y i \<sqsubseteq> Y j"
  by blast  
  then have"(\<Squnion>i. min x (Y i)) = x"
  proof -
    have f1: "\<And>n. min x (Y n) \<sqsubseteq> x"
      by (metis (lifting) lnle_def min.bounded_iff order_refl)
    then have f2: "\<And>n. min x (Y n) = x \<or> Y n \<sqsubseteq> x"
      by (metis (lifting) min_def)
    have f3: "\<infinity> \<notsqsubseteq> x"
      by (metis (lifting) a2 inf_less_eq lnle_def) 
    have "Lub Y = \<infinity>"
      by (meson a0 a1 unique_inf_lub)
    then obtain nn :: "(nat \<Rightarrow> lnat) \<Rightarrow> lnat \<Rightarrow> nat" where
      f4: "min x (Y (nn Y x)) = x \<or> \<infinity> \<sqsubseteq> x"
      using f2 by (metis (no_types) a0 lub_below_iff)
    have "\<forall>f n. \<exists>na. (f (na::nat)::lnat) \<notsqsubseteq> f n \<or> Lub f = f n"
      by (metis lub_chain_maxelem)
    then show ?thesis
      using f4 f3 f1 by (metis (full_types))
    qed
  then show ?thesis
    by (simp add: a0 a1 unique_inf_lub)
qed

text{* Reversed Version of min_lub: The minimum of the lub is the lub of a chain in a minimum. *}  
lemma min_lub_rev:"chain Y \<Longrightarrow>  min (x) (\<Squnion>i::nat. (Y i)) = (\<Squnion>i::nat. min (x::lnat) (Y i)) "
  using min_lub by auto

text{* \<le> relation between two chains in a minimum is as well preserved by their lubs. *}
lemma lub_min_mono: "\<lbrakk>chain (X::nat\<Rightarrow>lnat); chain (Y::nat\<Rightarrow>lnat); \<And>i. min x (X i) \<le> Y i\<rbrakk>
    \<Longrightarrow> min x (\<Squnion>i. X i) \<le> (\<Squnion>i. Y i)"
  by (metis dual_order.trans is_ub_thelub lnle_def lub_mono2 min_le_iff_disj)

text{* Twisted version of lub_min_mono: \<le> rel. between two chains in minimum is preserved by lubs. *}
lemma lub_min_mono2: "\<lbrakk>chain (X::nat\<Rightarrow>lnat); chain (Y::nat\<Rightarrow>lnat); \<And>i. min (X i) y \<le> Y i\<rbrakk>
    \<Longrightarrow> min (\<Squnion>i. X i) y \<le> (\<Squnion>i. Y i)"
  by (metis dual_order.trans is_ub_thelub lnle_def lub_mono2 min_le_iff_disj)


lemma lessequal_addition: assumes "a \<le> b" and "c \<le> d" shows "a + c \<le> b + (d :: lnat)"
proof -
  have "b = \<infinity> \<Longrightarrow> a + c \<le> b + d"
    by (simp add: plus_lnatInf_r)
  moreover
  have "d = \<infinity> \<Longrightarrow> a + c \<le> b + d"
    by (simp add: plus_lnatInf_r)
  moreover
  have "a = \<infinity> \<Longrightarrow> a + c \<le> b + d"
    using assms(1) plus_lnatInf_r by auto
  moreover
  have "c = \<infinity> \<Longrightarrow> a + c \<le> b + d"
    using assms(2) plus_lnatInf_r by auto
  moreover
  have "a \<noteq> \<infinity> \<Longrightarrow> b \<noteq> \<infinity> \<Longrightarrow> c \<noteq> \<infinity> \<Longrightarrow> d \<noteq> \<infinity> \<Longrightarrow> a + c \<le> b + d"
  proof -
    assume "a \<noteq> \<infinity>"
    then obtain m where m_def: "Fin m = a"
      using infI by force
    assume "b \<noteq> \<infinity>"
    then obtain n where n_def: "Fin n = b"
      using infI by force
    assume "c \<noteq> \<infinity>"
    then obtain x where x_def: "Fin x = c"
      using infI by force
    assume "d \<noteq> \<infinity>"
    then obtain y where y_def: "Fin y = d"
      using infI by force
    show ?thesis
      using assms m_def n_def x_def y_def by auto
    qed
  then show "a + c \<le> b + d"
    using calculation by blast
qed

lemma lnmin_eqasmthmin: assumes "a = b" and "a \<le> c" shows "a = lnmin\<cdot>b\<cdot>c"
proof -
  have "a = \<infinity> \<Longrightarrow> a = lnmin\<cdot>b\<cdot>c"
    using assms by auto
  moreover
  have "b = \<infinity> \<Longrightarrow> a = lnmin\<cdot>b\<cdot>c"
    using assms by auto
  moreover
  have "c = \<infinity> \<Longrightarrow> a = lnmin\<cdot>b\<cdot>c"
    using assms by auto
  moreover
  have "a \<noteq> \<infinity> \<Longrightarrow> b \<noteq> \<infinity> \<Longrightarrow> c \<noteq> \<infinity> \<Longrightarrow>  a = lnmin\<cdot>b\<cdot>c"
    by (metis assms less2nat lncases lnmin_fin min.order_iff)

  then show ?thesis
    using calculation by blast
qed

lemma lnmin_asso: "lnmin\<cdot>x\<cdot>y = lnmin\<cdot>y\<cdot>x"
proof -
  have "x = \<infinity> \<Longrightarrow> lnmin\<cdot>x\<cdot>y = lnmin\<cdot>y\<cdot>x"
    by simp
  moreover
  have "y = \<infinity> \<Longrightarrow> lnmin\<cdot>x\<cdot>y = lnmin\<cdot>y\<cdot>x"
    by simp
  moreover
  have "x \<noteq> \<infinity> \<Longrightarrow> y \<noteq> \<infinity> \<Longrightarrow> lnmin\<cdot>x\<cdot>y = lnmin\<cdot>y\<cdot>x"
    by (metis (full_types) lncases lnmin_fin min.commute)
  then show ?thesis
    using calculation by blast
qed

lemma lnmin_smaller_addition: "lnmin\<cdot>x\<cdot>y \<le> x + y"
proof -
  have "x = \<infinity> \<Longrightarrow> lnmin\<cdot>x\<cdot>y \<le> x + y"
    by (simp add: plus_lnatInf_r)
  moreover
  have "y = \<infinity> \<Longrightarrow> lnmin\<cdot>x\<cdot>y \<le> x + y"
    by simp
  moreover
  have "x \<noteq> \<infinity> \<Longrightarrow> y \<noteq> \<infinity> \<Longrightarrow> lnmin\<cdot>x\<cdot>y \<le> x + y"
    by (metis bot_is_0 lessequal_addition linear lnle_def lnmin_asso lnmin_eqasmthmin minimal plus_lnat0_l)
  then show ?thesis
    using calculation by blast
qed


end