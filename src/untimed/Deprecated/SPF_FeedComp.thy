(*  Title:  SPF_FeedComp.thy
    Author: Jens Christoph Bürger
    e-mail: jens.buerger@rwth-aachen.de

    Description: Extension for SPFComp, handles lifting of feedback composition
                 MAIN LEMMA: gen_fix_iter_spfComp_eq
*)

theory SPF_FeedComp
  imports SPF_Comp  SPF_Templates
begin

  
  
(* ----------------------------------------------------------------------- *)
section \<open>general-lemmas\<close>
(* ----------------------------------------------------------------------- *)

(* Insert rule for SBs with a single channel *)
lemma sb_onech_getch_insert :"([ch1 \<mapsto> s]\<Omega>) . ch1 = (s:: nat stream)"
  by(simp add: sbgetch_rep_eq)

(* Insert rule for iterating spfCompH i+1 times *)
lemma iter_spfCompOldh3_suc_insert: "iter_spfCompH f1 f2 (Suc i) sb
                        = ((f1 \<rightleftharpoons>((sb \<uplus> (iter_spfCompH f1 f2 i sb))  \<bar> spfDom\<cdot>f1))
                            \<uplus> (f2 \<rightleftharpoons>((sb \<uplus> (iter_spfCompH f1 f2 (i) sb))  \<bar> spfDom\<cdot>f2)))"
  apply (unfold iterate_Suc, subst spfCompH_def)
  apply (subst Abs_cfun_inverse2)
   apply (simp only: spfCompH_cont)
   by simp

(* lemma test [simp]: "sb_well [ch \<mapsto> sb . ch]"
  sorry
*)

(* Repackaging by restricting an SB to one channel c that is in the domain *)
lemma nat_sb_repackage: assumes "ch \<in> sbDom\<cdot>sb"
  shows "(sb::nat SB) \<bar> {ch} = [ch \<mapsto> sb . ch]\<Omega>"
  apply (rule sb_eq)
  
  apply (simp_all add: assms sbdom_rep_eq)
  apply (subst sbgetch_rep_eq)
  by simp_all
    


(* used for substitution *)
lemma two_times_one_insert: "2 * (Suc 0) = Suc(Suc(0))"
  by simp

lemma two_times_suci_insert: "2 * (Suc i) = (2 + (2*i))"
  by simp


lemma two_suc_suc_eq_insert: "2 = Suc(Suc(0))"
  by simp


(* ----------------------------------------------------------------------- *)
section \<open>definitions\<close>
(* ----------------------------------------------------------------------- *)

(* Fixpoint for f1 f2 (generalization of sum4) *)
abbreviation gen_fix :: "(nat stream \<rightarrow> nat stream \<rightarrow> nat stream)
                        \<Rightarrow> (nat stream \<rightarrow> nat stream)
                        \<Rightarrow> (nat stream \<rightarrow> nat stream)" where
"gen_fix f1 f2 \<equiv> (\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>x\<cdot>(f2\<cdot>z ))\<cdot>\<bottom>)"

(* Feedback iteration: f2 feeds into f1, f1 also takes x *)
abbreviation spf_feed_sb_inout2_iter :: "(nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)
                                         \<Rightarrow> (nat stream \<rightarrow> nat stream)
                                         \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> channel
                                         \<Rightarrow> nat SB \<Rightarrow> nat
                                         \<Rightarrow> nat SB" where
"spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i \<equiv>
iterate (i)\<cdot>(\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>)"

(* Feedback iteration: Similar to above, except f2 does not directly feed f1, but through feedback *)
abbreviation spf_feed_sb_inout3_iter :: "(nat stream \<rightarrow> nat stream  \<rightarrow> nat stream)
                                          \<Rightarrow> (nat stream \<rightarrow> nat stream)
                                          \<Rightarrow> channel \<Rightarrow> channel \<Rightarrow> channel
                                          \<Rightarrow> nat SB \<Rightarrow> nat
                                          \<Rightarrow> nat SB" where
"spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i \<equiv>
iterate (i)\<cdot>(\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(z . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>)"


(* ----------------------------------------------------------------------- *)
section \<open>more general feedback\<close>
(* ----------------------------------------------------------------------- *)

(* The fixpoint is cont *)
lemma gen_fix_cont[simp]: fixes f1 :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream"
                          fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont  (\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>x\<cdot>(f2\<cdot>z ))\<cdot>\<bottom>)"
  by simp

subsection \<open>step2\<close>

(* Rule for gen_fix with an SB containing only the channel ch1 *)
lemma spf_feed_sb_in_eq: fixes f1 :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream"
                         fixes f2 :: "nat stream \<rightarrow> nat stream"
                         assumes "sb = ([ch1 \<mapsto> s]\<Omega>)"
 shows "(gen_fix f1 f2)\<cdot>s = (\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>z))\<cdot>(\<bottom>))\<cdot>sb"
 by (simp add: assms sbgetch_rep_eq)


subsection \<open>step3\<close>

(* The first inner statement in spf_feed_sb_inout2_iter is monotonic *)
lemma spf_feed_sb_inout1_inner_mono [simp]: fixes f1 :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream"
                                            fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "monofun (\<lambda> z. [ch1 \<mapsto> f1\<cdot>x\<cdot>(f2\<cdot>(z . ch2))]\<Omega> )"
  apply(rule monofunI)
   apply (rule sb_below)
    apply (simp add: sbdom_insert)
    apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
   by (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)

(* ... and retains chain properties, i.e. transforms a chain of SBs into a new one *)
lemma spf_feed_sb_inout1_inner_chain1 [simp]: fixes f1 :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream"
                                              fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "chain Y  \<Longrightarrow> chain (\<lambda> i. [ch3\<mapsto>  f1\<cdot>(x)\<cdot>(f2\<cdot>((Y i) . ch2))]\<Omega>)"
    apply (rule chainI)
  apply (rule sb_below)
   apply (simp add: sbdom_rep_eq)
   apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)



(* LUB and inner statement are commutative *)
lemma spf_feed_sb_inout1_inner_lub: fixes f1 :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream"
                                    fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "chain Y \<Longrightarrow> (\<Squnion>i. f\<cdot>x\<cdot>(f2\<cdot>(Y i . ch2))) = f\<cdot>x\<cdot>(f2\<cdot>((Lub Y). ch2))"
proof -
  assume a1: "chain Y"
  then have "\<And>c. (\<Squnion>n. Y n . c) = Lub Y . c"
    using sbgetch_lub by fastforce
  then show ?thesis
    using a1 by (metis ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg)
qed

(* The domain of the LUB of the new chain of SBs is the channel ch1 *)
lemma spf_feed_sb_inout1_inner_lub_dom: fixes f :: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream"
                                        fixes f2 :: "nat stream \<rightarrow> nat stream"
shows "chain Y \<Longrightarrow> {ch1} = sbDom\<cdot>(\<Squnion>i. [ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>(Y i . ch2))]\<Omega>)"
proof -
  assume a1: "chain Y"
  hence f1: "chain (\<lambda> i. [ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>((Y i) . ch2))]\<Omega>)"
    by simp
  hence f2: "\<forall> i.  sbDom\<cdot>([ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>((Y i) . ch2))]\<Omega>) = {ch1}"
    by (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
  hence f3: "\<forall> i. ([ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>((Y i) . ch2))]\<Omega>)  \<sqsubseteq> (\<Squnion>i. [ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>(Y i . ch2))]\<Omega>)"
    using f1 is_ub_thelub by blast
  thus ?thesis
    using f1 f2 sbChain_dom_eq2 by blast
qed


(* The first inner statement of spf_feed_sb_inout2_iter is cont *)
lemma spf_feed_sb_inout1_inner_cont [simp]: fixes f :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                            fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont (\<lambda> z. [ch1 \<mapsto> f\<cdot>x\<cdot>(f2\<cdot>(z . ch2))]\<Omega> )"
  apply (rule mycontI2, simp only: spf_feed_sb_inout1_inner_mono)
  apply(rule sb_below) (* must work *)
    apply (simp_all add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
   apply (simp add: spf_feed_sb_inout1_inner_lub_dom)
  proof -
    fix Y :: "nat \<Rightarrow> nat SB" and c :: channel
    assume a1: "chain Y"
    then have "\<And>c. (\<Squnion>n. (c\<cdot>(Y n)::channel \<rightarrow> nat stream)) = c\<cdot>(Lub Y)"
      by (simp add: contlub_cfun_arg)
    then show "f\<cdot>x\<cdot>(f2\<cdot>(\<Squnion>n. Y n . ch2)) \<sqsubseteq> (\<Squnion>n. f\<cdot>x\<cdot>(f2\<cdot>(Y n . ch2)))"
      using a1 by (metis ch2ch_Rep_cfunR contlub_cfun_fun po_eq_conv spf_feed_sb_inout1_inner_lub)
  qed

(* Working with nat streams directly equals working with SBs and then getting the channel  *)
lemma spf_feed_sb_inout1_iter_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                  fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "(iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>(x)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>)) .ch3
        = iterate i\<cdot>(\<Lambda> z. f1\<cdot>(x)\<cdot>(f2\<cdot>(z)))\<cdot>(\<bottom>)"
proof (induction i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case
    apply (unfold iterate_Suc)    
    by (simp add: Suc.IH sbgetch_rep_eq)
qed

(* LUB and sbGetCh are commutative *)
lemma spf_feed_sb_inout1_lub_getch:  fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                     fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "(\<Squnion>i. iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>s\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>)) . ch3
       = (\<Squnion>i. (iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>s\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>)) .ch3)"
  apply (rule sbgetch_lub)
  apply(rule sbIterate_chain)
  by (simp add: sbdom_rep_eq)

(* Result step 3: gen_fix for an SB with sole channel ch1 corresponds to inout1 *)
lemma spf_feed_sb_inout1_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                             fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "sb = ([ch1 \<mapsto> s]\<Omega>)"
  shows "(gen_fix f1 f2)\<cdot>s =
            ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>)) sb) .ch3"
  by (simp add: spf_feed_sb_in_eq assms spf_feed_sb_inout1_lub_getch spf_feed_sb_inout1_iter_eq sbgetch_rep_eq)


subsection \<open>step4\<close>

(* The second inner statement in spf_feed_sb_inout2_iter is cont *)
lemma contfun_contHelp[simp]: fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont (\<lambda> z. (f2\<cdot>(z . ch3)))"
  by simp

(* The second inner statement in spf_feed_sb_inout2_iter is monotonic *)
lemma contfun_monofun[simp]: fixes f2 :: "nat stream \<rightarrow> nat stream"
shows "monofun (\<lambda> z. ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>))"
    apply(rule monofunI)
    apply (rule sb_below)
     apply (simp add: sbdom_insert)
      apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (meson monofun_cfun monofun_cfun_arg monofun_cfun_fun)

(* The second inner statementin spf_feed_sb_inout2_iter preserves chain properties *)
lemma contfun_chain[simp]: fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "chain Y \<Longrightarrow> chain (\<lambda> i. ([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))"
    apply (rule chainI)
    apply (rule sb_below)
     apply (simp add: sbdom_rep_eq)
      apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
  by (simp add: monofun_cfun po_class.chainE)

(* LUB and the second inner statement are commutative *)
lemma contfun_innerLub: fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "chain Y \<Longrightarrow> (\<Squnion> i. (f2\<cdot>((Y i) . ch3))) = f2\<cdot>((Lub Y) . ch3)"
proof -
  assume a1: "chain Y"
  then have f1: "\<And>c. (\<Squnion>n. Y n . c) = Lub Y . c"
    using sbgetch_lub by fastforce
  then show ?thesis
    using a1 by (metis ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg)
qed

(* The chain of SBs resulting from applying the 2nd inner statement to a chain has domain ch2 *)
lemma contfun_innerLub_dom: fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "chain Y \<Longrightarrow> {ch2} = sbDom\<cdot>(\<Squnion>i. ([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))"
proof -
  assume a1: "chain Y"
  hence f1: "chain (\<lambda> i.([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))"
    by simp
  hence f2: "\<forall> i.  sbDom\<cdot>(([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>)) = {ch2}"
    by (simp add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub)
  hence f3: "\<forall> i. (([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))  \<sqsubseteq> (\<Squnion>i. ([ch2 \<mapsto> (f2\<cdot>((Y i) . ch3))]\<Omega>))"
    using f1 is_ub_thelub by blast
  thus ?thesis
    using f1 f2 sbChain_dom_eq2 by blast
qed

(* The SB resulting from the second inner statement in spf_feed_sb_inout2_iter is cont *)
lemma contfun_getch_cont [simp]: fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont (\<lambda> z. ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>))"
  apply (rule mycontI2, simp only: contfun_monofun)
  apply(rule sb_below)
   apply (simp_all add: sbdom_rep_eq sbgetch_rep_eq sbgetch_lub
                        contfun_innerLub_dom)
    using ch2ch_Rep_cfunL ch2ch_Rep_cfunR contlub_cfun_arg po_eq_conv by blast

(* inout2 is cont *)
lemma spf_feed_sb_inout2_iterable_cont[simp]: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                               fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont (\<lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)
                      \<uplus> ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>))"
  by simp

(* inout2's domain is {ch2, ch3}  *)
lemma spf_feed_sb_inout2_dom: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                              fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "sbDom\<cdot>((\<Lambda> z.([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)
                                \<uplus> ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>)) = {ch2, ch3}"
proof -
  have "sbDom\<cdot>([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>\<epsilon>)]\<Omega>) = {ch3}"
    by (simp add: sbdom_rep_eq)
  moreover
  have "sbDom\<cdot>([ch2 \<mapsto> f2\<cdot>\<epsilon>]\<Omega>) = {ch2}"
    by (simp add: sbdom_rep_eq)
  ultimately
  show ?thesis
    by simp
qed

(* Shortening inout2 if we are only interested in ch3 *)
lemma spf_feed_inout2_iter_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                               fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "ch2 \<noteq> ch3"
  shows "iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>) . ch3
        =iterate i\<cdot>(\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)
                          \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>) . ch3"
proof (induction i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case
  proof -
    have f1: "\<And> z. (([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)  \<uplus> ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>)) . ch3
                    = f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))"
      apply (subst sbunion_getchL)
       apply (simp_all add: sbdom_rep_eq assms sbgetch_rep_eq)
        using assms by blast
    thus ?thesis
      apply (unfold iterate_Suc)
      apply (simp add: f1 sbgetch_rep_eq)
      using Suc.IH by presburger
  qed
qed





lemma gen_fix_insert: "(\<Lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>x\<cdot>(f2\<cdot>z))\<cdot>\<epsilon>)\<cdot>s
                        = (\<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>s\<cdot>(f2\<cdot>z))\<cdot>\<epsilon>)"
  by simp




(* Result step 4: gen_fix for an SB with sole channel ch1 corresponds to inout2 *)
lemma spf_feed_sb_inout2_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                             fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "sb = ([ch1 \<mapsto> s]\<Omega>)" and "ch2 \<noteq> ch3"
  shows "(gen_fix f1 f2)\<cdot>s = ((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)
                                            \<uplus> ([ch2 \<mapsto> (f2\<cdot>(z . ch3))]\<Omega>))\<cdot>({ch2, ch3}^\<bottom>)) sb) .ch3"
proof -
  have f1: "(gen_fix f1 f2)\<cdot>s
             =((\<lambda> x. \<Squnion>i. iterate i\<cdot>(\<Lambda> z. [ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>(z . ch3))]\<Omega>)\<cdot>({ch3}^\<bottom>)) sb) .ch3"
    using assms(1) spf_feed_sb_inout1_eq by blast
  show ?thesis
  apply (simp only: f1)
  apply (subst sbgetch_lub)
  apply(rule sbIterate_chain, simp add: sbdom_rep_eq)
   apply (subst sbgetch_lub)
   apply(rule sbIterate_chain)
     apply(simp only: spf_feed_sb_inout2_dom)
    by(subst spf_feed_inout2_iter_eq, simp_all add: assms)
qed


subsection \<open>step5\<close>

(* inout3 is cont *)
lemma spf_feed_sb_inout3_iterable_cont[simp]: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                              fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "cont (\<lambda> z.  ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(z . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))"
  by simp




(* Iteration insert rule for i+1 iterations of inout2 *)
lemma spf_feed_sb_inout2_iter_suc_insert: "spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x (Suc i)
  = (([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(f2\<cdot>((spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i) . ch3))]\<Omega>)
      \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i) . ch3)]\<Omega>))"
  by simp

(* Iteration insert rule for i+1 iterations of inout3 *)
lemma spf_feed_sb_inout3_iter_suc_insert: "spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (Suc i)
  = (([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i) . ch2)]\<Omega>)
      \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i) . ch3)]\<Omega>))"
  by simp

(* Iteration insert rule for 2*(i+1) iterations of inout3 *)
lemma spf_feed_sb_inout3_iter_two_suc_insert:
  shows "spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) *  (Suc i))
   = (\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(z . ch2)]\<Omega>)
      \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (Suc (2 * i)))"
  by simp


lemma spf_feed_sb_inout3_iter_2_suc_insert: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                            fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows " (\<Lambda> z. ([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>(z . ch2)]\<Omega>) \<uplus> ([ch2 \<mapsto> f2\<cdot>(z . ch3)]\<Omega>))\<cdot>(([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>
  ((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch2)]\<Omega>)
      \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch3)]\<Omega>))
  =  (([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>((([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>
                ((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch2)]\<Omega>)
                \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x
                                                        ((2::nat) * Suc i)) . ch3)]\<Omega>)) . ch2)]\<Omega>)
      \<uplus> ([ch2 \<mapsto> f2\<cdot>((([ch3 \<mapsto> f1\<cdot>(x . ch1)\<cdot>
                ((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * Suc i)) . ch2)]\<Omega>)
                \<uplus> ([ch2 \<mapsto> f2\<cdot>((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x
                                                        ((2::nat) * Suc i)) . ch3)]\<Omega>)) . ch3)]\<Omega>))"
  apply (subst beta_cfun, simp)
    by blast


(* for the getch inserts use sb_onech_getch_insert *)

lemma spf_feed_sb_inout3_even_iter_ch_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                          fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "((spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * i) . ch3))
            = ((add\<cdot>(x . ch1)\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * i) . ch2)))"
  shows "f1\<cdot>(x . ch1)\<cdot>
          (appendElem2 (0::nat)\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * i) . ch3))
        = f1\<cdot>(x . ch1)\<cdot>
          (appendElem2 (0::nat)\<cdot>(add\<cdot>(x . ch1)\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x
                                                                            ((2::nat) * i) . ch2)))"
    by (simp add: assms)


lemma spf_feed_iter_new_ch_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                               fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "ch2 \<noteq> ch3" and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
  shows "spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * i) . ch3
         = f1\<cdot>(x . ch1)\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x ((2::nat) * i) . ch2)"
  proof (induction i)
    case 0
    then show ?case
      apply (simp add: sbdom_rep_eq)
      by (simp add: assms(2))
  next
    case (Suc i)
    hence "spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * i) . ch3
            = f1\<cdot>(x . ch1)\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * i) . ch2)"
      by blast
    then show ?case
      apply (subst spf_feed_sb_inout3_iter_two_suc_insert, subst spf_feed_sb_inout3_iter_suc_insert)
      apply(simp add: sbgetch_rep_eq)
      apply (subst sbunion_getchR, simp add: sbdom_rep_eq)
      apply(subst sbunion_getchL, simp add: sbdom_rep_eq)
         using assms apply blast
         apply(simp add: sbdom_rep_eq)
       apply(subst sbunion_getchL, simp add: sbdom_rep_eq)
         using assms apply blast
         apply (simp add: sbgetch_rep_eq)
         apply(subst sbunion_getchL, simp add: sbdom_rep_eq)
         using assms apply blast
         by (simp add: sbgetch_rep_eq)
     qed

(* this lemma is written very hackily because simp goes wild *)
(* inout2 and inout3 do the same, though inout2 only needs half the steps *)
lemma spf_feed_step5_lub_iter_eq_req: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                      fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "ch2 \<noteq> ch3" and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
  shows "spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x (Suc i)
        = spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * (Suc i))"
proof (induction i)
  case 0
  then show ?case
    apply(subst two_times_one_insert)
    apply (unfold iterate_Suc)
    apply auto
    apply(rule sbunion_eqI, rule sb_one_ch_eqI)
     apply (simp_all add: sbdom_rep_eq assms sbgetch_rep_eq)
    apply(subst sbunion_getchL, simp add: sbdom_rep_eq sbgetch_rep_eq)
      using assms apply blast
      by (simp add: sbgetch_rep_eq)
next
  case (Suc i)
  hence "spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x (Suc i)
        = spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * Suc i)"
    by blast
  then show ?case
    apply (subst spf_feed_sb_inout2_iter_suc_insert)
    apply(subst spf_feed_sb_inout3_iter_two_suc_insert, subst spf_feed_sb_inout3_iter_suc_insert,
          subst spf_feed_sb_inout3_iter_2_suc_insert)
    apply(rule sbunion_eqI)
      (* channel ch3 *)
     apply(rule sb_one_ch_eqI)
     apply(rule cfun_arg_eqI)
     apply(subst sbunion_getchR)
      apply (simp add: sbdom_rep_eq sbgetch_rep_eq)
     apply (simp add: sbgetch_rep_eq)
      (* channel ch2 *)
    apply(rule sb_one_ch_eqI)
    apply(rule cfun_arg_eqI)
      (* on a slow machine, the next step may take some time *)
    apply(subst sbunion_getchL, simp add: sbdom_rep_eq sbgetch_rep_eq)
    using assms apply blast
    apply (simp only:  sb_onech_getch_insert)
      by (rule spf_feed_iter_new_ch_eq, simp_all add: assms)
  qed

lemma spf_feed_step5_lub_iter_eq_req2: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                       fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "ch2 \<noteq> ch3" and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
  shows "spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i
        = spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * i)"
proof (cases "i = 0")
  case True
  then show ?thesis
    by simp
next
  case False
  hence "0 < i \<Longrightarrow> spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i
                    = spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x (2 * i)"
    proof -
    obtain j where "i = Suc(j)"
      using False not0_implies_Suc by auto
    thus ?thesis
      using spf_feed_step5_lub_iter_eq_req assms by blast
  qed
  then show ?thesis
    using False by blast
qed

(* LUB of inout2 and inout3 are the same *)
lemma spf_feed_step5_lub_iter_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                  fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "ch2 \<noteq> ch3" and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
  shows "(\<Squnion>i. spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 x i)
        = (\<Squnion>i. spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i)"
  apply (rule lub_mult2_shift_eq)
    apply (rule sbIterate_chain, simp add: sbdom_rep_eq)
   apply (rule sbIterate_chain, simp add: sbdom_rep_eq)
  using spf_feed_step5_lub_iter_eq_req2 assms by simp

(* Resulting lemma of step 5: gen_fix is the LUB of inout3 *)
lemma spf_feed_sb_in_out_eq: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                             fixes f2 :: "nat stream \<rightarrow> nat stream"
  assumes "sb = ([ch1 \<mapsto> s]\<Omega>)" and "ch2 \<noteq> ch3" and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
  shows "(gen_fix f1 f2)\<cdot>s = (\<lambda> x. (\<Squnion>i. spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i)) sb . ch3"
proof -
  have f1: "(gen_fix f1 f2)\<cdot>s = (\<Squnion>i. spf_feed_sb_inout2_iter f1 f2 ch1 ch2 ch3 sb i) . ch3"
    by (rule spf_feed_sb_inout2_eq, simp_all add: assms)
  show ?thesis
    apply (subst f1)
    using spf_feed_step5_lub_iter_eq assms by presburger
qed


subsection \<open>step6\<close>

(* Domain of inout3 is {ch2, ch3} *)
lemma spf_feed_sb_inout3_iter_dom: fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                   fixes f2 :: "nat stream \<rightarrow> nat stream"
  shows "sbDom\<cdot>(spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 sb i) = {ch2,ch3}"
proof (induction i)
  case 0
  then show ?case
    by simp
next
  case (Suc i)
  then show ?case
    apply (subst spf_feed_sb_inout3_iter_suc_insert)
      by (simp add: sbdom_rep_eq)
  qed

(* Reverse definition of SPF2x1 *)
lemma SPF2x1_apply_rev: assumes "ch1 \<noteq> ch2"
  shows "([ch3 \<mapsto> (f\<cdot>s1\<cdot>s2)]\<Omega>)
        = (SPF2x1 f (ch1, ch2, ch3)) \<rightleftharpoons> ([ch1 \<mapsto> (s1:: nat stream), ch2  \<mapsto> (s2:: nat stream)]\<Omega>) "
  apply(simp add: SPF2x1_rep_eq sb_id_def sbgetch_insert)
  by(auto simp add: sbdom_rep_eq assms)


(* Shorthand for iterating SBs *)
abbreviation iter_sbfix:: "('m SB \<Rightarrow> 'm SB \<rightarrow> 'm SB) \<Rightarrow> nat \<Rightarrow> channel set \<Rightarrow> 'm SB \<Rightarrow> 'm SB" where
"iter_sbfix F i cs \<equiv> (\<lambda> x. iterate i\<cdot>(F x)\<cdot>(cs^\<bottom>))"
    
(* iterCompH can be expressed using inout3 *)
lemma spf_feed_SPF_eq:  fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                        fixes f2 :: "nat stream \<rightarrow> nat stream"
                        assumes "sbDom\<cdot>sb = {ch1}" and "ch1 \<noteq> ch2" and "ch1 \<noteq> ch3" and "ch2 \<noteq> ch3"
                        and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
                        and "spf1 = SPF2x1 f1 (ch1,ch2,ch3)" and "spf2 = SPF1x1 f2 (ch3,ch2)"
  shows "(iter_spfCompH spf1 spf2 i) sb = spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 sb i"
proof (induction i)
  case 0
  then show ?case
    by (simp add: assms)
next
  case (Suc i)
  have spf2x1revapp:"\<And> f s1 s2. ([ch3 \<mapsto> (f\<cdot>s1\<cdot>s2)]\<Omega>)
          = (SPF2x1 f (ch1, ch2, ch3)) \<rightleftharpoons> ([ch1 \<mapsto> (s1:: nat stream), ch2  \<mapsto> (s2:: nat stream)]\<Omega>)"
    by (simp add: SPF2x1_apply assms)
  have spf1x1revapp: "\<And> f s.([ch2 \<mapsto> f\<cdot>(s:: nat stream)]\<Omega>)
                            = (SPF1x1 f (ch3, ch2)) \<rightleftharpoons> ([ch3 \<mapsto> s]\<Omega>)"
    by (simp add: SPF1x1_apply assms)
  hence "iter_sbfix (spfCompH spf1 spf2) i (spfRan\<cdot>spf1 \<union> spfRan\<cdot>spf2) sb
                                                  = spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 sb i"
    using Suc.IH  by blast
  then show ?case
    apply (subst spf_feed_sb_inout3_iter_suc_insert, subst iter_spfCompOldh3_suc_insert)
    apply(rule sbunion_eqI)

     (* spf1 component *)
     apply (subst assms(6),subst spf2x1revapp, rule spf_arg_eqI, simp)
     apply(subst sbunion_restrict3)
      (* left bundle prep *)
       apply(subst sbres_sbdom_supset, simp add: assms)
       apply(simp only: assms, subst nat_sb_repackage, simp add: assms)
      (* right bundle prep *)
      apply(simp only: SPF2x1_dom)
      apply(subst sbres_sbdom_supset_inter, simp add: spf_feed_sb_inout3_iter_dom assms)
      apply(subst nat_sb_repackage, simp add: spf_feed_sb_inout3_iter_dom, simp add: sbunion_insert)

      (* spf2 component *)
      apply (subst assms(7), subst spf1x1revapp, rule spf_arg_eqI, simp add: assms)
      apply (subst nat_sb_repackage)
        apply (simp add: spf_feed_sb_inout3_iter_dom)
        by (rule sb_one_ch_eqI, rule sbunion_getchR, simp add: spf_feed_sb_inout3_iter_dom)
qed


(* Result of step 6: gen_fix is the same as the LUB of spfCompH *)
lemma gen_fix_iter_spfComp_eq:  fixes f1 :: "nat stream \<rightarrow> nat stream  \<rightarrow> nat stream"
                                fixes f2 :: "nat stream \<rightarrow> nat stream"
                                assumes "sb = ([ch1 \<mapsto> s]\<Omega>)"
                                and "ch1 \<noteq> ch2" and "ch1 \<noteq> ch3" and "ch2 \<noteq> ch3"
                                and "\<forall>sb . f1\<cdot>(sb . ch1)\<cdot>\<epsilon> = \<epsilon>"
                                and "spf1 = SPF2x1 f1 (ch1,ch2,ch3)"
                                and "spf2 = SPF1x1 f2 (ch3,ch2)"
  shows "(gen_fix f1 f2)\<cdot>s = (\<Squnion>i. (iter_spfCompH spf1 spf2 i) sb) .ch3"
proof -
  have f1: "(gen_fix f1 f2)\<cdot>s = (\<lambda> x. (\<Squnion>i. spf_feed_sb_inout3_iter f1 f2 ch1 ch2 ch3 x i)) sb . ch3"
    by (rule spf_feed_sb_in_out_eq, simp_all add: assms)
  have f2: "(\<Squnion>i. iterate i\<cdot>(\<Lambda> z. f1\<cdot>s\<cdot>(f2\<cdot>z))\<cdot>\<epsilon>) = (gen_fix f1 f2)\<cdot>s"
    by simp
  show ?thesis
  apply (subst spf_feed_SPF_eq, simp_all add: assms)
   apply(simp add: sbdom_rep_eq)
    by (subst f2, subst f1, simp add: assms(1))
qed


(* USAGE: use gen_fix_iter_spfComp_eq to show the equality behind the \<leadsto> if domain is correct
          otherwise the equality is trivial see SPF_FeedComp_JB, Feedback_MW as example *)








end


