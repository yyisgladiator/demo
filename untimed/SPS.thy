theory SPS

imports SPF "../USpec_Comp"

begin

default_sort message

type_synonym 'm SPS = "'m SPF uspec"



section \<open>Definition\<close>


definition spsConcOut:: "'m SB \<Rightarrow> 'm SPS \<rightarrow> 'm SPS" where
"spsConcOut sb = Abs_cfun (uspecImage (Rep_cfun (spfConcOut sb)))"

definition spsRtIn:: "'m SPS \<rightarrow> 'm SPS" where
"spsRtIn = Abs_cfun (uspecImage (Rep_cfun spfRtIn))"


section \<open>Lemma\<close>

  subsection \<open>spsConcOut\<close>

lemma spsconcout_cont: 
  assumes "\<And>c. c\<in>ubDom\<cdot>sb \<Longrightarrow> # (sb . c) < \<infinity>"
  shows"cont (uspecImage (Rep_cfun (spfConcOut sb)))"
  apply(rule uspecimage_inj_cont)
  using assms spfconc_surj apply blast
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  
lemma spsconcout_insert: 
  assumes "\<And>c. c\<in>ubDom\<cdot>sb \<Longrightarrow> # (sb . c) < \<infinity>"
  shows"spsConcOut sb\<cdot>sps =  (uspecImage (Rep_cfun (spfConcOut sb)) sps)"
  apply(simp only: spsConcOut_def)
  by (simp add: assms spsconcout_cont)

lemma spsconcout_dom [simp]: 
  assumes "\<And>c. c\<in>ubDom\<cdot>sb \<Longrightarrow> # (sb . c) < \<infinity>"
  shows "uspecDom\<cdot>(spsConcOut sb\<cdot>sps) = uspecDom\<cdot>sps"
  by (simp add: assms spsconcout_insert ufclDom_ufun_def ufclRan_ufun_def)

lemma spsconcout_ran [simp]: 
  assumes "\<And>c. c\<in>ubDom\<cdot>sb \<Longrightarrow> # (sb . c) < \<infinity>"
  shows "uspecRan\<cdot>(spsConcOut sb\<cdot>sps) = uspecRan\<cdot>sps"
  by (simp add: assms spsconcout_insert ufclDom_ufun_def ufclRan_ufun_def)



  subsection \<open>spsRtIn\<close>

lemma spsrtin_cont: "cont (uspecImage (Rep_cfun spfRtIn))"
  apply(rule uspecimage_inj_cont)
   apply (simp add: spfRt_inj)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)

lemma spsrtin_insert: "spsRtIn\<cdot>sps = uspecImage (Rep_cfun spfRtIn) sps"
  apply(simp add: spsRtIn_def spsrtin_cont)
  done

lemma spsrtin_dom [simp]: "uspecDom\<cdot>(spsRtIn\<cdot>sps) = uspecDom\<cdot>sps"
  by (simp add: spsRtIn_def spsrtin_cont ufclDom_ufun_def ufclRan_ufun_def)

lemma spsrtin_ran [simp]: "uspecRan\<cdot>(spsRtIn\<cdot>sps) = uspecRan\<cdot>sps"
  by (simp add: spsRtIn_def spsrtin_cont ufclDom_ufun_def ufclRan_ufun_def)

  
end