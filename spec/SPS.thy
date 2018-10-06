theory SPS

imports fun.SPF USpec_Comp

begin

default_sort message

type_synonym ('m,'n) SPS = "('m,'n) SPF uspec"

section \<open>Definition\<close>
                         
definition uspecConstOut:: "channel set \<Rightarrow> 'n::message SB  \<Rightarrow> ('m,'n) SPF uspec" where
"uspecConstOut \<equiv> \<lambda> In sb. uspecConst (ufConst In\<cdot>sb)"

definition spsConcOut:: "'n SB \<Rightarrow> ('m,'n) SPS \<Rightarrow> ('m,'n) SPS" where
"spsConcOut sb = (uspecImage (Rep_cfun (spfConcOut sb)))"

definition spsConcIn:: "'m SB \<Rightarrow> ('m,'n) SPS \<Rightarrow> ('m,'n) SPS" where
"spsConcIn sb = uspecImage (Rep_cfun (spfConcIn sb))"

definition spsRtIn:: "('m,'n) SPS \<rightarrow> ('m,'n) SPS" where
"spsRtIn = Abs_cfun (uspecImage (Rep_cfun spfRtIn))"


section \<open>Lemma\<close>

(* ----------------------------------------------------------------------- *)
subsection \<open>uspecConstOut\<close>
(* ----------------------------------------------------------------------- *)
lemma uspecconstout_insert: "uspecConstOut In sb =  uspecConst (ufConst In\<cdot>sb)"
  by (simp add: uspecConstOut_def)

lemma uspecconstout_dom[simp]: "uspecDom\<cdot>(uspecConstOut In sb) = In"
  apply (simp add: uspecconstout_insert)
  by (simp add: ufclDom_ufun_def uspecconst_dom)

lemma uspecconstout_ran[simp]: "uspecRan\<cdot>(uspecConstOut In sb) = ubclDom\<cdot>sb"
  apply (simp add: uspecconstout_insert)
  by (simp add: ufclRan_ufun_def uspecconst_ran)


(* ----------------------------------------------------------------------- *)
subsection \<open>spsConcOut\<close>
(* ----------------------------------------------------------------------- *)

lemma spsconcout_mono: "monofun (uspecImage (Rep_cfun (spfConcOut sb)))"
  apply (rule uspecimage_mono)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)


lemma spsconcout_cont: 
  assumes "\<And>c. c\<in>ubDom\<cdot>sb \<Longrightarrow> # (sb . c) < \<infinity>"
  shows "cont (uspecImage (Rep_cfun (spfConcOut sb)))"
  apply(rule uspecimage_inj_cont)
  using assms spfconc_surj apply blast
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)
  
lemma spsconcout_insert: 
  "spsConcOut sb sps = (uspecImage (Rep_cfun (spfConcOut sb)) sps)"
  by (simp only: spsConcOut_def)

lemma spsconcout_dom [simp]: 
  "uspecDom\<cdot>(spsConcOut sb sps) = uspecDom\<cdot>sps"
  apply (simp add: spsconcout_insert)
  by (simp add: spsconcout_insert ufclDom_ufun_def ufclRan_ufun_def)

lemma spsconcout_ran [simp]: 
  "uspecRan\<cdot>(spsConcOut sb sps) = uspecRan\<cdot>sps"
  by (simp add: spsconcout_insert ufclDom_ufun_def ufclRan_ufun_def)

lemma spsconcout_obtain: assumes "uspec_in g (spsConcOut sb sps)"
  shows "\<exists> f. uspec_in f sps \<and> g = spfConcOut sb\<cdot>f"
  by (metis (no_types, lifting) assms spfConcOut_dom spfConcOut_ran spsconcout_insert ufclDom_ufun_def ufclRan_ufun_def uspecimage_obtain)

lemma spsconcout_const[simp]: "spsConcOut sb (uspecConst f) = uspecConst (spfConcOut sb\<cdot>f)"
  apply(simp add: spsConcOut_def)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)

lemma spsconcout_consistentI: assumes "uspecIsConsistent S" 
  shows "uspecIsConsistent (spsConcOut sb S)"
  by (metis (no_types, hide_lams) assms emptyE spfConcOut_dom spfConcOut_ran spsConcOut_def 
      ufclDom_ufun_def ufclRan_ufun_def uspecIsConsistent_def uspec_consist_f_ex uspecimage_ele_in uspecrevset_insert)

(* ----------------------------------------------------------------------- *)
subsection \<open>spsConcIn\<close>
(* ----------------------------------------------------------------------- *)

lemma spsconcin_insert: "spsConcIn sb sps = (uspecImage (Rep_cfun (spfConcIn sb)) sps)"
  by (simp add: spsConcIn_def)

lemma spsconcin_dom: "uspecDom\<cdot>(spsConcIn sb sps) = uspecDom\<cdot>sps"
  by (simp add: spsConcIn_def ufclDom_ufun_def ufclRan_ufun_def)

lemma spsconcin_ran:  "uspecRan\<cdot>(spsConcIn sb sps) = uspecRan\<cdot>sps"
  by (simp add: spsConcIn_def ufclDom_ufun_def ufclRan_ufun_def)

lemma spsconcin_const[simp]: "spsConcIn sb (uspecConst f) = uspecConst (spfConcIn sb\<cdot>f)"
  apply(simp add: spsConcIn_def)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)

lemma spsconcin_ele: assumes "uspec_in g H"
  shows "\<And> sbe. uspec_in (spfConcIn sbe\<cdot>g) (spsConcIn sbe H)"
  by (simp add: assms spsConcIn_def ufclDom_ufun_def ufclRan_ufun_def uspecimage_ele_in)
(* ----------------------------------------------------------------------- *)
subsection \<open>spsRtIn\<close>
(* ----------------------------------------------------------------------- *)

lemma spsrtin_cont: "cont (uspecImage (Rep_cfun spfRtIn))"
  apply(rule uspecimage_inj_cont)
  apply (simp add: spfRt_inj)
  by (simp add: ufclDom_ufun_def ufclRan_ufun_def)

lemma spsrtin_insert: "spsRtIn\<cdot>sps = uspecImage (Rep_cfun spfRtIn) sps"
  by(simp add: spsRtIn_def spsrtin_cont)

lemma spsrtin_dom [simp]: "uspecDom\<cdot>(spsRtIn\<cdot>sps) = uspecDom\<cdot>sps"
  by (simp add: spsRtIn_def spsrtin_cont ufclDom_ufun_def ufclRan_ufun_def)

lemma spsrtin_ran [simp]: "uspecRan\<cdot>(spsRtIn\<cdot>sps) = uspecRan\<cdot>sps"
  by (simp add: spsRtIn_def spsrtin_cont ufclDom_ufun_def ufclRan_ufun_def)

(*
lemma spsconcout_inj: 
  assumes "\<And>c. c\<in>ubDom\<cdot>sb \<Longrightarrow> # (sb . c) < \<infinity>"
  shows "inj (\<lambda>sps. spsConcOut sb sps)"

proof -
  have f1: "\<forall>c. c \<notin> ubDom\<cdot>sb \<or> #(sb . c) < \<infinity>"
    by (meson assms)
  have f2: "\<forall>f u ua. ((\<exists>u ua. (ufclDom\<cdot>(u::('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun) = ufclDom\<cdot>ua \<and> ufclRan\<cdot>u = ufclRan\<cdot>ua) 
    \<and> (ufclDom\<cdot>(f u::('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun) \<noteq> ufclDom\<cdot>(f ua) \<or> ufclRan\<cdot>(f u) \<noteq> ufclRan\<cdot>(f ua))) \<or> 
    \<not> inj f \<or> uspecDom\<cdot>u \<noteq> uspecDom\<cdot>ua \<or> uspecRan\<cdot>u \<noteq> uspecRan\<cdot>ua \<or> uspecRevSet\<cdot>(uspecImage f u) 
    \<noteq> uspecRevSet\<cdot>(uspecImage f ua)) \<or> u = ua"
    by (meson urs_img_inj uspec_eqI)
  obtain uu :: "(('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun \<Rightarrow> ('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun) \<Rightarrow> ('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun" and uua :: 
    "(('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun \<Rightarrow> ('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun) \<Rightarrow> ('a stream\<^sup>\<Omega>, 'a stream\<^sup>\<Omega>) ufun" where
    "\<forall>x2. (\<exists>v3 v4. (ufclDom\<cdot>v3 = ufclDom\<cdot>v4 \<and> ufclRan\<cdot>v3 = ufclRan\<cdot>v4) \<and> (ufclDom\<cdot>(x2 v3) \<noteq> 
    ufclDom\<cdot>(x2 v4) \<or> ufclRan\<cdot>(x2 v3) \<noteq> ufclRan\<cdot>(x2 v4))) = ((ufclDom\<cdot>(uu x2) = ufclDom\<cdot>(uua x2) \<and> 
    ufclRan\<cdot>(uu x2) = ufclRan\<cdot>(uua x2)) \<and> (ufclDom\<cdot>(x2 (uu x2)) \<noteq> ufclDom\<cdot>(x2 (uua x2)) \<or> 
    ufclRan\<cdot>(x2 (uu x2)) \<noteq> ufclRan\<cdot>(x2 (uua x2))))"
    by moura
  then have f3: "\<forall>f u ua. ((ufclDom\<cdot>(uu f) = ufclDom\<cdot>(uua f) \<and> ufclRan\<cdot>(uu f) = ufclRan\<cdot>(uua f)) \<and> 
    (ufclDom\<cdot>(f (uu f)) \<noteq> ufclDom\<cdot>(f (uua f)) \<or> ufclRan\<cdot>(f (uu f)) \<noteq> ufclRan\<cdot>(f (uua f))) \<or> \<not> inj f 
    \<or> uspecDom\<cdot>u \<noteq> uspecDom\<cdot>ua \<or> uspecRan\<cdot>u \<noteq> uspecRan\<cdot>ua \<or> uspecRevSet\<cdot>(uspecImage f u) \<noteq> 
    uspecRevSet\<cdot>(uspecImage f ua)) \<or> u = ua"
    using f2 by presburger
  have "\<forall>f. (\<exists>u ua. (f (u::('a stream\<^sup>\<Omega>) ufun uspec)::('a stream\<^sup>\<Omega>) ufun uspec) = f ua \<and> u \<noteq> ua) \<or> inj f"
    by (meson injI)
  then obtain uub :: "(('a stream\<^sup>\<Omega>) ufun uspec \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec" 
    and uuc :: "(('a stream\<^sup>\<Omega>) ufun uspec \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec" where
    f4: "\<forall>f. f (uub f) = f (uuc f) \<and> uub f \<noteq> uuc f \<or> inj f"
    by moura
  obtain cc :: "'a stream\<^sup>\<Omega> \<Rightarrow> channel" where
    "\<forall>u ua. cc u \<in> ubDom\<cdot>u \<and> \<not> #(u . cc u) < \<infinity> \<or> spsConcOut u\<cdot>ua = uspecImage (Rep_cfun (spfConcOut u)) ua"
    using spsconcout_insert by moura
  moreover
  { assume "uspecRevSet\<cdot> (uspecImage (Rep_cfun (spfConcOut sb)) (uub (Rep_cfun (spsConcOut sb)))) = 
    uspecRevSet\<cdot> (uspecImage (Rep_cfun (spfConcOut sb)) (uuc (Rep_cfun (spsConcOut sb))))"
    moreover
    { assume "uspecDom\<cdot>(uub (Rep_cfun (spsConcOut sb))) \<noteq> uspecDom\<cdot>(uuc (Rep_cfun (spsConcOut sb)))"
      then have "spsConcOut sb\<cdot>(uub (Rep_cfun (spsConcOut sb))) \<noteq> spsConcOut sb\<cdot>(uuc (Rep_cfun 
      (spsConcOut sb))) \<or> uub (Rep_cfun (spsConcOut sb)) = uuc (Rep_cfun (spsConcOut sb))"
        using f1 spsconcout_dom by metis }
    ultimately have "inj (Rep_cfun (spsConcOut sb)) \<or> spsConcOut sb\<cdot>(uub (Rep_cfun (spsConcOut sb))) 
      \<noteq> spsConcOut sb\<cdot>(uuc (Rep_cfun (spsConcOut sb))) \<or> uub (Rep_cfun (spsConcOut sb)) = uuc 
      (Rep_cfun (spsConcOut sb))"
      using f3 f1 by (metis (no_types) spsconcout_ran spfConcOut_dom spfConcOut_ran spfconc_surj 
        ufclDom_ufun_def ufclRan_ufun_def) }
  ultimately show ?thesis
    using f4 f1 by (metis (no_types))
qed*)

end