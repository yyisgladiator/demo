(*  Title:  TstreamCausality_HK.thy
    Author: Hendrik Kausch
    e-mail: hendrik.kausch@rwth-aachen.de

    Description:  Definitons and lemmas for Causality with tstream functions
*)

theory TStreamCausality_HK
imports TStream StreamCase_Study
begin







(* ----------------------------------------------------------------------- *)
  section \<open>"weak/strong Causality"\<close>
(* ----------------------------------------------------------------------- *)



(* tspf_weakCausality defines equality of the input up to time n to imply equality of the output 
   up to time n *)
definition tspf_weakCausality :: "('a tstream \<Rightarrow> 'a tstream) \<Rightarrow> bool" where
"tspf_weakCausality f \<equiv> (\<forall> (n :: nat) (ts1 :: 'a tstream) (ts2 :: 'a tstream).
                        (ts1\<down>n) = (ts2\<down>n) \<longrightarrow> ((f ts1)\<down>n) = ((f ts2)\<down>n))"

(*tspf_strongCausaltiy defines equality of the input up to time n to imply equality of the output 
  up to time n+1 *)
definition tspf_strongCausality :: "('a tstream \<Rightarrow> 'a tstream) \<Rightarrow> bool" where
"tspf_strongCausality f \<equiv> (\<forall> (n :: nat) (ts1 :: 'a tstream) (ts2 :: 'a tstream).
                          (ts1\<down>n) = (ts2\<down>n) \<longrightarrow> ((f ts1)\<down>(Suc n)) = ((f ts2)\<down>(Suc n)))"

lemma tspf_weakCau: "tspf_weakCausality f \<and> (ts1\<down>n) = (ts2\<down>n) \<Longrightarrow> ((f ts1)\<down>n) = ((f ts2)\<down>n)"
using tspf_weakCausality_def by auto

lemma tspf_strongCau: "tspf_strongCausality f \<and> (ts1\<down>n) = (ts2\<down>n) \<Longrightarrow> ((f ts1)\<down>(Suc n)) = ((f ts2)\<down>(Suc n))"
using tspf_strongCausality_def by auto

lemma tspf_strng_weak: "tspf_strongCausality f \<Longrightarrow> tspf_weakCausality f "
apply (simp add: tspf_strongCausality_def tspf_weakCausality_def)
using tsSucTake by blast

lemma tspf_weakCau_down: "tspf_weakCausality f \<and> (ts1\<down>n) = (ts2\<down>n) \<and> x\<le>n \<Longrightarrow> ((f ts1)\<down>x) = ((f ts2)\<down>x)"
using tspf_weakCausality_def tstake_less 
by blast

lemma tspf_strongCau_down: "tspf_strongCausality f \<and> (ts1\<down>n) = (ts2\<down>n) \<and> x\<le>(Suc n) \<Longrightarrow> ((f ts1)\<down>x) = ((f ts2)\<down>x)"
using tspf_strongCausality_def tstake_less tspf_strng_weak
by blast


(* ----------------------------------------------------------------------- *)
  section \<open>"sum4 test"\<close>
(* ----------------------------------------------------------------------- *)

definition testSum4:: "nat stream" where
"testSum4 = sum4\<cdot> (<[1,4,3]>)"

lemma sum4_three_unfold [simp]: "sum4\<cdot>(\<up>a \<bullet> \<up>b \<bullet> \<up>c) = sum4\<cdot>(\<up>a \<bullet> \<up>b) \<bullet> sum4\<cdot>(\<up>(a+b+c))"
using sum4_unfold
by (smt Groups.add_ac(1) Groups.add_ac(2) add_eps1 add_unfold assoc_sconc lscons_conv sum4_one sup'_def)

lemma sum4_three: "sum4\<cdot>(\<up>a \<bullet> \<up>b \<bullet> \<up>c) = \<up>a \<bullet> \<up>(a+b) \<bullet> \<up>(a+b+c)"
using sum4_three_unfold sum4_two
by auto

lemma testSum4_eq: "testSum4 = <[1,5,8]>"
by (simp add: testSum4_def)




(* ----------------------------------------------------------------------- *)
  section \<open>"Stream tests"\<close>
(* ----------------------------------------------------------------------- *)


definition twoPowerStream_1 :: "nat stream" where  (* also  = <1 2 4 8 \<dots>> *)
"twoPowerStream_1 \<equiv> fix\<cdot> (\<Lambda> y. \<up>1 \<bullet> smap (\<lambda>x. x*2)\<cdot>y)"

definition twoPowerStream_2 :: "nat stream" where  
"twoPowerStream_2 = siterate (\<lambda>x. x*2) 1"


end