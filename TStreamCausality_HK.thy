(*  Title:  TstreamCausality_HK.thy
    Author: Hendrik Kausch
    e-mail: hendrik.kausch@rwth-aachen.de

    Description:  Definitons and lemmas for Causality with tstream functions
*)

theory TStreamCausality_HK
imports TStreamTheorie
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


end