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


(* ----------------------------------------------------------------------- *)
  section \<open>"sum5 TStream_def"\<close>
(* ----------------------------------------------------------------------- *)
(*
definition tshd:: "'a tstream \<Rightarrow> 'a" where
"tshd ts \<equiv> THE a. shd (tsAbs\<cdot>ts) = a"
*)
definition stwbl      :: "('a \<Rightarrow> bool) \<Rightarrow> 'a spfo" where
"stwbl f \<equiv> fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. 
                          if (f a) then \<up>a \<bullet>  h\<cdot>(srt\<cdot>s) else \<up>a))"

definition shddw      :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> 'a" where
"shddw f x \<equiv> shd (sdropwhile f\<cdot>x)"


(* drops \<surd> and takes first Msg of the tstream *)
definition tshd :: "'a tstream \<Rightarrow> 'a" where
"tshd ts \<equiv> THE x. Msg x = shddw (\<lambda>a. a=\<surd>) (Rep_tstream ts)"

(* drops \<surd> and first Msg of the tstream *)
definition tsrt :: "'a tstream \<rightarrow> 'a tstream" where
"tsrt \<equiv> \<Lambda> ts. Abs_tstream (srtdw(\<lambda>a. a=\<surd>)\<cdot>(Rep_tstream ts))"


definition stwdroprt :: "('a \<Rightarrow> bool) \<Rightarrow> 'a spfo" where
"stwdroprt f \<equiv> fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. 
                          if (f a) then \<up>a \<bullet>  h\<cdot>(srt\<cdot>s) else \<bottom>))"


(* takes first \<surd>s and drops rest of the tstream *)
definition tsTickrt :: "'a tstream \<rightarrow> 'a tstream" where
"tsTickrt \<equiv> \<Lambda> ts. Abs_tstream (stwdroprt (\<lambda>a. a=\<surd>)\<cdot>(Rep_tstream ts))"


primrec tsrtdrop:: "nat \<Rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsrtdrop 0 = ID"|
"tsrtdrop (Suc n) = (\<Lambda> ts. tsrtdrop n\<cdot>(tsrt\<cdot> ts))"


primrec tsh :: "nat \<Rightarrow> nat tstream \<Rightarrow> nat \<Rightarrow> nat tstream" where
"tsh 0 ts y = \<bottom>" | (*maximal one non-variable argument required, so \<epsilon>-case must be encoded in the line below.*)
"tsh (Suc n) ts y = (if tsAbs\<cdot>ts=\<epsilon> then \<bottom> else  (tsTickrt\<cdot>ts) \<bullet> (Abs_tstream(\<up>(Msg(tshd ts + y )))) \<bullet> (tsh n (tsrt\<cdot> ts) (shd (tsAbs\<cdot>ts)+ y)))"


definition tssum5_helper :: " nat \<Rightarrow> nat tstream \<rightarrow> nat tstream" where
"tssum5_helper n \<equiv> \<Lambda> x. \<Squnion>i. tsh i x n"


definition tssum5:: "nat tstream \<rightarrow> nat tstream" where
"tssum5 \<equiv> \<Lambda> x. tssum5_helper 0\<cdot>x"

lemma tsAbs_bot[simp]: "tsAbs\<cdot>\<bottom> = \<epsilon>"
by(simp add: tsAbs_def)

lemma tsh_bot: "tsh n \<bottom> y = \<bottom>"
by(induct_tac n,auto)

end