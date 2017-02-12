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
tsum s = help s 0

help p \<euro> = \<euro>
help p T:xs = T : help p xs
help p x:xs = (p+x) : help (p+x) xs


primrec tsumhelper:: "nat \<Rightarrow> nat tstream \<Rightarrow> nat tstream" where
"tsumhelper p \<bottom> = \<bottom>" |
"tsumhelper p (tsConc((Abs_tstream(\<up>\<surd>))\<cdot>ts)) = tsConc (Abs_tstream (\<up>\<surd>)) \<cdot>(tsumhelper p ts)" |
"tsumhelper (Suc p) ts = (Suc p + t)"


definition tsum :: "nat tstream \<Rightarrow> nat tstream" where
"tsum ts = tsumhelper 0 ts"
*)


(*
definition tshd:: "'a tstream \<Rightarrow> 'a" where
"tshd ts \<equiv> THE a. shd (tsAbs\<cdot>ts) = a"
*)
(*
definition stwbl      :: "('a \<Rightarrow> bool) \<Rightarrow> 'a spfo" where
"stwbl f \<equiv> fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. 
                          if (f a) then \<up>a \<bullet>  h\<cdot>(srt\<cdot>s) else \<up>a))"

definition shddw      :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> 'a" where
"shddw f x \<equiv> shd (sdropwhile f\<cdot>x)"
*)
(*
(* drops \<surd> and takes first Msg of the tstream *)
definition tshd :: "'a tstream \<Rightarrow> 'a" where
"tshd ts \<equiv> THE x. Msg x = shddw (\<lambda>a. a=\<surd>) (Rep_tstream ts)"


(* drops \<surd> and first Msg of the event stream *)
definition esrt :: "'a event stream \<rightarrow> 'a event stream" where
"esrt \<equiv> \<Lambda> ts. (srtdw(\<lambda>a. a=\<surd>)\<cdot>(ts))"

(* takes as long as f holds, drops the rest*)
definition stwdroprt :: "('a \<Rightarrow> bool) \<Rightarrow> 'a spfo" where
"stwdroprt f \<equiv> fix\<cdot>(\<Lambda> h s. slookahd\<cdot>s\<cdot>(\<lambda> a. 
                          if (f a) then \<up>a \<bullet>  h\<cdot>(srt\<cdot>s) else \<bottom>))"


(* takes first \<surd>s and drops rest of the event stream *)
definition esTickrt :: "'a event stream \<rightarrow> 'a event stream" where
"esTickrt \<equiv> \<Lambda> ts. (stwdroprt (\<lambda>a. a=\<surd>)\<cdot>(ts))"
*)
(*
primrec tsrtdrop:: "nat \<Rightarrow> 'a tstream \<rightarrow> 'a tstream" where
"tsrtdrop 0 = ID"|
"tsrtdrop (Suc n) = (\<Lambda> ts. tsrtdrop n\<cdot>(tsrt\<cdot> ts))"

"sum4 \<equiv>  \<Lambda> x. (fix\<cdot>(\<Lambda> z. add\<cdot>x\<cdot>(\<up>0\<bullet>(z))))"*)

primrec tsh :: "nat \<Rightarrow> nat \<Rightarrow> nat event stream \<Rightarrow> nat event stream" where
"tsh 0 p ts =  \<epsilon>" | (*maximal one non-variable argument required, so \<epsilon>-case must be encoded in the line below.*)
"tsh (Suc n) p ts = (if ts = \<epsilon> then \<epsilon> 
                        else(if shd ts= \<surd> then (\<up>\<surd> \<bullet> (tsh n p (srt\<cdot>ts)))
                                else (\<up>(Msg (p + (THE m. Msg m = shd ts)))) \<bullet> (tsh n (p +(THE m. Msg m = shd ts)) (srt\<cdot> ts))))"


definition tssum5_helper :: " nat \<Rightarrow> nat tstream \<rightarrow> nat tstream" where
"tssum5_helper p \<equiv> \<Lambda> ts. Abs_tstream (\<Squnion>i. tsh i p (Rep_tstream ts))"


definition tssum5:: "nat tstream \<rightarrow> nat tstream" where
"tssum5 \<equiv> \<Lambda> ts. tssum5_helper 0\<cdot>ts"



(*Testing tssum5_def*)

lemma tsAbs_bot[simp]: "tsAbs\<cdot>\<bottom> = \<epsilon>"
by(simp add: tsAbs_def)

lemma tsh_bot: "tsh n p \<epsilon> = \<epsilon>"
by(induct_tac n,auto)

lemma tswell2tswell: "Fin n < #ts \<and> ts_well ts \<Longrightarrow> ts_well (sdrop n\<cdot> ts)"
by simp

lemma AbsStsAbs_tick[simp]: "ts_well as \<Longrightarrow> tsAbs\<cdot> (Abs_tstream (\<up>(\<surd>)\<bullet>as)) = tsAbs\<cdot>(Abs_tstream as)"
by(simp add: tsabs_insert)


lemma tsh_tick[simp]: "ts_well as \<Longrightarrow> tsh (Suc n) p ((\<up>\<surd>)\<bullet>as) = (\<up>\<surd>)\<bullet> tsh n p as"
by(simp add: tsh_def)

lemma tsabs_abs_tick[simp]:"tsAbs\<cdot>(Abs_tstream (\<up>\<surd>)) = \<epsilon>"
by(simp add: tsAbs_def)

lemma tswellinftick: "ts_well ((\<up>\<surd>)\<infinity>)"
by (simp add: ts_well_def)


lemma tssum5_helpersinf[simp]: "tsh (Suc n) p (sinftimes(\<up>\<surd>)) = (\<up>\<surd>) \<bullet> tsh n p (sinftimes (\<up>\<surd>))"
by auto

lemma contlub_tsh:
  "\<forall>s p. tsh i p s = tsh i p (stake i\<cdot>s)"
apply (induct_tac i, auto)
apply (rule_tac x=s in scases)
apply auto
apply (metis (no_types, lifting) inject_scons stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis shd1 stake_Suc surj_scons)
apply (metis lshd_updis stake_Suc stream.sel_rews(3) surj_scons)
apply (rule_tac x=s in scases)
by auto

(*
lemma chain_tsh: "chain tsh"
apply (rule chainI)
apply (subst fun_below_iff)+
apply (induct_tac i, auto)
apply (erule_tac x="x" in allE)
apply (simp add: tsh_bot)
by (smt monofun_cfun_arg)

lemma tsum5_helper2sinf2[simp]: "(\<Squnion>i. tsh i p (\<up>\<surd>)) = \<up>\<surd>"
apply(subst lub_def)
sorry

lemma tssum5_helper2sinf : "Abs_tstream (\<Squnion>i. tsh i p (sinftimes(\<up>\<surd>))) = Abs_tstream(sinftimes(\<up>\<surd>))"
using tswellinftick
sorry

lemma tswell_test: "ts_well ((<[Msg 1,\<surd>,Msg 2,\<surd>,\<surd>,Msg 4]>) \<bullet> (sinftimes(\<up>\<surd>)))"
by(simp add: ts_well_def)

lemma tssum5_test:"tssum5\<cdot> (Abs_tstream ((<[Msg 1,\<surd>,Msg 2,\<surd>,\<surd>,Msg 4]>) \<bullet> (sinftimes(\<up>\<surd>))))
 =(Abs_tstream ((<[Msg 1,\<surd>,Msg 3,\<surd>,\<surd>,Msg 7]>) \<bullet> (sinftimes(\<up>\<surd>))))"
apply simp+
sorry


lemma chain_tsh: "chain tsh"
apply (rule chainI)
apply (subst fun_below_iff)+
apply (induct_tac i, auto)
apply (erule_tac x="x" in allE)
sorry

(* monotonicity of h *)
lemma mono_tsh: 
  "\<forall> x y q. x \<sqsubseteq> y \<longrightarrow> tsh n q x \<sqsubseteq> tsh n q y"
apply (induct_tac n, auto)
apply (drule lessD, erule disjE, simp)
apply (erule exE)+
apply (erule conjE)+
apply auto
sorry

(* tssum5 is cont*)
lemma cont_lub_tssum5_helper: "cont (\<lambda> ts. Abs_tstream (\<Squnion>i. tsh i p (Rep_tstream ts)))"
sorry

lemma [simp]: "tssum5_helper p\<cdot>\<bottom> = \<bottom>"
apply (simp add: tssum5_helper_def)
apply (subst beta_cfun, rule cont_lub_tssum5_helper)
using tsh_bot by simp

lemma tssum5_helper_scons:"a\<noteq>\<surd> \<and> ts_well ((\<up>a) \<bullet> s) \<Longrightarrow> tssum5_helper n \<cdot>(Abs_tstream((\<up>a) \<bullet> s)) =
 Abs_tstream(\<up>(Msg (shd (tsAbs\<cdot>(Abs_tstream (\<up>a)))+n))) \<bullet> (tssum5_helper ((shd (tsAbs\<cdot>(Abs_tstream (\<up>a))))+n)\<cdot>(Abs_tstream s))"  
apply (simp add: tssum5_helper_def)
apply (subst beta_cfun, rule cont_lub_tssum5_helper)+
apply (subst lub_range_shift [where j="Suc 0", THEN sym])
apply (rule ch2ch_fun, rule ch2ch_fun)
apply (rule chainI)
apply (rule fun_belowD [of _ _ "f"])
apply (smt chain_tsh fun_belowI po_class.chain_def)
sorry

lemma tssum5_one: "tssum5\<cdot> (Abs_tstream(\<up>a)) = Abs_tstream(\<up>a)"
apply (simp add: tssum5_def tssum5_helper_def)
using tsh_def
apply (cases "a=\<surd>")
sorry
*)
end