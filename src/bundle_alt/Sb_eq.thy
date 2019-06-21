theory Sb_eq

imports SBv3 sbElemv3

begin


definition sbeq_well :: "('c::chan \<Rightarrow> M stream) \<Rightarrow> bool" where
"sbeq_well f = (\<forall>c d. #(f c) = #(f d)) "

lemma sb_ex:"sbeq_well (\<lambda>c. \<epsilon>)"
  by(simp add: sbeq_well_def sValues_def)

pcpodef 'c::chan sbeq("(_\<^sup>\<Omega>\<^sup>=)" [1000] 999) = "{sb::'c\<^sup>\<Omega>. sbeq_well (Rep_sb sb)}"
   apply auto
   apply (simp add: Rep_sb_strict sbeq_well_def) 
  apply(simp add: sbeq_well_def)
  apply(rule adm_all)+
  apply(rule adm_eq)
   apply(rule cont2cont,simp_all)
   apply(rule Cont.contI2)
  apply(rule monofunI)
  apply (simp add: below_sb_def fun_belowD)
   apply(subst cont2contlubE[of Rep_sb]) 
  using cont_Rep_sb cont_id apply blast
  apply simp
   apply (simp add: below_sb_def lub_fun po_class.chain_def)
   apply(rule cont2cont,simp_all)
   apply(rule Cont.contI2)
  apply(rule monofunI)
  apply (simp add: below_sb_def fun_belowD)
   apply(subst cont2contlubE[of Rep_sb]) 
  using cont_Rep_sb cont_id apply blast
  apply simp
  by (simp add: below_sb_def lub_fun po_class.chain_def)


lift_definition sbeq2fun::"'cs sbeq \<rightarrow> ('cs \<Rightarrow> M stream)" is
"(\<lambda>sb. Rep_sb(Rep_sbeq sb))"
  apply(simp add: cfun_def)
  using cfun_def cont_Rep_sbeq cont_Rep_sb cont_id by blast

lemma[simp]:"\<forall>(c::'a) d::'a. #(Rep_sb (Rep_sbeq sbeq) c) = #(Rep_sb (Rep_sbeq sbeq) d)"
  using Rep_sbeq sbeq_well_def by auto

lemma [simp]:"(\<forall>c d. #((sbeq2fun\<cdot>sbeq) c) = #((sbeq2fun\<cdot>sbeq) d))"
  by(simp add: sbeq2fun.rep_eq)

lemma "sbeq\<noteq>\<bottom> \<Longrightarrow> \<forall>c. #((sbeq2fun\<cdot>sb) c)\<noteq> \<bottom>"
  apply(rule allI)
  oops

lift_definition sbeqLen_alt::"'cs sbeq \<rightarrow> lnat" is
"(\<lambda>sb. if range(Rep::'cs\<Rightarrow> channel)\<subseteq>cEmpty then \<infinity> else #((sbeq2fun\<cdot>sb) (SOME c. True)))"
  by(simp add: cfun_def)

definition isRealBot::"'cs sbeq \<Rightarrow> bool" where
"isRealBot sb \<equiv> ((sb=\<bottom>) \<and> (\<forall>c::'cs. (ctype (Rep c))\<noteq>{}))"

lemma isrealbotonechange[simp]:"x\<sqsubseteq>y \<Longrightarrow> isRealBot y \<Longrightarrow> isRealBot x"
  by(simp add: isRealBot_def)

lemma isrealbot_not_mono[simp]:"x\<sqsubseteq>y \<Longrightarrow> \<not>(isRealBot x) \<Longrightarrow> \<not>(isRealBot y)"
  by auto

lift_definition sbeq2sb::"'c\<^sup>\<Omega>\<^sup>= \<rightarrow> 'c\<^sup>\<Omega>" is  "Rep_sbeq"
  using cfun_def cont_Rep_sbeq cont_id by blast

lift_definition sbeqGetCh::"'e \<Rightarrow> 'c\<^sup>\<Omega>\<^sup>= \<rightarrow> M stream" is
"\<lambda> e sb. (sbeq2sb\<cdot>sb)\<^enum> e"
  by(simp add: cfun_def)

lemma sb2sbeq_well[simp]:"sbeq_well (Rep_sb(sbTake (sbLen sb)\<cdot>sb))"
  apply(auto simp add: sbeq_well_def)
  by (metis sbgetch_insert2 sbtake_len)


lemma monofun_sb2sbeq:"monofun (\<lambda>a::'a\<^sup>\<Omega>. sbTake (sbLen a)\<cdot>a)"
proof(rule monofunI)
  fix x y::"'a\<^sup>\<Omega>"
  assume a1:"x \<sqsubseteq> y"
  show "sbTake (sbLen x)\<cdot>x \<sqsubseteq> sbTake (sbLen y)\<cdot>y"
  apply(simp add: sbTake.rep_eq)
  apply(case_tac "sbLen x = \<infinity>")
  apply simp
  using a1 sblen_mono apply fastforce
  apply(subgoal_tac "\<exists>n. sbLen x = Fin n")
  apply auto
  apply(case_tac "sbLen y = \<infinity>")
  apply simp
  apply(simp add: sbMapStream_def)
  apply(simp add: below_sb_def)
  apply(subst Abs_sb_inverse)
  apply simp
  apply(simp add: sbgetch_insert2)
  apply (meson a1 below_sb_def fun_belowI rev_below_trans stream.take_below)
  apply (subgoal_tac "\<exists>m. sbLen y = Fin m \<and> n \<le> m")
  apply auto
  apply(simp add: sbMapStream_def)
  apply(simp add: below_sb_def)
  apply(simp add: Abs_sb_inverse)
  apply(simp add: sbgetch_insert2)
  apply(rule fun_belowI)
  apply (metis a1 below_sb_def cfun_belowI fun_belowD monofun_cfun stake_mono)
  apply (metis a1 antisym_conv1 inf_ub less2nat_lemma lnat_well_h2 lnle_conv sblen_mono)
  using SBv3.lnat.exhaust by auto
qed

lemma sb2sbeq_lubwell[simp]:"chain Y \<Longrightarrow> chain (\<lambda>i::nat. Abs_sbeq (sbTake (sbLen (Y i))\<cdot>(Y i))) \<Longrightarrow>
                            sbeq_well (Rep_sb (\<Squnion>i::nat. sbTake (sbLen (Y i))\<cdot>(Y i)))"
proof(auto simp add: sbeq_well_def)
  fix c d::'a
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. Abs_sbeq (sbTake (sbLen (Y i))\<cdot>(Y i)))"
  then have "#((\<Squnion>i::nat. sbTake (sbLen (Y i))\<cdot>(Y i) ) \<^enum> c) = #((\<Squnion>i::nat. sbTake (sbLen (Y i))\<cdot>(Y i) ) \<^enum> d)"
  apply(subst contlub_cfun_arg)
  apply(rule chainI)
  apply(subgoal_tac "Y i \<sqsubseteq> Y (Suc i)")
  apply(rule monofunE,simp_all)
  apply (simp add: monofun_sb2sbeq)
  using a1 po_class.chain_def apply auto[1]
  apply(subst contlub_cfun_arg)
  apply(rule chainI)
   apply(subgoal_tac "Y i \<sqsubseteq> Y (Suc i)")
    apply(subgoal_tac "sbTake (sbLen (Y i))\<cdot>(Y i) \<sqsubseteq> sbTake (sbLen (Y (Suc i)))\<cdot>(Y (Suc i))")
     apply (simp add: monofun_cfun_arg)
  apply(subst monofunE[of "\<lambda>a::'a\<^sup>\<Omega>. sbTake (sbLen a)\<cdot>a"],auto)
  apply (simp add: monofun_sb2sbeq)
  using a1 po_class.chain_def apply auto[1]
apply(subst contlub_cfun_arg)
  apply(rule chainI)
  apply(subgoal_tac "Y i \<sqsubseteq> Y (Suc i)")
  apply(rule monofunE,simp_all)
  apply (simp add: monofun_sb2sbeq)
  using a1 po_class.chain_def apply auto[1]
  apply(subst contlub_cfun_arg)
  apply(rule chainI)
   apply(subgoal_tac "Y i \<sqsubseteq> Y (Suc i)")
    apply(subgoal_tac "sbTake (sbLen (Y i))\<cdot>(Y i) \<sqsubseteq> sbTake (sbLen (Y (Suc i)))\<cdot>(Y (Suc i))")
     apply (simp add: monofun_cfun_arg)
  apply(subst monofunE[of "\<lambda>a::'a\<^sup>\<Omega>. sbTake (sbLen a)\<cdot>a"],auto)
  apply (simp add: monofun_sb2sbeq)
  using a1 po_class.chain_def by auto[1]
  then show "#(Rep_sb (\<Squnion>i::nat. sbTake (sbLen (Y i))\<cdot>(Y i)) c) = #(Rep_sb (\<Squnion>i::nat. sbTake (sbLen (Y i))\<cdot>(Y i)) d)"
    by (simp add: sbgetch_insert2)
qed

lemma sbtake_cont[simp]:"cont sbTake"
  apply(rule Cont.contI2)
  apply simp
  apply(rule cfun_belowI)
  apply(simp add: sbTake.rep_eq)
  oops

definition sb2sbeq::"'c\<^sup>\<Omega> \<rightarrow> 'c\<^sup>\<Omega>\<^sup>=" where
"sb2sbeq \<equiv> \<Lambda> sb. Abs_sbeq(sbTake(sbLen sb)\<cdot>sb)" (* zu lange sachen abschneiden *)

lemma assumes "adm (\<lambda>sb::'b\<^sup>\<Omega>. sbLen sb = k)" shows "cont (\<lambda> sb::'b\<^sup>\<Omega>. Abs_sbeq(sbTake(sbLen sb)\<cdot>sb))"
  apply(rule Cont.contI2)
  apply(rule monofunI)
  apply(simp add: below_sbeq_def Abs_sbeq_inverse)
  apply(simp add: below_sb_def)
  apply(rule fun_belowI)
  apply(simp add: sbTake.rep_eq)
  apply(case_tac "sbLen x= \<infinity>")
  apply simp
  apply (metis below_sb_def fun_belowD inf_less_eq lnat.simps(5) lnle_def sblen_mono)
  apply(subgoal_tac "\<exists>n. sbLen x = Fin n")
  apply auto
  apply(case_tac "sbLen y= \<infinity>")
  apply simp
  apply(simp add: Abs_sb_inverse sbMapStream_def)
  apply (metis fun_belowD rev_below_trans sbgetch_insert2 stream.take_below)
  apply(subgoal_tac "\<exists>m. sbLen y = Fin m")
  apply auto
  apply(simp add: Abs_sb_inverse sbMapStream_def)
  apply(subgoal_tac "n \<le> m")
  apply auto
  apply (simp add: cfun_belowI fun_belowD monofun_cfun sbgetch_insert2 stake_mono)
  apply (metis below_sb_def less2nat lnle_def sblen_mono)
  using lncases apply auto[1]
  using lncases apply auto[1]
  apply(simp add: below_sbeq_def Abs_sbeq_inverse)
  apply(simp add:  lub_sbeq)
  apply(simp add: Abs_sbeq_inverse)
  apply(subgoal_tac "adm (\<lambda>sb::'b\<^sup>\<Omega>. sbLen sb = k) \<Longrightarrow> cont (\<lambda>sb::'b\<^sup>\<Omega>. sbTake (sbLen sb)\<cdot>sb)")
  apply(subst cont2contlubE[of "(\<lambda> sb. sbTake (sbLen sb)\<cdot>sb)"])
  apply (simp_all add: assms)
  apply(insert assms)
  apply(rule Cont.contI2)
  apply (simp add: monofun_sb2sbeq)
proof-
  fix Ya::"nat \<Rightarrow> 'b\<^sup>\<Omega>"
  assume adm:"adm (\<lambda>sb::'b\<^sup>\<Omega>. sbLen sb = k)"
  assume ch1:"chain Ya"
  assume ch2:"chain (\<lambda>i::nat. sbTake (sbLen (Ya i))\<cdot>(Ya i))"
  show "sbTake (sbLen (\<Squnion>i::nat. Ya i))\<cdot>(\<Squnion>i::nat. Ya i) \<sqsubseteq> (\<Squnion>i::nat. sbTake (sbLen (Ya i))\<cdot>(Ya i))"
    apply(subst lub_APP,simp_all add: ch1 ch2)
    apply(rule chainI)
    defer
    apply(subgoal_tac "sbLen (Lub Ya) = (\<Squnion>i. sbLen (Ya i))",simp)
    apply(subgoal_tac "sbTake (\<Squnion>i::nat. sbLen (Ya i))\<cdot>(Lub Ya) = (\<Squnion>i::nat. sbTake ( sbLen (Ya i)))\<cdot>(Lub Ya)")
    apply simp_all
    defer
    sorry
qed



(* TODO: 
  Some wellformed condition over "k" ... then prove "cont"
  sbeq not cont 
*)
definition sbeqSB::  "('cs sb \<rightarrow> 'as sb) \<Rightarrow> ('cs sbeq \<rightarrow> 'as sbeq)" where
"sbeqSB k = (\<Lambda> sbeq. sb2sbeq\<cdot>(k\<cdot>(sbeq2sb\<cdot>sbeq)))"

lift_definition sbeqRestrict::"'c\<^sup>\<Omega>\<^sup>= \<rightarrow> 'e\<^sup>\<Omega>\<^sup>="is
"\<lambda>sb. sb2sbeq\<cdot>((sbeq2sb\<cdot>sb)\<star>)"
  by(simp add: cfun_def)

definition sbeqUnion::"'c\<^sup>\<Omega>\<^sup>= \<rightarrow> 'd\<^sup>\<Omega>\<^sup>= \<rightarrow> 'e\<^sup>\<Omega>\<^sup>=" where
"sbeqUnion = (\<Lambda> sb1 sb2. sb2sbeq\<cdot>((sbeq2sb\<cdot>sb1)\<uplus>(sbeq2sb\<cdot>sb2)))"
  
(* Automaten Semantik: 'c\<^sup>\<Omega>\<^sup>= \<rightarrow> 'c\<^sup>\<Omega> *)

definition sbeqECons::"'c\<^sup>\<surd> \<rightarrow> 'c\<^sup>\<Omega>\<^sup>= \<rightarrow> 'c\<^sup>\<Omega>\<^sup>=" where
"sbeqECons = (\<Lambda> sbe sb. sb2sbeq\<cdot>(sbECons\<cdot>sbe\<cdot>(sbeq2sb\<cdot>sb)))"

lemma sbeqECons_insert:"sbeqECons\<cdot>sbe\<cdot>sb = sb2sbeq\<cdot>(sbECons\<cdot>sbe\<cdot>(sbeq2sb\<cdot>sb))"
  by(simp add: sbeqECons_def)

(* TODO: "sb\<noteq>\<bottom>" ersetzen durch: "\<not>domain \<subseteq> cEmpty" *)
lemma sbeqecons_notbot[simp]:"sb \<noteq> \<bottom> \<Longrightarrow> sbeqECons\<cdot>sbe\<cdot>sb \<noteq> \<bottom>"
  sorry

lemma sbeq_notctypebot[simp]:"(sb::'a\<^sup>\<Omega>\<^sup>=) \<noteq> \<bottom> \<Longrightarrow> range (Rep::'a\<Rightarrow>channel) \<inter> cEmpty = {}"
proof-
  assume a1:"sb \<noteq> \<bottom>"
  then have "(Rep_sbeq sb) \<noteq> \<bottom>"
    by (simp add: Rep_sbeq_bottom_iff)
  then have"\<forall>c::'a. sbeqGetCh c\<cdot>sb \<noteq> \<epsilon>"
    apply(simp add: sbeqGetCh.rep_eq sbeq2sb.rep_eq)
    sorry
  then show ?thesis
  sorry
qed

lift_definition sbHdElem_h::"('c\<^sup>\<Omega>\<^sup>=) \<rightarrow> ('c\<^sup>\<surd>) u"is (*muss noch anders definiert werden für cEmpty*)
"(\<lambda> sb. if (range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty) then Iup(Abs_sbElem None) else 
        if sb = \<bottom> then \<bottom> else Iup(Abs_sbElem (Some (\<lambda>c. shd((sbeq2sb\<cdot>sb) \<^enum> c)))))"
  apply(simp add: cfun_def)
  apply(rule Cont.contI2)
  sorry

definition sbHdElem::"('c)\<^sup>\<Omega>\<^sup>= \<Rightarrow> 'c\<^sup>\<surd>"where
"sbHdElem = (\<lambda> sb. case (sbHdElem_h\<cdot>sb) of Iup sbElem \<Rightarrow> sbElem | _ \<Rightarrow> undefined)"

lemma sbhdelem_notbot[simp]:"sb\<noteq>\<bottom> \<Longrightarrow> sbHdElem sb \<noteq> Abs_sbElem(None)"
  sorry

lemma sbhdelem_none[simp]:"(range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty) \<Longrightarrow> sbHdElem((x::('c)\<^sup>\<Omega>\<^sup>=)) = Abs_sbElem(None)"
  by(simp add: sbHdElem_def sbHdElem_h.rep_eq)

lemma sbhdelem_some:"(\<not>(range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty) \<and> x\<noteq>\<bottom>) \<Longrightarrow> sbHdElem((x::('c)\<^sup>\<Omega>\<^sup>=)) = Abs_sbElem(Some(\<lambda>c. shd((sbeq2sb\<cdot>x) \<^enum> c)))"
  by(simp add: sbHdElem_def sbHdElem_h.rep_eq)

lemma sbhdelem_mono_empty[simp]:"((range(Rep::'c\<Rightarrow> channel)\<subseteq>cEmpty)) \<Longrightarrow> (x::('c)\<^sup>\<Omega>\<^sup>=) \<sqsubseteq> y \<Longrightarrow> sbHdElem x = sbHdElem y"
  by(simp)

lemma sbhdelem_mono[simp]:"x \<noteq> \<bottom> \<Longrightarrow>  x \<sqsubseteq> y \<Longrightarrow> sbHdElem x = sbHdElem y"
  apply(cases "(range(Rep::'a\<Rightarrow> channel)\<subseteq>cEmpty)")
  apply simp
proof-
  assume a1:" x\<noteq> \<bottom>"
  assume a2:"x \<sqsubseteq> y"
  assume a3:"\<not> range Rep \<subseteq> cEmpty"
  then have "y\<noteq> \<bottom>"
    using a1 a2  by auto
  then have h1:"\<And>c::'a. shd (sbeq2sb\<cdot>x  \<^enum>  c) = shd (sbeq2sb\<cdot>y  \<^enum>  c)"
    sorry
  then show ?thesis
    apply(subst sbhdelem_some)
    using a1 sbeq_notctypebot apply fastforce
    apply(subst sbhdelem_some) 
    using \<open>(y::'a\<^sup>\<Omega>\<^sup>=) \<noteq> \<bottom>\<close> sbeq_notctypebot apply fastforce
    by(simp add: h1)
qed

lift_definition sbeqDrop :: "nat \<Rightarrow> 'c\<^sup>\<Omega>\<^sup>= \<rightarrow> 'c\<^sup>\<Omega>\<^sup>="is 
"(\<lambda>n  sb. sb2sbeq\<cdot>(sbDrop n\<cdot>(sbeq2sb\<cdot>sb)))"
  by(simp add: cfun_def)


abbreviation sbeqRt :: "'c\<^sup>\<Omega>\<^sup>= \<rightarrow> 'c\<^sup>\<Omega>\<^sup>="  where 
"sbeqRt \<equiv> sbeqDrop 1"
(************************************************)
(************************************************)      
    subsection \<open>Fixrec\<close>
(************************************************)
(************************************************)

(* TODO: Besserer Name! *)
definition sbeqSbeFix::"'cs sbeq \<rightarrow> ('cs sbElem \<rightarrow> 'cs sbeq \<rightarrow> 'a::pcpo) \<rightarrow> ('a)" where (*sbHdElem nicht immer definiert*)
"sbeqSbeFix = (\<Lambda> sb k. ((if isRealBot sb then \<bottom> else k\<cdot>(sbHdElem sb)\<cdot>(sbeqRt\<cdot>sb))))"


lemma sbeqsbefix_cont[simp]:"cont (\<lambda>sb::'b\<^sup>\<Omega>\<^sup>=. \<Lambda> (k::'b\<^sup>\<surd> \<rightarrow> 'b\<^sup>\<Omega>\<^sup>= \<rightarrow> 'a::pcpo). if isRealBot sb then \<bottom> else k\<cdot>(sbHdElem sb)\<cdot>(sbeqRt\<cdot>sb))"
  apply(intro cont2cont)
  apply(rule Cont.contI2)
  apply(rule monofunI)
  apply auto[1]
  apply(simp add: isRealBot_def)
  apply auto[1]
  using cfun_below_iff monofun_cfun monofun_cfun_arg apply blast
  apply(subst sbhdelem_mono_empty)
  apply(simp add: cEmpty_def)
  apply (metis (mono_tags, lifting) Int_Collect cEmpty_def chan_botsingle empty_iff range_eqI)
  apply simp
  apply (simp add: monofun_cfun)
  apply(case_tac"isRealBot (fst (\<Squnion>i::nat. Y i))" )
  apply simp 
  sorry

lemma sbeqSbeFix_insert:"sbeqSbeFix\<cdot>sb\<cdot>f = (if isRealBot sb then \<bottom> else (f\<cdot>(sbHdElem sb)\<cdot>(sbeqRt\<cdot>sb)))"
  by(simp add: sbeqSbeFix_def)

definition sbeqLen:: "'cs sbeq \<rightarrow> lnat" where
"sbeqLen = (fix\<cdot>(\<Lambda> h sb. sbeqSbeFix\<cdot>sb\<cdot>(\<Lambda> sbe sb2 . lnsuc\<cdot>(h\<cdot>sb2))))"


lemma [simp]: "\<not>(isRealBot sb) \<Longrightarrow> sbeqSbeFix\<cdot>(sbeqECons\<cdot>sbe\<cdot>sb)\<cdot>k = k\<cdot>sbe\<cdot>sb"
  apply(simp add: sbeqSbeFix_insert)
  sorry

lemma [simp]: "isRealBot sb \<Longrightarrow> sbeqSbeFix\<cdot>sb = \<bottom>"
  by(simp add: sbeqSbeFix_def)


lemma "isRealBot sb \<Longrightarrow> sbeqLen\<cdot>sb = 0"
  apply(subst sbeqLen_def)
  apply(subst fix_eq)
  apply(subst sbeqLen_def[symmetric])
  apply simp
  using bot_is_0 by blast
  
lemma "\<not>(isRealBot sb) \<Longrightarrow> sbeqLen\<cdot>(sbeqECons\<cdot>sbe\<cdot>sb) = lnsuc\<cdot>(sbeqLen\<cdot>sb)"
  apply(subst sbeqLen_def)
  apply(subst fix_eq)
  apply(subst sbeqLen_def[symmetric])
  by simp


(*
 FIXREC sachen sind erstmal egal, da die immer strict sind. 
    "sbLen" soll aber nicht strict sein...

definition (* Todo: Wichtig, muss cont sein *)
  match_sb_sbecons :: "'cs sbeq \<rightarrow> ('cs sbElem\<rightarrow> 'cs sbeq \<rightarrow> ('b ::cpo) match) \<rightarrow> 'b match" where
  "match_sb_sbecons = (\<Lambda> xs k. if xs = \<bottom> then Fixrec.fail else k\<cdot>(sbHdElem xs)\<cdot>(sbeqRt\<cdot>xs))"

lemma"cont(\<lambda>k. if xs=\<bottom> then \<bottom> else k\<cdot>(sbHdElem xs)\<cdot>(sbeqRt\<cdot>xs))"
  by simp

(*lub chain proofs*)
lemma lubchain_below_lub:"chain (Y1::nat \<Rightarrow> 'a::cpo) \<Longrightarrow> chain Y2 \<Longrightarrow> \<forall> i\<ge>n. Y1 i = Y2 i \<Longrightarrow> (\<Squnion>i. Y2 i) \<sqsubseteq> (\<Squnion>i. Y1 i)"
  by (metis (full_types) below_lub linear lub_below_iff po_class.chain_mono)

lemma lubeqlubchain:"chain (Y1::nat \<Rightarrow> 'a::cpo) \<Longrightarrow> chain Y2 \<Longrightarrow> \<forall> i\<ge>n. Y1 i = Y2 i \<Longrightarrow> (\<Squnion>i. Y1 i) = (\<Squnion>i. Y2 i)"
  by (metis (mono_tags) lubchain_below_lub po_eq_conv)

(*A version of if then else cont, but to hard*)
lemma cont_if2 [simp]: "(\<And>x. P x \<longrightarrow> cont f) \<Longrightarrow> (\<And>x. \<not>(P x) \<longrightarrow> cont g) 
                        \<Longrightarrow> (\<And> x. f x \<sqsubseteq> g x) \<Longrightarrow>(\<And> x y. x\<sqsubseteq> y \<Longrightarrow> P (y) \<Longrightarrow> P x) \<Longrightarrow> adm P 
                        \<Longrightarrow> cont (\<lambda>x. if P(x) then f x else g x)"
  apply(rule Cont.contI2)
  apply(rule monofunI)
  apply auto[1]
  apply (simp add: cont2monofunE)
  apply (meson cont2mono monofun_def rev_below_trans)
  apply (simp add: cont2monofunE)
  apply(case_tac "P (\<Squnion>i::nat. Y i)")
  apply (smt contE is_lub_below_iff lub_below_iff po_eq_conv ub_rangeI)
proof-
  fix Y::"nat \<Rightarrow> 'a"
  assume cont1:"(\<And>x::'a. P x \<longrightarrow> cont f)"
  assume cont2:"(\<And>x::'a. \<not> P x \<longrightarrow> cont g)"
  assume belowf:"(\<And>x::'a. f x \<sqsubseteq> g x)"
  assume P1change:"(\<And>(x::'a) y::'a. x \<sqsubseteq> y \<Longrightarrow> P y \<Longrightarrow> P x)"
  assume amdP:"adm P"
  assume chain1:"chain Y"
  assume chain2:"chain (\<lambda>i::nat. if P (Y i) then f (Y i) else g (Y i))"
  assume notlubP:"\<not> P (\<Squnion>i::nat. Y i)"
  then have chaing:"chain (\<lambda>i. g( Y i))"
    using ch2ch_cont chain1 cont2 by blast
  then obtain i where i_def:"\<not>P (Y i)"
    using admD amdP chain1 notlubP by auto
  then have "\<forall>n\<ge>i. \<not>P (Y n)"
    using P1change chain1 po_class.chain_mono by blast
  then have "\<forall>n\<ge>i.( if P (Y n) then f (Y n) else g (Y n)) = ( g (Y n))"
    by simp
  then have h1:"(\<Squnion>i::nat. if P (Y i) then f (Y i) else g (Y i)) = (\<Squnion>i::nat. g (Y i)) "
    using chain2 chaing lubeqlubchain by blast
  then show "(if P (\<Squnion>i::nat. Y i) then f (\<Squnion>i::nat. Y i) else g (\<Squnion>i::nat. Y i)) \<sqsubseteq> (\<Squnion>i::nat. if P (Y i) then f (Y i) else g (Y i))"
    using chain1 cont2 cont2contlubE notlubP by fastforce
qed


lemma contlub_if2 [simp]: "chain (Y::nat\<Rightarrow> 'a::cpo) \<Longrightarrow> adm P  \<Longrightarrow> (\<And> x. f x \<sqsubseteq> g x) \<Longrightarrow>(\<And> x y. x\<sqsubseteq> y \<Longrightarrow> P (y) \<Longrightarrow> P x)
                        \<Longrightarrow> ( P (\<Squnion>i::nat. Y i) \<Longrightarrow> f (\<Squnion>i::nat. Y i) = (\<Squnion>i. f ( Y i)))
                        \<Longrightarrow>( \<not>P (\<Squnion>i::nat. Y i) \<Longrightarrow> g (\<Squnion>i::nat. Y i) = (\<Squnion>i. g ( Y i)))
                        \<Longrightarrow> chain (\<lambda>i. if P (Y i) then f (Y i) else g( Y i))
                        \<Longrightarrow>(if P (\<Squnion>i::nat. Y i) then f (\<Squnion>i::nat. Y i) else g (\<Squnion>i::nat. Y i)) \<sqsubseteq> (\<Squnion>i::nat. if P (Y i) then f (Y i) else g (Y i))"
proof-
  assume chainY:"chain Y"
  assume admP:"adm P"
  assume fbelow:"(\<And>x::'a. f x \<sqsubseteq> g x)"
  assume ponechange:"(\<And>(x::'a) y::'a. x \<sqsubseteq> y \<Longrightarrow> P y \<Longrightarrow> P x)"
  assume flub_well:"(P (\<Squnion>i::nat. Y i) \<Longrightarrow> f (\<Squnion>i::nat. Y i) = (\<Squnion>i::nat. f (Y i)))"
  assume glub_well:"(\<not> P (\<Squnion>i::nat. Y i) \<Longrightarrow> g (\<Squnion>i::nat. Y i) = (\<Squnion>i::nat. g (Y i)))"
  assume chain2:"chain (\<lambda>i. if P (Y i) then f (Y i) else g( Y i))"
  then obtain somen where somen_def:"P (\<Squnion>i::nat. Y i) = P (Y somen)"
    by (metis (no_types, lifting) admD admD2 admP adm_upward chainY ponechange)
  show"(if P (\<Squnion>i::nat. Y i) then f (\<Squnion>i::nat. Y i) else g (\<Squnion>i::nat. Y i)) \<sqsubseteq> (\<Squnion>i::nat. if P (Y i) then f (Y i) else g (Y i))"
  proof(cases "P (\<Squnion>i::nat. Y i)")
    case True
    then show ?thesis
      by (smt True chainY flub_well image_cong is_ub_thelub po_eq_conv ponechange)
  next
    case False
    then obtain n where n_def:"\<not> P(Y n)"
      using admD admP chainY by auto
    then have "\<forall>i\<ge>n. (\<not> P (Y n))"
      using ponechange chainY po_class.chain_mono by blast
    then have "\<forall>i\<ge>n. (if P (Y i) then f (Y i) else g (Y i)) = (if P (Y n) then f (Y i) else g (Y i))"
      by (meson chainY po_class.chain_mono ponechange)
    then have h1:"(\<Squnion>i::nat. if P (Y i) then f (Y i) else g (Y i)) = (\<Squnion>i::nat. if P (Y n) then f (Y i) else g (Y i))"
      sorry
    then show ?thesis
      by (simp add: False glub_well n_def)
  qed
qed

lemma match_sb_sbecons_cont[simp]:"cont (\<lambda> xs. \<Lambda> k. if xs=\<bottom> then \<bottom> else k\<cdot>(sbHdElem xs)\<cdot>(sbeqRt\<cdot>xs))"
  apply(rule cont2cont)
  apply(rule Cont.contI2)
  defer
  apply(rule contlub_if2,auto)
  sorry




(* TODO: cont-beweisen *)  
(* Danach die match-lemmata anpassen:  *)
lemma match_sbeq_simps [simp]:
  "match_sb_sbecons\<cdot>\<bottom>\<cdot>k = \<bottom>"
  "sb \<noteq>\<bottom> \<Longrightarrow> match_sb_sbecons\<cdot>(sbeqECons\<cdot>sbe\<cdot>sb)\<cdot>k = k\<cdot>(sbe)\<cdot>(sb)" (*Da sb\<noteq> \<bottom> \<Longrightarrow> \<forall>c\<in>range(Rep::'a \<Rightarrow> channel) . ctype \<noteq> {} \<Longrightarrow> sbe \<noteq> None, deswegen keine weiteren Fälle benötigt*)
  sorry

setup \<open>
  Fixrec.add_matchers
    [ (@{const_name sbeqECons},  @{const_name match_sb_sbecons})
    (* , (@{const_name ID},  @{const_name match_sb_empty}) *)
    ]
\<close>


text \<open>sbLen wird aktuell für die fixrec-matcher verwendet, das kann man ohne Problem durch ein
      Prädikat "sbIsEmpty" ersetzen\<close>


(* Bottom-Regel wird automatisch erstellt. Klappt aber nur mit "fixrec_simp" und nicht einfach "simp" *)
*)


text \<open>Einfache "Case"-Regel für Bündel\<close>
lemma sbeq_cases [case_names empty sbeCons, cases type: sbeq]: 
  shows "(isRealBot sb'\<Longrightarrow> P) \<Longrightarrow> (\<And>sbe sb. sb' = sbeqECons\<cdot>sbe\<cdot>sb \<Longrightarrow> P) \<Longrightarrow> P"
  sorry (* TODO: andere "cases" regel mit normalem "\<bottom>"-Fall *)

(* Demo: *)
lemma "(a::('cs sbeq)) = b"
proof(cases a)
  case empty
  then show ?thesis sorry
next
  case (sbeCons sbe sb)
  then show ?thesis oops



text \<open>Einfache "Induktion"-Regel für Bündel\<close>
lemma sb_induct [case_names empty adm sbeCons, induct type: sbeq]: 
  assumes "P \<bottom>" (* SWS: Ich glaube "isRealBot" ist nicht anwendbar... würde mich aber gerne irren *)
        and "adm P"
        and     "\<And>sbe sb. P sb \<Longrightarrow> P (sbeqECons\<cdot>sbe\<cdot>sb)"  (* TODO: nicht die domain cEmpty *)
      shows "P sb"
  sorry

(* Demo: *)
lemma "(a::('cs sbeq)) = b"
proof(induction a)
  case empty
  then show ?case sorry
next
  case adm
  then show ?case sorry
next
  case (sbeCons sbe a)
  then show ?case oops




end