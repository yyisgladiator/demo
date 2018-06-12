(*  Title:        NewSpfStep
    Author:       Hendrik Kausch
    e-mail:       hendrik.kausch@rwth-aachen.de
*)

theory NewSpfStep
imports SPF
begin
default_sort type

typedef 'm sbElem = "{x :: (channel\<rightharpoonup>'m::message) . sbElemWell x}"
   by(simp add: sbElemWellEx)
  
definition sbHdElemWell::"'m::message SB \<Rightarrow> bool" where
"sbHdElemWell sb = (\<forall>c \<in> ubDom\<cdot>(sb). sb. c \<noteq> \<epsilon>)"  

lemma sbHdElemWell_inv_ex:"sbHdElemWell sb \<Longrightarrow> \<exists>x. convDiscrUp x = (sbHdElem\<cdot>sb)"
  using convdiscrup_inv_eq sbHdElemWell_def sbHdElem_dom sbHdElem_channel by blast

lemma sbHdElemWell_invConvDiscrUp:"sbHdElemWell sb \<Longrightarrow> \<forall>c\<in>ubDom\<cdot>(sb).((inv convDiscrUp) (sbHdElem\<cdot>sb)) \<rightharpoonup> c = inv Discr (inv Iup ((sbHdElem\<cdot>sb) \<rightharpoonup> c))"
  by (simp add: convDiscrUp_inv_subst sbHdElemWell_def sbHdElem_channel)
     
(* updis bijectiv *)
thm inv_def
(* Returns the SPF that switches depending on input.  (spfStep_h1 In Out\<cdot>h)\<cdot>(sbHdElem\<cdot>sb) computes the SPF which has to be applied to the input sb*)
definition spfStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF" where
"spfStep In Out \<equiv> \<Lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In \<and> sbHdElemWell sb) 
                                              \<leadsto> (ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb)))"


lemma spfStep_innerCont:"cont (\<lambda>  sb.  (ubDom\<cdot>sb = In \<and> sbHdElemWell sb) 
                                              \<leadsto> (ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb)))"
  sorry

lemma spfStep_innerWell:"ufWell (\<Lambda>  sb.  (ubDom\<cdot>sb = In \<and> sbHdElemWell sb) 
                                              \<leadsto> (ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb))) "
  sorry



lemma spfStep_cont:"cont (\<lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In \<and> sbHdElemWell sb) 
                                              \<leadsto> (ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb))))"
  sorry

lemma [simp]:"inj (\<lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In \<and> sbHdElemWell sb) 
                                              \<leadsto> (ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb))))" (*h must map to spf with dom = In and Range = Out and not map to ufLeast In Out*)
proof(rule injI)
  fix x y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
  assume a1:" Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb) =
              Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb)"
  then have "\<forall>insb. Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb) \<rightleftharpoons> insb =
              Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb) \<rightleftharpoons> insb"
    by simp
  then have a2:"\<forall> insb. (\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb) insb =
           (\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb) insb"
    apply(simp add: spfStep_innerWell spfStep_innerCont)
    by (smt ufRestrict_dom ufapplyin_eq_pre)
  have "(\<forall>elem. (x elem) \<noteq> ufLeast In Out \<and> ufDom\<cdot>(x elem) = In \<and> ufRan\<cdot>(x elem) = Out)"
    sorry
  then have "(\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb) =
             (\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb)"
    by auto
  moreover have "(\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb) =
                 (\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb)"
    sorry
  ultimately have "(\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb) = 
                   (\<lambda>sb. (ubDom\<cdot>sb = In \<and> sbHdElemWell sb)\<leadsto>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb)"
    sorry
  then show "x = y"
    sorry
qed

lemma spfStep_inj:"inj (Rep_cfun(spfStep In Out))"  
  by(simp add: spfStep_def spfStep_cont)

lemma spfstep_insert: "spfStep In Out\<cdot>h= Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In \<and> sbHdElemWell sb) 
                                              \<leadsto> (ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb)))"
  by(simp add: spfStep_def spfStep_cont)

lemma spfstep_dom[simp]:s"ufDom\<cdot>(spfStep cIn cOut\<cdot>f) = cIn"
  oops
    
lemma spfstep_ran [simp]:"ufRan\<cdot>(spfStep cIn cOut\<cdot>f) = cOut"
  oops 
    
lemma spfstep_step: assumes "ubDom\<cdot>sb = In" and "\<forall>c\<in>In. sb . c \<noteq> \<bottom>"  shows "spfStep In Out\<cdot>f\<rightleftharpoons>sb = (f (Abs_sbElem(inv convDiscrUp(sbHdElem\<cdot>sb))))\<rightleftharpoons>(sbRt\<cdot>sb)"
  oops

end