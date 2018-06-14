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
    
lemma sbHdElem_eq:"\<forall>c\<in>(ubDom\<cdot>sb1). sb1. c \<noteq>\<epsilon> \<Longrightarrow> sb1\<sqsubseteq>sb2 \<Longrightarrow> sbHdElem\<cdot>sb1 = sbHdElem\<cdot>sb2"
proof
  fix x::channel
  assume a1:"\<forall>c\<in>(ubDom\<cdot>sb1). sb1. c \<noteq>\<epsilon>"
  assume a2:"sb1\<sqsubseteq>sb2"
  have a3:"ubDom\<cdot>sb1 = ubDom\<cdot>sb2"
    using a2 ubdom_below by auto
  show "(sbHdElem\<cdot>sb1) x = (sbHdElem\<cdot>sb2) x"
    apply(simp add:sbHdElem_def sbHdElem_cont a3)
    using a1 a2 a3 lshd_eq ubgetch_below by blast
qed
  
     
(* updis bijectiv *)
thm inv_def
(* Returns the SPF that switches depending on input.  (spfStep_h1 In Out\<cdot>h)\<cdot>(sbHdElem\<cdot>sb) computes the SPF which has to be applied to the input sb*)
definition spfStep :: "channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPF) \<rightarrow> 'm SPF" where
"spfStep In Out \<equiv> \<Lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In) 
                                              \<leadsto> (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb) else ubclLeast Out))"


lemma spfStep_innerMono:"monofun (\<lambda>  sb.  (ubDom\<cdot>sb = In) 
                                              \<leadsto> (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb) else ubclLeast Out))"
proof(rule monofunI)
  fix x y::"'a stream\<^sup>\<Omega>"
  assume a1:"x\<sqsubseteq>y"
  have a2:"(ubDom\<cdot>x = In \<and> sbHdElemWell x) \<Longrightarrow> (ubDom\<cdot>y = In \<and> sbHdElemWell y)"
    by (metis a1 below_bottom_iff sbHdElemWell_def ubdom_below ubgetch_below)
  show "(ubDom\<cdot>x = In)\<leadsto>if sbHdElemWell x then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>x)))) \<rightleftharpoons> sbRt\<cdot>x else ubclLeast Out \<sqsubseteq>
       (ubDom\<cdot>y = In)\<leadsto>if sbHdElemWell y then ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>y)))) \<rightleftharpoons> sbRt\<cdot>y else ubclLeast Out"
  proof(cases "ubDom\<cdot>x = In")
    case True
    then have true_x:"ubDom\<cdot>x = In"
      by simp
    then have true_y:"ubDom\<cdot>y = In"
      using a1 ubdom_below by auto
    then show ?thesis
    proof(cases "sbHdElemWell x")
      case True
      have true_y2:"sbHdElemWell y"
        using True a1 a2 true_y ubdom_below by auto
      have a3:"sbHdElem\<cdot>x = sbHdElem\<cdot>y"
        apply(rule sbHdElem_eq)
        using True sbHdElemWell_def a1 by blast+
      have "(ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>x)))) \<rightleftharpoons> sbRt\<cdot>x) \<sqsubseteq> (ufRestrict In Out\<cdot>(h (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>y)))) \<rightleftharpoons> sbRt\<cdot>y)"
        by (smt a1 a3 below_option_def po_eq_conv spfrt_step ufun_rel_eq)
      then show ?thesis
        by(simp add: True true_x true_y true_y2 some_below)
    next
      case False
      then show ?thesis
        by (smt a1 po_eq_conv sbrt_sbdom some_below ubclDom_ubundle_def ubcldom_least ubdom_below ufRestrict_dom ufRestrict_ran ufran_2_ubcldom2)
    qed
  next
    case False
    then show ?thesis
      using a1 ubdom_below by force
  qed
qed
  

lemma spfStep_innerCont:"cont (\<lambda>  sb.  (ubDom\<cdot>sb = In) 
                                              \<leadsto> (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb) else ubclLeast Out))"
  sorry

lemma spfStep_innerWell:"ufWell (\<Lambda>  sb.  (ubDom\<cdot>sb = In) 
                                              \<leadsto> (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb) else ubclLeast Out)) "
  sorry



lemma spfStep_cont:"cont (\<lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In) 
                                              \<leadsto> (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb) else ubclLeast Out)))"
  sorry

lemma [simp]:"inj_on (\<lambda> h. Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In) 
                                              \<leadsto> (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb) else ubclLeast Out))) {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}" (*h must map to spf with dom = In and Range = Out and not map to ufLeast In Out*)
proof(rule inj_onI)
  fix x y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
  assume ax:"x \<in> {h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. \<forall>m::'a sbElem. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out }"
  assume ay:"y \<in> {h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. \<forall>m::'a sbElem. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}"
  assume a1:" Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>if sbHdElemWell sb then ufRestrict In Out\<cdot>(x (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb else ubclLeast Out) =
       Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>if sbHdElemWell sb then ufRestrict In Out\<cdot>(y (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sbRt\<cdot>sb else ubclLeast Out)"
  have ya:"(\<forall>elem.  ufDom\<cdot>(y elem) = In \<and> ufRan\<cdot>(y elem) = Out)"
    using ay by auto
  show "x = y"
    sorry
qed

lemma spfStep_inj:"inj (Rep_cfun(spfStep In Out))"  
  sorry

lemma spfstep_insert: "spfStep In Out\<cdot>h= Abs_ufun (\<Lambda>  sb.  (ubDom\<cdot>sb = In) 
                                              \<leadsto> (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> (sbRt\<cdot>sb) else ubclLeast Out))"
  by(simp add: spfStep_def spfStep_cont)

lemma spfstep_dom[simp]:s"ufDom\<cdot>(spfStep cIn cOut\<cdot>f) = cIn"
  oops
    
lemma spfstep_ran [simp]:"ufRan\<cdot>(spfStep cIn cOut\<cdot>f) = cOut"
  oops 
    
lemma spfstep_step: assumes "ubDom\<cdot>sb = In" and "\<forall>c\<in>In. sb . c \<noteq> \<bottom>"  shows "spfStep In Out\<cdot>f\<rightleftharpoons>sb = (f (Abs_sbElem(inv convDiscrUp(sbHdElem\<cdot>sb))))\<rightleftharpoons>(sbRt\<cdot>sb)"
  oops

end