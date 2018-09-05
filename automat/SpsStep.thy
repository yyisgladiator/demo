theory SpsStep

(* imports "../USpec" "NewSpfStep" "../USpec_Comp" *)
imports NewSpfStep spec.USpec 

begin

default_sort type
type_synonym 'm SPS = "'m SPF uspec"
  
  
 

lemma lub_in:assumes "chain Y" shows "(\<Squnion>i. ((Y i)::'m set rev, Discr In,Discr Out)) = (\<Squnion>i. Y i, Discr In, Discr Out)"
  by (smt Pair_below_iff assms below_refl fstI is_lub_prod lub_const lub_eq lub_eqI po_class.chain_def sndI)
    
definition spsStep_h::"('m::message sbElem \<Rightarrow> 'm SPS)\<rightarrow> ('m sbElem \<Rightarrow> 'm SPF) set rev"where
"spsStep_h= (\<Lambda> h. setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(h e)))"

definition spsStep_P:: "channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPF)  \<Rightarrow> bool" where
"spsStep_P In Out \<equiv> \<lambda> g. (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)"
(* "spsStep_P In Out \<equiv> \<lambda> g. (\<forall>m. ((dom (Rep_sbElem m) = In ) \<longrightarrow> ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out) 
\<and> ((dom (Rep_sbElem m) \<noteq> In ) \<longrightarrow> (g m) = ufLeast In Out))" *)

definition newSpsStep:: "channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"newSpsStep In Out \<equiv> \<Lambda> H. Abs_uspec ((setrevImage (\<lambda> h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb)  sb)) 
                                      (setrevImage (\<lambda> h. spfStep_inj In Out h) 
                                      (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) 
                                      (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))))),Discr  In, Discr Out)"
(* new spsStep with NewSpfStep (spfStep_inj)*)

definition spsStep_inj :: "channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPS) \<rightarrow> ('m SB \<rightarrow> 'm SPF) set rev" where
"spsStep_inj In Out = (\<Lambda> h. Rev {\<Lambda> sb. spfStep_inj In Out g sb | g. g\<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)})"

definition spsStep_inj2 :: "channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPS) \<rightarrow> 'm SB \<rightarrow> 'm SPF set rev" where
"spsStep_inj2 In Out = (\<Lambda> h sb. if sbHdElemWell sb then Rev {spfStep_inj In Out g sb | g. g\<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)} else uspecRevSet\<cdot>(uspecLeast In Out))"

definition spsStep ::"channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep In Out = (\<Lambda> h. Abs_rev_uspec ((\<lambda>f. Abs_cufun(\<lambda>sb. (Rep_cufun (f\<cdot>sb)) sb)) ` (inv Rev (spsStep_inj In Out\<cdot>h))) In Out)"
(*

definition spsStep ::"channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep In Out = (\<Lambda> h. Abs_rev_uspec ({Abs_ufun(\<Lambda> sb. (ubDom\<cdot>sb = In) \<leadsto>((f\<cdot>sb)\<rightleftharpoons> sb)) | f. f \<in> inv Rev (spsStep_inj In Out\<cdot>h)}) In Out)"
 *)
lemma spsStep_h_mono[simp]:"monofun (\<lambda> h::('m::message sbElem \<Rightarrow> 'm SPS). setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(h e)))"
proof(rule monofunI, simp add: uspecRevSet_def)
  fix x y::"'m sbElem \<Rightarrow> 'm SPS"
  assume a1:"x \<sqsubseteq> y"
  then show "setify\<cdot>(\<lambda>e. fst (Rep_uspec (x e))) \<sqsubseteq> setify\<cdot>(\<lambda>e. fst (Rep_uspec (y e)))"
    by (simp add: below_fun_def fst_monofun monofun_cfun_arg rep_uspec_belowI)
qed
   
lemma spsStep_h_cont[simp]:"cont (\<lambda> h::('m::message sbElem \<Rightarrow> 'm SPS). setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(h e)))"
proof(rule Cont.contI2,simp)
  fix Y::"nat \<Rightarrow> 'm sbElem \<Rightarrow> 'm SPS"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))"
  have a3:"(\<lambda>e. \<Squnion>i. uspecRevSet\<cdot>(Y i e)) =  (\<Squnion>i.(\<lambda>e. uspecRevSet\<cdot>(Y i e)))"
    apply(subst lub_fun,auto)
    by (metis (mono_tags, lifting) a1 cont_pref_eq1I fun_below_iff po_class.chain_def)
  show "setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>((\<Squnion>i::nat. Y i) e)) \<sqsubseteq> (\<Squnion>i. setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))"
    apply(simp add: a1 lub_fun)
    apply (simp add: contlub_cfun_arg a1 ch2ch_fun a3)
    apply(subst contlub_cfun_arg, auto)
    by (metis (mono_tags, lifting) a1 fun_below_iff monofun_cfun_arg po_class.chain_def)
qed
  

lemma spsStep_h_insert:"spsStep_h\<cdot>f = setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(f e))"
  by(simp add: spsStep_h_def)
    
(*NewSpsStep Lemma*)    
    

    
lemma newSpsStep_mono_h:assumes "x \<sqsubseteq> y" shows "setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
     (setrevImage (spfStep_inj In Out) (setrevImage (\<lambda>h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>x)))) \<sqsubseteq>
    setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
     (setrevImage (spfStep_inj In Out) (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>y))))"
proof-
  have "(setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>x)) \<sqsubseteq> (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>y))"
    by (simp add: assms cont_pref_eq1I)
  then have"(setrevImage (\<lambda>h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>x))) \<sqsubseteq> (setrevImage (\<lambda>h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>y)))"
    using image_mono_rev monofunE by blast
  then have "(setrevImage (spfStep_inj In Out) (setrevImage (\<lambda>h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>x)))) \<sqsubseteq> (setrevImage (spfStep_inj In Out) (setrevImage (\<lambda>h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>y))))"
    using image_mono_rev monofunE by blast
  thus ?thesis
    using image_mono_rev monofunE by auto
qed
  
lemma newSpsStep_uspecWell:"uspecWell
        (setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
          (setrevImage (spfStep_inj In Out)
            (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>h)))))
         (Discr In) (Discr Out)"
  apply(rule uspec_wellI2)
proof
  fix f::"('a stream\<^sup>\<Omega>) ufun"
  assume a1:"f \<in> inv Rev (setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
                      (setrevImage (spfStep_inj In Out)
                        (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>h)))))"
  then show"ufclDom\<cdot>f = In"
    apply(simp_all add: spsStep_P_def setrevImage_def setrevFilter_def inv_rev_rev)
    apply(simp add: ufclDom_ufun_def)
    sorry
next
  show "\<forall>f::('a stream\<^sup>\<Omega>) ufun\<in>inv Rev (setrevImage (\<lambda>h::'a stream\<^sup>\<Omega> \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (h sb) sb))
                                      (setrevImage (spfStep_inj In Out)
                                        (setrevImage (\<lambda>(h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>h))))).
       ufclRan\<cdot>f = Out"
  proof
    fix f::"('a stream\<^sup>\<Omega>) ufun"
    assume a1:"f \<in> inv Rev (setrevImage (\<lambda>h::'a stream\<^sup>\<Omega> \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (h sb) sb))
                      (setrevImage (spfStep_inj In Out)
                        (setrevImage (\<lambda>(h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>h)))))"
    then show "ufclRan\<cdot>f = Out"
      apply(simp_all add: spsStep_P_def setrevImage_def setrevFilter_def inv_rev_rev)
      sorry
  qed
qed
  
  
    
lemma newSpsStep_mono:"monofun (\<lambda> H. Abs_uspec ((setrevImage (\<lambda> h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb)  sb)) 
                                      (setrevImage (\<lambda> h. spfStep_inj In Out h) 
                                      (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) 
                                      (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))))),Discr  In, Discr Out))"
proof(rule monofunI)
  fix x y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"x \<sqsubseteq> y"
  show"Abs_uspec
        (setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
          (setrevImage (spfStep_inj In Out)
            (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>x)))),
         Discr In, Discr Out) \<sqsubseteq>
       Abs_uspec
        (setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
          (setrevImage (spfStep_inj In Out)
            (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>y)))),
         Discr In, Discr Out)"
    by(simp add: below_uspec_def newSpsStep_uspecWell newSpsStep_mono_h a1)
qed    
    (*
    
definition setrevImage_inj_on::"('m \<Rightarrow> 'n) \<Rightarrow> 'm set rev \<rightarrow> 'n set rev" where
"setrevImage_inj_on f \<equiv> \<Lambda> S.  if inj_on f (inv Rev S) then Rev (f ` (inv Rev S)) else Rev {}"

lemma image_mono_rev_inj_on: "monofun (\<lambda> S.  if inj_on f (inv Rev S) then Rev (f ` (inv Rev S)) else Rev UNIV)"
  apply (rule monofunI)
  by (simp add: image_mono inv_rev_rev revBelowNeqSubset subset_inj_on)

lemma rev_rule:"inv Rev x \<sqsubseteq> inv Rev y \<Longrightarrow> y \<sqsubseteq> x"
  by (metis below_rev.simps rev_inv_rev) 
        
lemma image_cont_rev_inj_on: "cont (\<lambda> S.  if inj_on f (inv Rev S) then Rev (f ` (inv Rev S)) else Rev UNIV)"
 *)

lemma inj_on_adm_set_rev:"adm (\<lambda>S. inj_on f (inv Rev S))"
  oops




lemma setreImage_lub_inj_on: assumes"chain Y" and "\<forall>i. inj_on f (inv Rev (Y i))" 
  shows "setrevImage f (\<Squnion>i. Y i) = (\<Squnion>i. setrevImage f (Y i))" (*main lemma for cont proof spsStep*)
proof (cases "(\<Squnion>i. Y i) = Rev {}")
  case True
  have "(\<Squnion>i::nat. Rev (f ` inv Rev (Y i))) = Rev (f ` {})"
    apply simp
    apply (rule setrev_lub_emptyI)
     apply (metis (mono_tags, lifting) assms(1) image_mono inv_rev_rev po_class.chainI po_class.chain_def revBelowNeqSubset)
    apply (simp add: inv_rev_rev)
    apply (case_tac "x \<notin> f ` inv Rev (Y 0)")
     apply auto[1]
    apply simp
  proof - 
    fix y::'b
    assume a1: " y \<in> f ` inv Rev (Y (0::nat))"
    obtain x where y_def_1: "y = f x "  and y_def_2: "x \<in> inv Rev (Y (0::nat))"
      using a1 by blast
    obtain da_i where "x \<notin> inv Rev (Y da_i)"
      by (meson True assms(1) setrev_lub_emptyD)
    have "y \<notin> f ` inv Rev (Y da_i)"
    proof (rule ccontr, simp)
      assume a2: "y \<in> f ` inv Rev (Y da_i)"
      then obtain da_x where "y =  f da_x" and "da_x \<in> inv Rev (Y da_i)"
        by blast
      have "Y 0 \<sqsubseteq> Y da_i"
        by (simp add: assms(1) po_class.chain_mono)
      then have "\<And>x. x \<in> inv Rev (Y da_i) \<Longrightarrow> x \<in> inv Rev (Y 0)"
        by (meson revBelowNeqSubset subsetCE)
      then have "da_x \<in> inv Rev (Y 0)"
        using \<open>(da_x::'a) \<in> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> by auto
      then have "x = da_x"
        using \<open>(y::'b) = (f::'a \<Rightarrow> 'b) (da_x::'a)\<close> assms(2) inj_onD y_def_1 y_def_2 by fastforce
      show "False"
        using \<open>(da_x::'a) \<in> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> \<open>(x::'a) = (da_x::'a)\<close> \<open>(x::'a) \<notin> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> by auto
    qed
    then show "\<exists>i::nat. y \<notin> f ` inv Rev (Y i)"
      by blast
  qed
  then show ?thesis 
    apply (simp add: setrevImage_def)
    by (simp add: True inv_rev_rev)
next
  case False
  have f1: "(\<Squnion>i::nat. Rev (f ` inv Rev (Y i))) = 
    Rev (\<Inter>{uu::'b set. \<exists>i::nat. uu = f ` inv Rev (Y i)})"
    apply (subst setrevLubEqInter)
     apply (metis (mono_tags, lifting) assms(1) image_mono inv_rev_rev po_class.chain_def revBelowNeqSubset)
    by (simp add: inv_rev_rev)
  show ?thesis
    apply (simp add: setrevImage_def)
    apply (subst po_eq_conv, rule)
     apply (simp add: f1) defer
     apply (simp add: f1) 
    apply (simp_all add: less_set_def)
    using assms(1) setrevLub_lub_eq_all apply fastforce
  proof 
    fix y::'b 
    assume a11: "y \<in> \<Inter>{uu::'b set. \<exists>i::nat. uu = f ` inv Rev (Y i)}"
    then have "\<And>i. y \<in> f ` inv Rev (Y i)"
      by blast
    then have " y \<in> f ` inv Rev (Y 0)"
      by simp
    then obtain x where "y = f x" and "x \<in> inv Rev (Y 0)"
      by blast
    have "\<forall> i. x \<in> inv Rev (Y i)"
    proof (rule ccontr, simp)
      assume a111: "\<exists>i::nat. x \<notin> inv Rev (Y i) "
      obtain da_i where "x \<notin> inv Rev (Y da_i)"
        using a111 by auto
      have "y \<in> f ` inv Rev (Y da_i)"
        by (simp add: \<open>\<And>i::nat. (y::'b) \<in> (f::'a \<Rightarrow> 'b) ` inv Rev ((Y::nat \<Rightarrow> 'a set rev) i)\<close>)
      obtain da_x where "y = f da_x" and "da_x \<in> inv Rev (Y da_i)"
        using \<open>(y::'b) \<in> (f::'a \<Rightarrow> 'b) ` inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> by blast
      then have "da_x \<in> inv Rev (Y 0)"
        by (meson assms(1) contra_subsetD po_class.chain_mono revBelowNeqSubset zero_le)
      then have "x = da_x"
        using \<open>(x::'a) \<in> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (0::nat))\<close> \<open>(y::'b) = (f::'a \<Rightarrow> 'b) (da_x::'a)\<close> \<open>(y::'b) = (f::'a \<Rightarrow> 'b) (x::'a)\<close> assms(2) inj_on_eq_iff by fastforce
      show False
        using \<open>(da_x::'a) \<in> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> \<open>(x::'a) = (da_x::'a)\<close> \<open>(x::'a) \<notin> inv Rev ((Y::nat \<Rightarrow> 'a set rev) (da_i::nat))\<close> by auto
    qed
    show "y \<in> f ` inv Rev (Lub Y)"
      by (simp add: \<open>(y::'b) = (f::'a \<Rightarrow> 'b) (x::'a)\<close> 
          \<open>\<forall>i::nat. (x::'a) \<in> inv Rev ((Y::nat \<Rightarrow> 'a set rev) i)\<close> assms(1) setrevLub_lub_eq_all)
  qed
qed

(*Probably have to use setrevImage_inj_on instead of setrevImage*)
lemma newSpsStep_cont:assumes "finite In" shows "cont (\<lambda> H. Abs_uspec ((setrevImage (\<lambda> h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb)  sb)) 
                                      (setrevImage (\<lambda> h. spfStep_inj In Out h) 
                                      (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) 
                                      (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>H))))),Discr  In, Discr Out))"
proof(rule Cont.contI2, simp add: newSpsStep_mono)
  fix Y::"nat \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"chain Y"
  assume a2:"chain(\<lambda>i. Abs_uspec
                        (setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (h sb) sb))
                          (setrevImage (spfStep_inj In Out)
                            (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))),
                         Discr In, Discr Out)) "
  have h1:"uspecWell (setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
          (setrevImage (spfStep_inj In Out)
            (setrevImage (\<lambda>h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(\<Squnion>i. Y i))))))
         (Discr In) (Discr Out)"
    by (simp add: newSpsStep_uspecWell)
  have h2:"uspecWell (\<Squnion>i. setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
                              (setrevImage (spfStep_inj In Out)
                                (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))))
                             (Discr In) (Discr Out)"
    sorry
  (*Inj*)    (*inj has to be exchanged with inj_on and the Inputset*)
  have inj1:"\<forall>i. inj_on (\<lambda>h sbEl. spfRtIn\<cdot>(h sbEl)) (inv Rev (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))"
  proof(auto)
    fix i::nat
    show "inj_on (\<lambda>h sbEl. spfRtIn\<cdot>(h sbEl)) (inv Rev (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))"
    proof(rule inj_onI)
      fix x y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
      assume a3:"(\<lambda>sbEl. spfRtIn\<cdot>(x sbEl)) = (\<lambda>sbEl. spfRtIn\<cdot>(y sbEl))"
      then show "x = y"
        apply(subst fun_eq_iff, simp add: a3)
        by (metis a3 spfRtIn_dom spfRt_inj_h spf_eq)
    qed
  qed
  have inj2:"\<forall>i::nat. inj_on (spfStep_inj In Out)
              (inv Rev (setrevImage (\<lambda>h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i)))))"
  proof(auto)
    fix i::nat
    show "inj_on (spfStep_inj In Out)
               (inv Rev (setrevImage (\<lambda>(h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i)))))"
    proof(rule inj_onI)
      fix x y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
      assume a1:"x \<in> inv Rev (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))"
      assume a2:"y \<in> inv Rev (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))"
      assume a3:" spfStep_inj In Out x = spfStep_inj In Out y"
      have "\<forall>g\<in>(inv Rev (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))). \<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out"
        by(simp add: spsStep_P_def setrevImage_def setrevFilter_def inv_rev_rev)
      then have "(inv Rev (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))) \<subseteq> {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}"
        by auto
      then have "inj_on (spfStep_inj In Out) (inv Rev (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i)))))"
        by (metis (mono_tags, lifting) assms inj_on_subset spfStep_inj_on)
      then show "x = y"
        by (metis a1 a2 a3 inj_on_eq_iff)
    qed
  qed
  have inj3:"\<forall>i::nat. inj_on (\<lambda>h::'a stream\<^sup>\<Omega> \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (h sb) sb))
              (inv Rev (setrevImage (spfStep_inj In Out)
                         (setrevImage (\<lambda>(h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))))"
  proof(auto)
    fix i::nat
    show"inj_on (\<lambda>h::'a stream\<^sup>\<Omega> \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (h sb) sb))
               (inv Rev (setrevImage (spfStep_inj In Out)
                          (setrevImage (\<lambda>(h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))))"
    proof(rule inj_onI)
      fix x y::"'a stream\<^sup>\<Omega> \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
      assume a1:"x \<in> inv Rev (setrevImage (spfStep_inj In Out)
                      (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i)))))"
      assume a2:"y \<in> inv Rev (setrevImage (spfStep_inj In Out)
                      (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i)))))"
      assume a3:"Abs_cufun (\<lambda>sb. Rep_cufun (x sb) sb) = Abs_cufun (\<lambda>sb. Rep_cufun (y sb) sb)" (*don't know*)
      show "x = y"
      proof (rule ccontr)
        assume a111: "x \<noteq> y"
        obtain da_x where da_x_def_1: "x = spfStep_inj In Out (\<lambda> sbEl. spfRtIn\<cdot>(da_x sbEl))" 
          and "da_x \<in> inv Rev (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i)))"
          by (smt a1 setrevExists_def setrevForall_def setrevforall_image)
        obtain da_y where da_y_def_1: "y = spfStep_inj In Out (\<lambda> sbEl. spfRtIn\<cdot>(da_y sbEl))" 
          and "da_y \<in> inv Rev (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i)))"
          by (smt a2 setrevExists_def setrevForall_def setrevforall_image)
        have "da_x \<noteq> da_y"
          using \<open>(x::'a stream\<^sup>\<Omega> \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) = spfStep_inj (In::channel set) (Out::channel set) (\<lambda>sbEl::'a sbElem. spfRtIn\<cdot> ((da_x::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl))\<close> \<open>(y::'a stream\<^sup>\<Omega> \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) = spfStep_inj (In::channel set) (Out::channel set) (\<lambda>sbEl::'a sbElem. spfRtIn\<cdot> ((da_y::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl))\<close> a111 by blast
        then obtain ele where ele_def: "da_x ele \<noteq> da_y ele"
          by (meson  ext)
        have da_x_ele_dom_ran: "ufDom\<cdot>(da_x ele) = In \<and> ufRan\<cdot>(da_x ele ) = Out"
          by (metis (mono_tags, lifting) Abs_cfun_inverse2 \<open>(da_x::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) \<in> inv Rev (setrevFilter (spsStep_P (In::channel set) (Out::channel set))\<cdot> (spsStep_h\<cdot> ((Y::nat \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec) (i::nat))))\<close> inv_rev_rev member_filter setrevFilter_def setrevfilter_cont spsStep_P_def)
        have "ufDom\<cdot>(da_y ele) = In \<and> ufRan\<cdot>(da_y ele ) = Out"
          by (metis (mono_tags, lifting) Abs_cfun_inverse2 \<open>(da_y::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) \<in> inv Rev (setrevFilter (spsStep_P (In::channel set) (Out::channel set))\<cdot> (spsStep_h\<cdot> ((Y::nat \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec) (i::nat))))\<close> inv_rev_rev member_filter setrevFilter_def setrevfilter_cont spsStep_P_def)
        then obtain da_sb where da_sb_def: "da_x ele \<rightleftharpoons> da_sb \<noteq> da_y ele  \<rightleftharpoons> da_sb"
          by (metis da_x_ele_dom_ran ele_def ufun_eqI)
        have "ubDom\<cdot>da_sb = In"
          by (metis \<open>ufDom\<cdot> ((da_x::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) (ele::'a sbElem)) = (In::channel set) \<and> ufRan\<cdot>(da_x ele) = (Out::channel set)\<close> \<open>ufDom\<cdot> ((da_y::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) (ele::'a sbElem)) = (In::channel set) \<and> ufRan\<cdot>(da_y ele) = (Out::channel set)\<close> da_sb_def option.exhaust_sel ubclDom_ubundle_def ufdom_2ufundom)
        obtain sb where sb_def:"((inv convDiscrUp (sbHdElem\<cdot>sb))) =  (Rep_sbElem ele) 
                                                \<and> sbHdElemWell sb \<and> ubDom\<cdot>sb = dom (Rep_sbElem ele)"
          by (metis (full_types) Abs_sbElem_inverse mem_Collect_eq sbElem_surj sbHdElemWell_def sbHdElem_sbElemWell)
        have sb_Well:"sbHdElemWell sb"
          by(simp add: sb_def)
        have "(\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb)) x 
      = Abs_cufun (\<lambda>sb. Rep_cufun (( spfStep_inj In Out (\<lambda> sbEl. spfRtIn\<cdot>(da_x sbEl))) sb) sb)"
          by (simp add: da_x_def_1)
        have "(\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb)) y
      = Abs_cufun (\<lambda>sb. Rep_cufun (( spfStep_inj In Out (\<lambda> sbEl. spfRtIn\<cdot>(da_y sbEl))) sb) sb)"
          by (simp add: da_y_def_1)        
        (* DD:   *)
        have "sbHdElem\<cdot>(ubConc (convSB (sbHdElem\<cdot>sb))\<cdot>da_sb) = sbHdElem\<cdot>sb"
          sorry  
        have "sbRt\<cdot>(ubConc (convSB (sbHdElem\<cdot>sb))\<cdot>da_sb) = da_sb"
          sorry  
        have "sbHdElemWell (ubConc (convSB (sbHdElem\<cdot>sb))\<cdot>da_sb)"
          by (metis \<open>sbHdElem\<cdot> (ubConc (convSB (sbHdElem\<cdot>(sb::'a stream\<^sup>\<Omega>)))\<cdot> (da_sb::'a stream\<^sup>\<Omega>)) = sbHdElem\<cdot>sb\<close> 
              sbHdElemWell_def sbHdElem_bottom_exI sbHdElem_channel sbHdElem_dom sb_Well)
        show False
          sorry
        qed
      qed
    qed








  (*Chain*)
  have chain0:"chain (\<lambda>i::nat. setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i)))"
    by (simp add: a1 cont_pref_eq1I po_class.chainE)
  have chain1:"chain (\<lambda>i::nat. setrevImage (\<lambda>(h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))"
    apply(rule ch2ch_monofun[of"setrevImage (\<lambda>(h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl))"])
    by (simp_all add: image_mono_rev chain0)
  have chain2:"chain (\<lambda>i::nat. setrevImage (spfStep_inj In Out)
                     (setrevImage (\<lambda>(h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i)))))"
    apply(rule ch2ch_monofun[of "setrevImage (spfStep_inj In Out)"])
    by (simp_all add: image_mono_rev chain1)
  have h3:"setrevImage (\<lambda>h::'a stream\<^sup>\<Omega> \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (h sb) sb))
     (setrevImage (spfStep_inj In Out)
       (setrevImage (\<lambda>(h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(\<Squnion>i. Y i))))) \<sqsubseteq>
    (\<Squnion>i::nat. setrevImage (\<lambda>h::'a stream\<^sup>\<Omega> \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (h sb) sb))
                (setrevImage (spfStep_inj In Out)
                  (setrevImage (\<lambda>(h::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun) sbEl::'a sbElem. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))))"
    apply(simp add: a1 a2 contlub_cfun_arg contlub_cfun_fun)
    apply(subst setreImage_lub_inj_on, simp add: chain0, simp add: inj1)
    apply(subst setreImage_lub_inj_on, simp add: chain1, simp add: inj2)
    apply(subst setreImage_lub_inj_on, simp add: chain2, simp add: inj3)
    by(simp)
  have "(\<Squnion>i. Abs_uspec (setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
                              (setrevImage (spfStep_inj In Out)
                                (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))),
                             Discr In, Discr Out)) = (Abs_uspec (\<Squnion>i. setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
                              (setrevImage (spfStep_inj In Out)
                                (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))),
                             Discr In, Discr Out))"
    apply(subst lub_uspec, simp add: a2)
    apply(subst rep_abs_uspec)
    apply (simp add: newSpsStep_uspecWell)
    apply(subst lub_in, simp_all)
    by (metis (mono_tags, lifting) a1 newSpsStep_mono_h po_class.chain_def)
  then show "Abs_uspec
        (setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
          (setrevImage (spfStep_inj In Out)
            (setrevImage (\<lambda>h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(\<Squnion>i. Y i))))),
         Discr In, Discr Out) \<sqsubseteq>
       (\<Squnion>i. Abs_uspec (setrevImage (\<lambda>h. Abs_cufun (\<lambda>sb. Rep_cufun (h sb) sb))
                              (setrevImage (spfStep_inj In Out)
                                (setrevImage (\<lambda> h sbEl. spfRtIn\<cdot>(h sbEl)) (setrevFilter (spsStep_P In Out)\<cdot>(spsStep_h\<cdot>(Y i))))),
                             Discr In, Discr Out))"
    by(simp add: below_uspec_def h1 h2 h3)
qed
  
    

(*NewSpsStep Lemma End*)
(*    
lemma inner_mono[simp]:"monofun(\<lambda> sb. if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then Rev {spfStep_inj In Out g sb | g. g\<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)} else uspecRevSet\<cdot>(uspecLeast In Out))"
proof(rule monofunI)
  fix x y::"'a stream\<^sup>\<Omega>"
  assume a1:"x \<sqsubseteq> y"
  show "(if sbHdElemWell x \<and> ubDom\<cdot>x = In
        then Rev {spfStep_inj In Out g x |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
        else uspecRevSet\<cdot>(uspecLeast In Out)) \<sqsubseteq>
       (if sbHdElemWell y \<and> ubDom\<cdot>y = In
        then Rev {spfStep_inj In Out g y |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
        else uspecRevSet\<cdot>(uspecLeast In Out))"
    proof(cases "sbHdElemWell x")
      case True
      then have t2:"sbHdElemWell y"
        by (metis a1 eq_bottom_iff sbHdElemWell_def ubdom_below ubgetch_below)
      show ?thesis
        apply(subst spfStep_eq_sb[of x y])
        apply(simp_all add: True t2 less_set_def a1)
        using a1 ubdom_below by blast
    next
      case False
      then show ?thesis
        apply (simp add: uspecrevset_insert uspecLeast_def, auto)
        apply(simp add: less_set_def ufclDom_ufun_def ufclRan_ufun_def)
        by (smt Collect_mono spfStep_inj_def ufRestrict_dom ufRestrict_ran)
    qed
qed
    
lemma inner_cont[simp]:assumes "finite In" shows "cont (\<lambda> sb. if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then Rev {spfStep_inj In Out g sb | g. g\<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)} else uspecRevSet\<cdot>(uspecLeast In Out))"
proof(rule Cont.contI2,simp)
  fix Y::"nat \<Rightarrow> 'a stream\<^sup>\<Omega>"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. if sbHdElemWell (Y i) \<and> ubDom\<cdot>(Y i) = In
                       then Rev {spfStep_inj In Out g (Y i) |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
                       else uspecRevSet\<cdot>(uspecLeast In Out))"
  have if_eq:"sbHdElemWell (\<Squnion>i. Y i) \<and> ubDom\<cdot>(\<Squnion>i::nat. Y i) = In \<Longrightarrow> \<exists>i. sbHdElemWell (Y i) \<and> ubDom\<cdot>(Y i) = In"
    using a1 assms sbhdelemwell_neg_adm_fin ubdom_chain_eq2 by blast
  show "(if sbHdElemWell (\<Squnion>i::nat. Y i) \<and> ubDom\<cdot>(\<Squnion>i::nat. Y i) = In
        then Rev {spfStep_inj In Out g (\<Squnion>i::nat. Y i) |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
        else uspecRevSet\<cdot>(uspecLeast In Out)) \<sqsubseteq>
       (\<Squnion>i::nat. if sbHdElemWell (Y i) \<and> ubDom\<cdot>(Y i) = In
                  then Rev {spfStep_inj In Out g (Y i) |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
                  else uspecRevSet\<cdot>(uspecLeast In Out))"
  proof(cases "sbHdElemWell (\<Squnion>i. Y i) \<and> ubDom\<cdot>(\<Squnion>i. Y i) = In")
    case True
    obtain n where n_def:"sbHdElemWell ( Y n) \<and> ubDom\<cdot>( Y n) = In"
      using True if_eq by blast
    then have h1:"(if sbHdElemWell (Y n) \<and> ubDom\<cdot>(Y n) = In
               then Rev {spfStep_inj In Out g (Y n) |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
               else uspecRevSet\<cdot>(uspecLeast In Out)) \<sqsubseteq> (\<Squnion>i. if sbHdElemWell (Y i) \<and> ubDom\<cdot>(Y i) = In
               then Rev {spfStep_inj In Out g (Y i) |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
               else uspecRevSet\<cdot>(uspecLeast In Out))"
      using a2 below_lub by blast
    have h2:"(if sbHdElemWell (\<Squnion>i::nat. Y i) \<and> ubDom\<cdot>(\<Squnion>i::nat. Y i) = In
        then Rev {spfStep_inj In Out g (\<Squnion>i::nat. Y i) |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
        else uspecRevSet\<cdot>(uspecLeast In Out)) = (if sbHdElemWell (Y n) \<and> ubDom\<cdot>(Y n) = In
               then Rev {spfStep_inj In Out g (Y n) |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
               else uspecRevSet\<cdot>(uspecLeast In Out))"
      apply(simp add: True n_def)
      apply(subst spfStep_eq_sb[of "Y n" "Lub Y "])
      by (simp_all add: a1 is_ub_thelub n_def)
    show ?thesis
      by(simp only: h2 h1)
  next
    case False
    then have f2:"\<forall>i. \<not> (sbHdElemWell (Y i) \<and> ubDom\<cdot>(Y i) = In)"
      by (smt a1 is_ub_thelub sbHdElemWell_def sbHdElem_bottom_exI sbHdElem_channel sbHdElem_eq ubdom_chain_eq2)
    then have "(\<Squnion>i::nat. if sbHdElemWell (Y i) \<and> ubDom\<cdot>(Y i) = In
               then Rev {spfStep_inj In Out g (Y i) |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
               else uspecRevSet\<cdot>(uspecLeast In Out)) = uspecRevSet\<cdot>(uspecLeast In Out)"
      by (simp add: f2)
    then show ?thesis
      by(simp add: False)
  qed
qed
  
    
lemma spsStep_inj2_mono[simp]:assumes "finite In" shows"monofun (\<lambda> h.  \<Lambda> sb.  if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then Rev {spfStep_inj In Out g sb | g. g\<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)} else uspecRevSet\<cdot>(uspecLeast In Out))"  
proof(rule monofunI)
  fix x y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"x \<sqsubseteq> y"
  show "(\<Lambda> sb.
           if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
           then Rev {spfStep_inj In Out g sb |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>x) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
           else uspecRevSet\<cdot>(uspecLeast In Out)) \<sqsubseteq>
       (\<Lambda> sb.
           if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
           then Rev {spfStep_inj In Out g sb |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>y) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
           else uspecRevSet\<cdot>(uspecLeast In Out))"
    apply(simp add: below_cfun_def  below_fun_def less_set_def assms, auto)
    by (metis (mono_tags, hide_lams) a1 monofun_cfun_arg revBelowNeqSubset subsetCE)
qed
  
  
lemma spsStep_inj2_cont[simp]:assumes "finite In" shows "cont (\<lambda> h.  \<Lambda> sb.  if sbHdElemWell sb \<and> ubDom\<cdot>sb = In then Rev {spfStep_inj In Out g sb | g. g\<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)} else uspecRevSet\<cdot>(uspecLeast In Out))"
proof(rule Cont.contI2, simp add: assms)
  fix Y::"nat \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec" and sb::"'a stream\<^sup>\<Omega>"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. \<Lambda> (sb::'a stream\<^sup>\<Omega>).
                          if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
                          then Rev {spfStep_inj In Out g sb |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun.
                                    g \<in> inv Rev (spsStep_h\<cdot>(Y i)) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
                          else uspecRevSet\<cdot>(uspecLeast In Out))"
  have h1:"(\<Squnion>i. \<Lambda> sb.
                     if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
                     then Rev {spfStep_inj In Out g sb |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i)) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
                     else uspecRevSet\<cdot>(uspecLeast In Out)) = (\<Lambda> sb. \<Squnion>i.
                     if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
                     then Rev {spfStep_inj In Out g sb |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i)) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
                     else uspecRevSet\<cdot>(uspecLeast In Out))"
    sorry
  have h2:"cont (\<lambda> sb. \<Squnion>i.
                     if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
                     then Rev {spfStep_inj In Out g sb |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i)) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
                     else uspecRevSet\<cdot>(uspecLeast In Out))"
    sorry
  have c1:"chain (\<lambda>i::nat. Rev {spfStep_inj (ubDom\<cdot>sb) Out g sb |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun.
                         g \<in> inv Rev (spsStep_h\<cdot>(Y i)) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = ubDom\<cdot>sb \<and> ufRan\<cdot>(g m) = Out)})"
    sorry
  have h3:"(  if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
           then Rev {spfStep_inj In Out g sb |g. g \<in> inv Rev (spsStep_h\<cdot>(\<Squnion>i. Y i)) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
           else uspecRevSet\<cdot>(uspecLeast In Out)) \<sqsubseteq>
       (\<Squnion>i. if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
                     then Rev {spfStep_inj In Out g sb |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i)) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
                     else uspecRevSet\<cdot>(uspecLeast In Out))"
    apply auto
    apply(simp add: inv_rev_rev setrevLubEqInter c1 less_set_def, auto)
    sorry
  then show"(\<Lambda> sb.
           if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
           then Rev {spfStep_inj In Out g sb |g. g \<in> inv Rev (spsStep_h\<cdot>(\<Squnion>i. Y i)) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
           else uspecRevSet\<cdot>(uspecLeast In Out)) \<sqsubseteq>
       (\<Squnion>i. \<Lambda> sb.
                     if sbHdElemWell sb \<and> ubDom\<cdot>sb = In
                     then Rev {spfStep_inj In Out g sb |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i)) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}
                     else uspecRevSet\<cdot>(uspecLeast In Out))" 
    sorry
qed
  
  *)

lemma spsStep_inj_mono[simp]:"monofun (\<lambda> h. Rev {\<Lambda> sb. spfStep_inj In Out g sb | g. g\<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)})"  
proof(rule monofunI)
  fix x y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"x \<sqsubseteq> y"
  show "Rev {\<Lambda> (sb::'a stream\<^sup>\<Omega>). spfStep_inj In Out g sb |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun.
            g \<in> inv Rev (spsStep_h\<cdot>x) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)} \<sqsubseteq>
       Rev {\<Lambda> (sb::'a stream\<^sup>\<Omega>). spfStep_inj In Out g sb |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>y) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}"
  apply(simp add: less_set_def, auto)
    by (metis (mono_tags, hide_lams) a1 monofun_cfun_arg revBelowNeqSubset subsetCE)
qed

  
lemma spsStep_inj_cont[simp]:assumes "finite In" shows"cont (\<lambda> h. Rev {\<Lambda> sb. spfStep_inj In Out g sb | g. g\<in> inv Rev (spsStep_h\<cdot>h)  \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)})"
proof(rule Cont.contI2,simp)
  fix Y::"nat \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. Rev {\<Lambda> (sb::'a stream\<^sup>\<Omega>). spfStep_inj In Out g sb |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun.
                            g \<in> inv Rev (spsStep_h\<cdot>(Y i)) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)})"
  have "\<And>x. \<forall>xa.
          (\<exists>i. xa = {spfStep_inj In Out g |g.(\<forall>m. g m \<in> Rep_rev_uspec (Y i m)) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}) \<longrightarrow>
          x \<in> xa \<Longrightarrow> \<exists>g. x = spfStep_inj In Out g \<and>
          (\<forall>x. (\<exists>i. x = {g. \<forall>m. g m \<in> Rep_rev_uspec (Y i m)}) \<longrightarrow> g \<in> x) \<and>  (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)"
  proof-
    fix x::"'a stream\<^sup>\<Omega> \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
    assume a1:"\<forall>xa.
          (\<exists>i. xa = {spfStep_inj In Out g |g.
                          (\<forall>m. g m \<in> Rep_rev_uspec (Y i m)) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}) \<longrightarrow>
          x \<in> xa"
    then have h1:"\<forall>i. x \<in> {spfStep_inj In Out g |g.(\<forall>m. g m \<in> Rep_rev_uspec (Y i m)) \<and> 
          (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}"
      by auto
    then obtain f where f_def:"x = spfStep_inj In Out f \<and> (\<forall>m. f m \<in> Rep_rev_uspec (Y 0 m)) \<and> 
          (\<forall>m. ufDom\<cdot>(f m) = In \<and> ufRan\<cdot>(f m) = Out)"
      by blast
    have h1_2:"\<forall>i. (\<forall>m. f m \<in> Rep_rev_uspec (Y i m))"
    proof
      fix i::nat
      have"\<not>(\<forall>m. f m \<in> Rep_rev_uspec (Y i m)) \<Longrightarrow> x \<notin> {spfStep_inj In Out g |g. \<forall>m. g m \<in> Rep_rev_uspec (Y i m) \<and> 
          ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out}"
      proof-
        assume a_01:"\<not> (\<forall>m::'a sbElem. f m \<in> Rep_rev_uspec (Y i m))"
        show " x \<notin> {spfStep_inj In Out g |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. \<forall>m::'a sbElem. g m \<in> Rep_rev_uspec (Y i m) \<and> ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out}"
        proof(cases "\<exists>g. x = spfStep_inj In Out g \<and> g \<noteq> f \<and> (\<forall>m. g m \<in> Rep_rev_uspec (Y i m) \<and> ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)")
          case True
          then obtain g where g_def:"x = spfStep_inj In Out g \<and> g \<noteq> f \<and> (\<forall>m. g m \<in> Rep_rev_uspec (Y i m) \<and> ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)"
            by auto
          have "g \<in>  {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out} \<and> f \<in>  {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}"
            by(simp add: f_def g_def)
          have "inj_on (spfStep_inj In Out)
                 {h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}"
            by(simp add: assms)
          then have "spfStep_inj In Out g \<noteq> spfStep_inj In Out f"
            apply(simp add: spfStep_inj_def)
            apply(insert inj_on_contraD[of "(\<lambda> h. (\<lambda> sb. (if (sbHdElemWell sb) then ufRestrict In Out\<cdot>(h (Abs_sbElem(inv convDiscrUp (sbHdElem\<cdot>sb)))) else ufLeast In Out)))" "{h. \<forall>m. ufDom\<cdot>(h m) = In \<and> ufRan\<cdot>(h m) = Out}" "g" "f"])
            by(simp add: True f_def g_def)
          then show ?thesis
            using f_def g_def by auto
        next
          case False
          then show ?thesis
            using a_01 by blast 
        qed
      qed
      then show "\<forall>m. f m \<in> Rep_rev_uspec (Y i m)"
        using h1 by blast
    qed    
    have h2:"\<And>g. (\<forall>x. (\<exists>i. x = {g. \<forall>m. g m \<in> Rep_rev_uspec (Y i m)}) \<longrightarrow> g \<in> x) = ((\<forall>i. g\<in> {h. \<forall>m. h m \<in> Rep_rev_uspec (Y i m)}))"
      by blast
    show "
       \<exists>g. x = spfStep_inj In Out g \<and> (\<forall>x. (\<exists>i. x = {g. \<forall>m. g m \<in> Rep_rev_uspec (Y i m)}) \<longrightarrow> g \<in> x) \<and>
          (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)"
      apply(simp add: h2)
      using f_def h1_2 by auto
  qed 
  then show " Rev {\<Lambda> (sb::'a stream\<^sup>\<Omega>). spfStep_inj In Out g sb |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun.
            g \<in> inv Rev (spsStep_h\<cdot>(\<Squnion>i::nat. Y i)) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)} \<sqsubseteq>
       (\<Squnion>i::nat. Rev {\<Lambda> (sb::'a stream\<^sup>\<Omega>). spfStep_inj In Out g sb |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun.
                       g \<in> inv Rev (spsStep_h\<cdot>(Y i)) \<and> (\<forall>m::'a sbElem. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)})"
  apply(simp add: a1 contlub_cfun_fun contlub_cfun_arg assms)
    apply(subst setrevLubEqInterII, simp add: a1)
    apply(subst setrevLubEqInter)
    apply (simp add: a2)
    apply(simp add: eta_cfun spsStep_h_insert setify_def uspecRevSet_def inv_rev_rev rev_inv_rev less_set_def assms)
    sorry
qed
  
lemma spsStep_inj_insert:assumes "finite In" shows"spsStep_inj In Out\<cdot>h = Rev {\<Lambda> sb. spfStep_inj In Out g sb | g. g\<in> inv Rev (spsStep_h\<cdot>h) \<and> (\<forall>m. ufDom\<cdot>(g m) = In \<and> ufRan\<cdot>(g m) = Out)}"
  by(simp add: spsStep_inj_def assms)
    
    
lemma spsStep_mono[simp]:"monofun(\<lambda> h. Abs_rev_uspec ((\<lambda>f. Abs_cufun(\<lambda>sb. (Rep_cufun (f\<cdot>sb)) sb)) ` (inv Rev (spsStep_inj In Out\<cdot>h))) In Out)" 
proof(rule monofunI)
  fix x y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"x\<sqsubseteq>y"
  have h1:"uspecWell (Rev ((\<lambda>f::'a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>x))) (Discr In) (Discr Out)"
    sorry
  have h2:"uspecWell (Rev ((\<lambda>f::'a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>y))) (Discr In) (Discr Out)"
    sorry
  show"Abs_rev_uspec ((\<lambda>f. Abs_cufun (\<lambda>sb. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>x)) In Out \<sqsubseteq>
       Abs_rev_uspec ((\<lambda>f. Abs_cufun (\<lambda>sb. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>y)) In Out"
    apply(simp add: below_uspec_def less_set_def)
    apply(subst rep_abs_uspec, simp only: h1)
    apply(subst rep_abs_uspec, simp only: h2)
    by (metis (no_types, lifting) Pair_below_iff a1 below_refl cont_pref_eq1I image_mono inv_rev_rev revBelowNeqSubset)
qed
  
lemma spsStep_cont[simp]:"cont(\<lambda> h. Abs_rev_uspec ((\<lambda>f. Abs_cufun(\<lambda>sb. (Rep_cufun (f\<cdot>sb)) sb)) ` (inv Rev (spsStep_inj In Out\<cdot>h))) In Out) "
proof(rule Cont.contI2, simp)
  fix Y::"nat \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. Abs_rev_uspec ((\<lambda>f. Abs_cufun (\<lambda>sb. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>(Y i))) In Out)"
  have h1:"\<And>i::nat. uspecWell (Rev ((\<lambda>f::'a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>(Y i)))) (Discr In)
               (Discr Out)"
    sorry
  have h2:"uspecWell (Rev ((\<lambda>f::'a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (\<Squnion>i::nat. spsStep_inj In Out\<cdot>(Y i)))) (Discr In)
     (Discr Out)"
    sorry
  have h3:"Rep_uspec
     (Abs_uspec
       (\<Squnion>i::nat. Rep_uspec (Abs_rev_uspec ((\<lambda>f::'a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>(Y i))) In
                              Out))) =
       (\<Squnion>i::nat. Rep_uspec (Abs_rev_uspec ((\<lambda>f::'a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>(Y i))) In
                              Out))"
    by (smt a2 cont2contlubE h1 lub_eq lub_uspec rep_abs_uspec uspec_rep_cont)
  have h5:"\<And>x::('a stream\<^sup>\<Omega>) ufun.
       \<forall>xa::('a stream\<^sup>\<Omega>) ufun set.
          (\<exists>i::nat. xa = (\<lambda>f::'a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>(Y i))) \<longrightarrow> x \<in> xa \<Longrightarrow>
       x \<in> (\<lambda>f::'a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (f\<cdot>sb) sb)) `
            \<Inter>{uu::('a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun) set. \<exists>i::nat. uu = inv Rev (spsStep_inj In Out\<cdot>(Y i))}"
  proof-
    fix x::"('a stream\<^sup>\<Omega>) ufun"
    assume a01:"\<forall>xa.
          (\<exists>i. xa = (\<lambda>f. Abs_cufun (\<lambda>sb. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>(Y i))) \<longrightarrow> x \<in> xa"
    then have a02:"\<forall>i. x \<in> (\<lambda>f. Abs_cufun (\<lambda>sb. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>(Y i))"
      by auto
    have "\<exists>xa\<in>\<Inter>{uu. \<exists>i. uu = inv Rev (spsStep_inj In Out\<cdot>(Y i))}.
       x = Abs_cufun (\<lambda>sb. Rep_cufun (xa\<cdot>sb) sb)"
    proof-
      have h02:"(\<exists>xa\<in>\<Inter>{uu. \<exists>i. uu = inv Rev (spsStep_inj In Out\<cdot>(Y i))}.
       x = Abs_cufun (\<lambda>sb. Rep_cufun (xa\<cdot>sb) sb)) =
        (\<exists>xa\<in>\<Inter>{inv Rev (spsStep_inj In Out\<cdot>(Y i)) | i. True}.
       x = Abs_cufun (\<lambda>sb. Rep_cufun (xa\<cdot>sb) sb))"
        by auto
      show"(\<exists>xa\<in>\<Inter>{uu. \<exists>i. uu = inv Rev (spsStep_inj In Out\<cdot>(Y i))}.
       x = Abs_cufun (\<lambda>sb. Rep_cufun (xa\<cdot>sb) sb))"
      proof(subst h02)
        obtain xa_set where xa_set_def:"xa_set= {xa. \<exists>i. xa\<in>inv Rev (spsStep_inj In Out\<cdot>(Y i)) \<and> x = Abs_cufun (\<lambda>sb. Rep_cufun (xa\<cdot>sb) sb)}"
          by simp
        obtain bla where bla_def:"bla = {xa. xa\<in> (\<Squnion>i. inv Rev (spsStep_inj In Out\<cdot>(Y i))) \<and> x = Abs_cufun (\<lambda>sb. Rep_cufun (xa\<cdot>sb) sb)}"
          by simp
        show "(\<exists>xa\<in>\<Inter>{inv Rev (spsStep_inj In Out\<cdot>(Y i)) | i. True}.
            x = Abs_cufun (\<lambda>sb. Rep_cufun (xa\<cdot>sb) sb))" (*Problem*)
          sorry
      qed
        
    qed
    then show "x \<in> (\<lambda>f. Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. Rep_cufun (f\<cdot>sb) sb)) `
            \<Inter>{uu. \<exists>i::nat. uu = inv Rev (spsStep_inj In Out\<cdot>(Y i))}"
      by(simp add: image_def)
  qed
  show "Abs_rev_uspec ((\<lambda>f. Abs_cufun (\<lambda>sb. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>(\<Squnion>i. Y i))) In Out \<sqsubseteq>
       (\<Squnion>i. Abs_rev_uspec ((\<lambda>f. Abs_cufun (\<lambda>sb. Rep_cufun (f\<cdot>sb) sb)) ` inv Rev (spsStep_inj In Out\<cdot>(Y i))) In Out)"
    apply(simp add: a1 contlub_cfun_fun contlub_cfun_arg)
    apply(simp add: below_uspec_def)
    apply(simp only: h2 rep_abs_uspec)
    apply(simp add: lub_uspec a2 h3)
    apply(subst rep_abs_uspec)
     apply(simp only: h1 rep_abs_uspec h2)
    apply(subst setrevLubEqInterII, simp add: a1)
    apply(subst lub_in)
    apply (metis (no_types, lifting) Pair_below_iff a2 h1 po_class.chain_def rep_abs_uspec rep_uspec_belowI)
    apply auto
    apply(subst setrevLubEqInter)
    apply (metis (no_types, lifting) Pair_below_iff a2 h1 po_class.chain_def rep_abs_uspec rep_uspec_belowI)
    apply(simp add: h1 h2 inv_rev_rev rev_inv_rev less_set_def)
    apply auto
    by(simp add: h5)
qed
  
  
    
    
    
  (*
lemma spsStep_inner_cont[simp]:assumes "\<And>sb. ufDom\<cdot>(f\<cdot>sb) = In" shows "cont (\<lambda> sb. (ubDom\<cdot>sb = In) \<leadsto>((f\<cdot>sb)\<rightleftharpoons> sb))"
  sorry  
    

lemma spsStep_inner_well[simp]:assumes "\<And>sb. ufDom\<cdot>(f\<cdot>sb) = In" shows "ufWell (\<Lambda> sb. (ubDom\<cdot>sb = In) \<leadsto>((f\<cdot>sb)\<rightleftharpoons> sb))"
  sorry  
    
lemma spsStep_mono[simp]:"monofun (\<lambda> h. Abs_rev_uspec ({Abs_ufun(\<Lambda> sb. (ubDom\<cdot>sb = In) \<leadsto>((f\<cdot>sb)\<rightleftharpoons> sb)) | f. f \<in> inv Rev (spsStep_inj In Out\<cdot>h)}) In Out)"
proof(rule monofunI)
  fix x y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"x\<sqsubseteq>y"
  have h1:"uspecWell (Rev {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>x)}) (Discr In)  (Discr Out)"
    sorry
  have h2:"uspecWell (Rev {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>y)}) (Discr In)  (Discr Out)"
    sorry
  have "inv Rev (spsStep_inj In Out\<cdot>y) \<subseteq> inv Rev (spsStep_inj In Out\<cdot>x)"
    by (meson a1 cont_pref_eq1I revBelowNeqSubset)
  then have "{Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>y)} \<sqsubseteq> {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>x)}"
    by(simp add: less_set_def, auto)
  then show "Abs_rev_uspec {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>x)} In Out \<sqsubseteq>
       Abs_rev_uspec {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>y)} In Out"
    by (metis (no_types, lifting) Pair_below_iff below_refl below_rev.simps below_uspec_def h1 h2 rep_abs_uspec)
qed


    
lemma spsStep_cont_inj_h[simp]:"inj_on (\<lambda>f. Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb)) (inv Rev (spsStep_inj In Out\<cdot>h))"
proof(rule inj_onI)
  fix x y::"'a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun"
  assume a1:"x \<in> inv Rev (spsStep_inj In Out\<cdot>h)"
  assume a2:"y \<in> inv Rev (spsStep_inj In Out\<cdot>h)"
  assume a3:"Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>x\<cdot>sb \<rightleftharpoons> sb) = Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>y\<cdot>sb \<rightleftharpoons> sb)"
  have dom_ran_x:"\<And> sb. ufDom\<cdot>(x\<cdot>sb) = In \<and> ufRan\<cdot>(x\<cdot>sb) = Out"
    by (smt Abs_cfun_inverse2 CollectD a1 inv_rev_rev spfStep_inj_cont spfStep_inj_cont_h spfStep_inj_def spfstep_inj_dom spfstep_inj_ran spsStep_inj_insert)
  have dom_ran_y:"\<And> sb. ufDom\<cdot>(y\<cdot>sb) = In \<and> ufRan\<cdot>(y\<cdot>sb) = Out"
    by (smt Abs_cfun_inverse2 CollectD a2 inv_rev_rev spfStep_inj_cont spfStep_inj_cont_h spfStep_inj_def spfstep_inj_dom spfstep_inj_ran spsStep_inj_insert)
  have h1:"\<And>sb. ubDom\<cdot>sb\<noteq> In \<Longrightarrow> ((x\<cdot>sb) \<rightleftharpoons> sb) = ((y\<cdot>sb) \<rightleftharpoons> sb)"
    by (metis dom_ran_x dom_ran_y test2 ufRestrict_apply)
  then have h2:"\<exists>sb. x\<cdot>sb \<rightleftharpoons> sb \<noteq> x\<cdot>sb \<rightleftharpoons> sb \<longrightarrow> x\<cdot>sb \<noteq> y\<cdot>sb"
    by simp
  then have h3:"\<exists>sb. x\<cdot>sb \<noteq> y\<cdot>sb \<Longrightarrow> x \<noteq> y"
    by blast
  have h4:"\<And>sb. x\<cdot>sb \<rightleftharpoons> sb = y\<cdot>sb \<rightleftharpoons> sb"
  proof-
    fix sb::"'a stream\<^sup>\<Omega>"
    show "x\<cdot>sb \<rightleftharpoons> sb = y\<cdot>sb \<rightleftharpoons> sb"
    proof(cases "ubDom\<cdot>sb = In")
    case True
    then show ?thesis
      apply(insert a3)
        sorry
    next
    case False
    then show ?thesis
      by(simp add:  h1)
    qed
  qed
  have "\<And>sb. x\<cdot>sb = y\<cdot>sb"
    apply(rule spf_eq, simp add: dom_ran_x dom_ran_y)
    sorry
  then show "x = y" 
    by (simp add:  cfun_eqI) 
qed
    
    
    
lemma spsStep_cont:"cont (\<lambda> h. Abs_rev_uspec ({Abs_ufun(\<Lambda> sb. (ubDom\<cdot>sb = In) \<leadsto>((f\<cdot>sb)\<rightleftharpoons> sb)) | f. f \<in> inv Rev (spsStep_inj In Out\<cdot>h)}) In Out)"
proof(rule Cont.contI2, simp)
  fix Y::"nat \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"chain Y" 
  assume a2:"chain (\<lambda>i::nat. Abs_rev_uspec {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>(Y i))} In Out)"
  have h1:"\<And>i::nat. uspecWell (Rev {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>(Y i))}) (Discr In)
               (Discr Out)"
    sorry
  have h2:"uspecWell (Rev {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (\<Squnion>i::nat. spsStep_inj In Out\<cdot>(Y i))}) (Discr In)
     (Discr Out)"
    sorry
  have h3:"Rep_uspec
     (Abs_uspec
       (\<Squnion>i. (Rev {Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f::'a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun. f \<in> inv Rev (spsStep_inj In Out\<cdot>(Y i))}, Discr In,
                   Discr Out))) =

       (\<Squnion>i. (Rev {Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f::'a stream\<^sup>\<Omega> \<rightarrow> ('a stream\<^sup>\<Omega>) ufun. f \<in> inv Rev (spsStep_inj In Out\<cdot>(Y i))}, Discr In,
                   Discr Out))"
    by (smt a2 cont2contlubE h1 lub_eq lub_uspec rep_abs_uspec uspec_rep_cont)
  have test:"\<And>g. Abs_cfun (Rep_cfun (spfStep_inj In Out\<cdot>g)) = spfStep_inj In Out\<cdot>g"
    by (simp add: Cfun.cfun.Rep_cfun_inverse)
  have h5:"\<And>x.
       \<forall>xa.
          (\<exists>i. xa = {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>(Y i))}) \<longrightarrow> x \<in> xa \<Longrightarrow>
       \<exists>f.
          x = Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) \<and>
          (\<forall>x. (\<exists>i::nat. x = inv Rev (spsStep_inj In Out\<cdot>(Y i))) \<longrightarrow> f \<in> x)"
  proof-
    fix x::"('a stream\<^sup>\<Omega>) ufun"
    assume a01:"\<forall>xa.
          (\<exists>i. xa = {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>(Y i))}) \<longrightarrow> x \<in> xa"
    then have h01:"\<forall>i. x \<in> {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>(Y i))}"
      by auto
    then obtain f where f_def: "x = Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) \<and> f \<in> inv Rev (spsStep_inj In Out\<cdot>(Y 0))"
      by blast
    have h02:"(\<exists>f.
          x = Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) \<and>
          (\<forall>x. (\<exists>i. x = inv Rev (spsStep_inj In Out\<cdot>(Y i))) \<longrightarrow> f \<in> x)) = 
          (\<exists>f. x = Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) \<and> 
          (\<forall>i. f \<in>inv Rev (spsStep_inj In Out\<cdot>(Y i))))"
      by auto
    show "\<exists>f.
          x = Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) \<and>
          (\<forall>x. (\<exists>i::nat. x = inv Rev (spsStep_inj In Out\<cdot>(Y i))) \<longrightarrow> f \<in> x)"
      sorry
  qed
  show "Abs_rev_uspec {Abs_cufun (\<lambda>sb. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>(\<Squnion>i::nat. Y i))} In Out \<sqsubseteq>
       (\<Squnion>i. Abs_rev_uspec {Abs_cufun (\<lambda>sb::'a stream\<^sup>\<Omega>. (ubDom\<cdot>sb = In)\<leadsto>f\<cdot>sb \<rightleftharpoons> sb) |f. f \<in> inv Rev (spsStep_inj In Out\<cdot>(Y i))} In Out)"
    apply(simp add: a1 contlub_cfun_fun contlub_cfun_arg)
    apply(simp add: below_uspec_def)
    apply(simp only: h2 rep_abs_uspec)
    apply(simp add: lub_uspec a2 )
    apply(subst rep_abs_uspec)
    apply(simp only: h1 rep_abs_uspec h2)
    apply(subst setrevLubEqInterII, simp add: a1)
    apply(simp add: h3 eta_cfun)
    apply(subst lub_in)
    apply (metis (no_types, lifting) Pair_below_iff a2 h1 po_class.chain_def rep_abs_uspec rep_uspec_belowI)
    apply auto
    apply(subst setrevLubEqInter)
    apply (metis (no_types, lifting) Pair_below_iff a2 h1 po_class.chain_def rep_abs_uspec rep_uspec_belowI)
    apply(simp add: h1 h2 inv_rev_rev rev_inv_rev less_set_def)
    apply auto
    by(simp add: h5)
qed*)
  
  
    
(* like spfStep, copy & pasteonly on SPS *)
fun spsStep_x :: "channel set \<Rightarrow> channel set \<Rightarrow> ('m::message sbElem \<Rightarrow> 'm SPS) \<rightarrow> 'm SPS" where
"spsStep_x In Out = (\<Lambda> h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in> inv Rev (spsStep_h\<cdot>h)} In Out)"

lemma [simp]:assumes "finite In" shows "monofun (\<lambda> h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in> inv Rev (spsStep_h\<cdot>h)} In Out)"
proof(rule monofunI)
  fix x y::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
   assume a1: "x \<sqsubseteq> y"
  have "(spsStep_h\<cdot>x) \<sqsubseteq> (spsStep_h\<cdot>y)" 
    by (simp add: a1 monofun_cfun_arg)
  then have "inv Rev(spsStep_h\<cdot>y) \<subseteq> inv Rev (spsStep_h\<cdot>x)"
    by (metis (full_types) SetPcpo.less_set_def below_rev.elims(2) inv_rev_rev)
  then have "\<And>g. g \<in> inv Rev(spsStep_h\<cdot>y) \<Longrightarrow> g \<in> inv Rev (spsStep_h\<cdot>x)"
    by blast
  then have h1:"{spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>y)} \<sqsubseteq>{spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>x)}"
    by (smt Collect_mono SetPcpo.less_set_def)
  have h2:"\<And>g. ufclDom\<cdot>(spfStep In Out\<cdot>g) = In"
    by (simp add: ufclDom_ufun_def assms)
  have h3:"\<And>g. ufclRan\<cdot>(spfStep In Out\<cdot>g) = Out"
    by (simp add: ufclRan_ufun_def assms)
  have h4:"\<And>f h. f\<in>{spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>h)} \<Longrightarrow> \<exists>g. f = spfStep In Out\<cdot>g"
    by auto
  have h2:"uspecWell (Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>x)}) (Discr In) (Discr Out)"
    using h2 h3 by auto
  have h3:"uspecWell (Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>y)}) (Discr In) (Discr Out)"
    by (metis (no_types, lifting) SetPcpo.less_set_def h1 h2 subsetCE uspecWell.simps)
  show "Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>x)} In  Out\<sqsubseteq>
       Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>y)} In Out"
    by (metis (no_types, lifting) Pair_below_iff below_refl below_rev.simps below_uspec_def h1 h2 h3 rep_abs_uspec)
qed

  
lemma assumes "finite In" shows"cont (\<lambda> h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in> inv Rev (spsStep_h\<cdot>h)} In Out)"
proof(rule Cont.contI2,simp add: assms)
  fix Y::"nat \<Rightarrow> 'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i::nat. Abs_rev_uspec {spfStep In Out\<cdot>g |g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>(Y i))} In Out)"
  have a3:"chain (\<lambda>i::nat. setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))"
    by (metis (mono_tags, lifting) a1 fun_below_iff monofun_cfun_arg po_class.chain_def)
  have a4:"chain (\<lambda>i::nat. Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))})"
      apply(simp add: spsStep_h_insert)
    by (smt Collect_mono SetPcpo.less_set_def a3 below_rev.elims(2) below_rev.simps inv_rev_rev po_class.chain_def subsetCE)
  have h1:"\<forall>i. uspecWell (Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}) (Discr In) (Discr Out)"
    by (smt finite mem_Collect_eq spfstep_dom spfstep_ran ufclDom_ufun_def ufclRan_ufun_def uspecWell.simps assms)
  have h2:"uspecWell (Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (\<Squnion>i::nat. spsStep_h\<cdot>(Y i))}) (Discr In) (Discr Out)"
    by (smt finite mem_Collect_eq spfstep_dom spfstep_ran ufclDom_ufun_def ufclRan_ufun_def uspecWell.simps assms)
  have h3:"Rep_uspec (Abs_uspec (\<Squnion>i. (Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}, Discr In, Discr Out)))
        =  (\<Squnion>i::nat. (Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}, Discr In, Discr Out))"
    by (metis (mono_tags, lifting) a2 cont2contlubE h1 lub_eq lub_uspec rep_abs_uspec uspec_rep_cont)
  have h4:"(\<Squnion>i. (Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}, Discr In, Discr Out))
           = ((\<Squnion>i. Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}), Discr In, Discr Out)"
    by(simp add: lub_in a4)
  have h5:"\<And>x. \<forall>i. x \<in> {spfStep In Out\<cdot>f |f. \<forall>m. f m \<in> Rep_rev_uspec (Y i m)}
           \<Longrightarrow> \<exists>g.
          x = spfStep In Out\<cdot>g \<and> (\<forall>i. g \<in> {f. \<forall>m. f m \<in> Rep_rev_uspec (Y i m)})"
  proof auto
    fix x::"('a stream\<^sup>\<Omega>) ufun"
    show"\<forall>i. \<exists>f. x = spfStep In Out\<cdot>f \<and> (\<forall>m. f m \<in> Rep_rev_uspec (Y i m)) \<Longrightarrow>
         \<exists>g. x = spfStep In Out\<cdot>g \<and> (\<forall>i m::'a sbElem. g m \<in> Rep_rev_uspec (Y i m))"
    proof-
      assume aa1:"\<forall>i. \<exists>f. x = spfStep In Out\<cdot>f \<and> (\<forall>m. f m \<in> Rep_rev_uspec (Y i m))"
      have h1: "\<And>f e. x = spfStep In Out\<cdot>f \<Longrightarrow> \<exists>sb. f e \<rightleftharpoons> sb = x \<rightleftharpoons> sb"
      proof(simp add: spfStep_2_spfStep_inj spfStep_inj_def)
        fix e::"'a sbElem" and f::"'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun"
        assume aa2:"x = spfStep In Out\<cdot>f"
        obtain sb where sb_def:"Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)) = e \<and> sbHdElemWell sb"
          by (metis sbElem_surj)
        have "ufRestrict In Out\<cdot>(f e) \<rightleftharpoons> sb = (f e) \<rightleftharpoons> sb"
          sorry
        then have"(sbHdElemWell sb \<longrightarrow> f e \<rightleftharpoons> sb = ufRestrict In Out\<cdot>(f (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb)))) \<rightleftharpoons> sb) \<and> (\<not> sbHdElemWell sb \<longrightarrow> f e \<rightleftharpoons> sb = ufLeast In Out \<rightleftharpoons> sb)"
          by (simp add: sb_def)
        then show "\<exists>sb::'a stream\<^sup>\<Omega>. f e \<rightleftharpoons> sb = spfStep In Out\<cdot>f \<rightleftharpoons> sb"
          by (metis assms spfStep_2_spfStep_inj spfStep_inj_def)
      qed  
      show "\<exists>g. x = spfStep In Out\<cdot>g \<and> (\<forall>i m. g m \<in> Rep_rev_uspec (Y i m))"
      proof-
        obtain g where g_def:"\<forall>sb. x \<rightleftharpoons> sb = g (Abs_sbElem (inv convDiscrUp (sbHdElem\<cdot>sb))) \<rightleftharpoons> sb"
          sorry
        show"\<exists>g::'a sbElem \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. x = spfStep In Out\<cdot>g \<and> (\<forall>(i::nat) m::'a sbElem. g m \<in> Rep_rev_uspec (Y i m))"
          sorry
      qed
    qed
  qed
  show "Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(\<Squnion>i::nat. Y i))} In Out \<sqsubseteq>
       (\<Squnion>i::nat. Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))} In Out)"
    apply(simp add: a1 contlub_cfun_fun contlub_cfun_arg)
    apply(simp add: below_uspec_def)
    apply(simp only: h2 rep_abs_uspec)
    apply(simp add: lub_uspec a2)
    apply(simp only: h1 rep_abs_uspec h3)
    apply(simp add: h4)
    apply(subst setrevLubEqInterII, simp add: a1)
    apply(subst setrevLubEqInter, simp add: a4)
    apply(simp add: spsStep_h_insert setify_def uspecRevSet_def inv_rev_rev rev_inv_rev less_set_def)
    apply auto
    using h5
    by (metis (mono_tags))
qed
  

(*
lemma spsStep_mono[simp]:"monofun (\<lambda>h::(channel \<Rightarrow> 'a::message option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec. Abs_rev_uspec {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h)} In Out)"


lemma spsStep_mono[simp]:assumes "finite In" shows"monofun (\<lambda>h::(channel \<Rightarrow> 'a::message option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun uspec. Abs_rev_uspec {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h)} In Out)"

proof(rule monofunI)
  fix x y::"(channel \<Rightarrow> 'm::message option) \<Rightarrow> 'm SPS" 
  assume a1: "x \<sqsubseteq> y"
  have "(spsStep_h\<cdot>x) \<sqsubseteq> (spsStep_h\<cdot>y)" 
    by (simp add: a1 monofun_cfun_arg)
  then have "inv Rev(spsStep_h\<cdot>y) \<subseteq> inv Rev (spsStep_h\<cdot>x)"
    by (metis (full_types) SetPcpo.less_set_def below_rev.elims(2) inv_rev_rev)
  then have "\<And>g. g \<in> inv Rev(spsStep_h\<cdot>y) \<Longrightarrow> g \<in> inv Rev (spsStep_h\<cdot>x)"
    by blast
  then have h1:"{spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>y)} \<sqsubseteq>{spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>x)}"
    by (smt Collect_mono SetPcpo.less_set_def)
  have h2:"\<And>g. ufclDom\<cdot>(spfStep In Out\<cdot>g) = In"
    by (simp add: ufclDom_ufun_def assms)
  have h3:"\<And>g. ufclRan\<cdot>(spfStep In Out\<cdot>g) = Out"
    by (simp add: ufclRan_ufun_def assms)
  have h4:"\<And>f h. f\<in>{spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'm option) \<Rightarrow> ('m stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>h)} \<Longrightarrow> \<exists>g. f = spfStep In Out\<cdot>g"
    by auto
  have h2:"uspecWell (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'm option) \<Rightarrow> ('m stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>x)}) (Discr In) (Discr Out)"
    using h2 h3 by auto
  have h3:"uspecWell (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'm option) \<Rightarrow> ('m stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>y)}) (Discr In) (Discr Out)"
    by (metis (no_types, lifting) SetPcpo.less_set_def h1 h2 subsetCE uspecWell.simps)
  show "Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>x)} In  Out\<sqsubseteq>
       Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>y)} In Out"
    by (metis (no_types, lifting) Pair_below_iff below_refl below_rev.simps below_uspec_def h1 h2 h3 rep_abs_uspec)
qed
 
lemma uspec_lub_insert:assumes "chain (Y::nat \<Rightarrow> 'm::ufuncl set rev)" shows "(\<Squnion>i. (Y i, Discr In, Discr Out)) = ((\<Squnion>i. Y i), Discr In, Discr Out)"
  sorry

lemma spsStep_cont[simp]:assumes "finite In" shows"cont (\<lambda>h. Abs_rev_uspec {spfStep In Out\<cdot>g | g. g \<in>inv Rev (spsStep_h\<cdot>h)} In Out)"
proof(rule Cont.contI2, simp add: assms)
  fix Y::"nat \<Rightarrow> ((channel \<Rightarrow> 'a option) \<Rightarrow> 'a SPS)"
  assume a1:"chain Y"
  assume a2:"chain (\<lambda>i. Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))} In Out)"
  have a3:"chain (\<lambda>i::nat. setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))"
    by (metis (mono_tags, lifting) a1 fun_below_iff monofun_cfun_arg po_class.chain_def)
  have a4:"chain (\<lambda>i::nat. Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))})"
    by (smt Collect_mono SetPcpo.less_set_def a3 below_rev.elims(2) below_rev.simps inv_rev_rev po_class.chain_def subsetCE)
  have h1:"\<forall>i. uspecWell (Rev {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}) (Discr In) (Discr Out)"
    by (smt finite mem_Collect_eq spfstep_dom spfstep_ran ufclDom_ufun_def ufclRan_ufun_def uspecWell.simps assms)
  have h2:"uspecWell (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (\<Squnion>i::nat. spsStep_h\<cdot>(Y i))}) (Discr In) (Discr Out)"
    by (smt finite mem_Collect_eq spfstep_dom spfstep_ran ufclDom_ufun_def ufclRan_ufun_def uspecWell.simps assms)
  have h3:"Rep_uspec (Abs_uspec (\<Squnion>i::nat. (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}, Discr In, Discr Out)))
        =  (\<Squnion>i::nat. (Rev {spfStep In Out\<cdot>g |g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. g \<in> inv Rev (spsStep_h\<cdot>(Y i))}, Discr In, Discr Out))"
    by (metis (mono_tags, lifting) a2 cont2contlubE h1 lub_eq lub_uspec rep_abs_uspec uspec_rep_cont)
  have h4:"\<And>x.
       \<forall>xa.
          (\<exists>i. xa = {spfStep In Out\<cdot>g |g. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))}) \<longrightarrow> x \<in> xa \<Longrightarrow>
       \<exists>g. x = spfStep In Out\<cdot>g \<and>
          (\<forall>x. (\<exists>i. x = inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))) \<longrightarrow> g \<in> x)"
  proof-
    fix x::"'a SPF"
    have h1:"(\<forall>xa.
          (\<exists>i. xa = {spfStep In Out\<cdot>g |g. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))}) \<longrightarrow> x \<in> xa) = (\<forall>i. x\<in>{spfStep In Out\<cdot>g |g. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))})"
      by auto
    have h2:"(\<exists>g. x = spfStep In Out\<cdot>g \<and> (\<forall>x. (\<exists>i. x = inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))) \<longrightarrow> g \<in> x)) = (\<exists>g. x = spfStep In Out\<cdot>g \<and> (\<forall>i. g\<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))))"
      by auto
    have "(\<forall>i. \<exists>g.  (\<forall>m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g) =  (\<exists>g.\<forall>i.  (\<forall>m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g)"
    proof(auto)
      assume a1:"\<forall>i::nat. \<exists>g::(channel \<Rightarrow> 'a option) \<Rightarrow> ('a stream\<^sup>\<Omega>) ufun. (\<forall>m::channel \<Rightarrow> 'a option. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g"
      obtain g where g_def:"\<exists>i. (\<forall>m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g"
        using a1 by blast(*
      have problem:"\<And>u w x. ufRestrict In Out\<cdot>(u x) = (u x) \<Longrightarrow> ufRestrict In Out\<cdot>(w x) = (w x) \<Longrightarrow>  spfStep In Out\<cdot>u = spfStep In Out\<cdot>w \<Longrightarrow> u=w"
        sorry*)
      have h1:"(\<forall>i m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g"
      proof(cases "\<exists>i m. uspecDom\<cdot>(Y i m) \<noteq>In \<or> uspecRan\<cdot>(Y i m) \<noteq>Out")
        case True
        then show ?thesis sorry
      next
        case False
        then show ?thesis sorry
      qed
      then show "\<exists>g. (\<forall>i m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g"
        by blast
    qed
    then have h3_h:"\<forall>i. \<exists>g.  (\<forall>m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g \<Longrightarrow>
    \<exists>g.  (\<forall>i m. g m \<in> Rep_rev_uspec (Y i m)) \<and> x = spfStep In Out\<cdot>g"
      by simp
    have h3:"\<forall>i. \<exists>g. x = spfStep In Out\<cdot>g \<and> g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e))) \<Longrightarrow>
    \<exists>g. x = spfStep In Out\<cdot>g \<and> (\<forall>i. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e))))"
      apply(simp add: setify_def inv_rev_rev uspecrevset_insert) using h3_h by blast
    show"\<forall>xa.
          (\<exists>i. xa = {spfStep In Out\<cdot>g |g. g \<in> inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))}) \<longrightarrow> x \<in> xa \<Longrightarrow>
       \<exists>g.
          x = spfStep In Out\<cdot>g \<and>
          (\<forall>x. (\<exists>i. x = inv Rev (setify\<cdot>(\<lambda>e. uspecRevSet\<cdot>(Y i e)))) \<longrightarrow> g \<in> x)"
    by(simp add: h1 h2 h3)
  qed
  show "Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(\<Squnion>i. Y i))} In Out \<sqsubseteq>
       (\<Squnion>i. Abs_rev_uspec {spfStep In Out\<cdot>g |g. g \<in> inv Rev (spsStep_h\<cdot>(Y i))} In Out)"
    apply(simp add: a1 contlub_cfun_fun contlub_cfun_arg)
    apply(simp add: below_uspec_def)
    apply(simp only: h2 rep_abs_uspec)
    apply(simp add: lub_uspec a2)
    apply(simp only: h1 rep_abs_uspec h3)
    apply(simp add: a1 spsStep_h_insert)
    apply(simp add: setrevLubEqInterII a3)
    apply(simp add: uspec_lub_insert setrevLubEqInter a4)
    apply(simp add: less_set_def inv_rev_rev rev_inv_rev)
    apply auto
    by(simp add: h4)
qed*)
  
end
  