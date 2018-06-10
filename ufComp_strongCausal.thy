theory ufComp_strongCausal
  imports UFun_Comp UBundle_Pcpo
begin

(* setup_lifting type_definition_ufun
setup_lifting type_definition_ubundle *)

(* default_sort uscl *)
 default_sort uscl_pcpo 
(* default_sort ubcl *)
(* default_sort ubcl_comp *)

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]


lemma ufComp_strongCausal: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" and "ufIsStrong f1" and "ufIsStrong f2"
  shows "ufIsStrong (ufComp f1 (f2::'m ubundle ufun))"
  apply (simp add: ufIsStrong_def ufComp_def ubclLen_ubundle_def)
  apply rule+
proof -

  fix b::"'m ubundle"
  assume a0: "b \<in> dom (Rep_cufun (Abs_cufun (\<lambda>x . (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))"

  have z2: "ufWell (\<Lambda>(x::'m\<^sup>\<Omega>). (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
    apply (rule ufun_wellI)
    apply (simp_all  )
    apply (simp_all add: domIff2)
    apply (simp_all add: ubclDom_ubundle_def)
    apply auto

    sorry

  have y98: "b \<in> dom (\<lambda>u. (ubclDom\<cdot>u = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 u) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
    using a0 z2 by auto
  have y99: "ubDom\<cdot>b = ufCompI f1 f2"
    using  y98 by (simp add: domIff2 ubclDom_ubundle_def)
  have chain_def: "chain (\<lambda>a::nat. iter_ubfix2 (ufCompH f1 f2) a (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)"
    by (simp add: ubclDom_ubundle_def y99)

  have y0: "ubLen (iter_ubfix2 (ufCompH f1 f2) 0 (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) = Fin 0"
    apply (simp add: ufCompH_def ubclLeast_ubundle_def)
    apply (simp add: ubLeast_def)

      sorry    (*wird (noch?) nicht genutzt*)

  have y1: "chain (\<lambda>i. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
    using ch2ch_monofun local.chain_def ublen_monofun by auto

  have y2: "\<And>i. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) < lnsuc\<cdot>(ubLen b) \<Longrightarrow> 
    ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<ge> lnsuc\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
    proof -
      fix i
      assume y21: "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) < lnsuc\<cdot>(ubLen b)"

      have minOr: "\<And> x y. lnmin\<cdot>x\<cdot>y = x \<or> lnmin\<cdot>x\<cdot>y = y"
        sorry (*siehe TStream.thy, muss noch nach lnat*)
      have sucmin_minsuc: "\<And> x y . lnsuc\<cdot>(lnmin\<cdot>x\<cdot>y) = lnmin\<cdot>(lnsuc\<cdot>x)\<cdot>(lnsuc\<cdot>y)"
        by simp

      have y22: "lnmin\<cdot>(ubLen b)\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) = (ubLen b) \<or>
                 lnmin\<cdot>(ubLen b)\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) = (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
        by (simp add: minOr)

      have y23: "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) = lnmin\<cdot>(ubLen b)\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
        apply (case_tac "(ubLen b) = \<infinity>")
        apply simp
        proof -
          have "lnmin\<cdot>(ubLen b) \<sqsubseteq> lnmin\<cdot>\<infinity>"
            by (meson inf_ub lnle_def monofun_cfun_arg)
          then show ?thesis
            by (metis (no_types) leD lnle2le lnless_def lnmin_fst_inf monofun_cfun_fun y21 y22)
        qed
  
        have a2:  "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<le> ubLen ((f1 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) \<uplus> (f2 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)))"
           (* ISAR proof aus remote_vampire ! *)
         proof -
           obtain nn :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" where
             "\<forall>f. (chain f \<or> f (nn f) \<notsqsubseteq> f (Suc (nn f))) \<and> ((\<forall>n. f n \<sqsubseteq> f (Suc n)) \<or> \<not> chain f)"
             by (metis (no_types) po_class.chain_def)
           then have "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<le> ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)"
             by (metis lnle_def y1)
           then show ?thesis
             by (simp add: ufcomph_insert)
         qed

         have a3: "(ubLen (iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))) \<le> ubLen ((f1 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))
\<uplus> (f2 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))))"
           using a2 by (simp add: a2 ufCompH_def)

         have a4: " (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) < ubLen b\<Longrightarrow>
lnsuc\<cdot>(ubLen (iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))) \<le> ubLen ((f1 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))
\<uplus> (f2 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))))"
         proof-
           assume a41: "(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) < ubLen b"
           then show "lnsuc\<cdot>(ubLen (iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))) \<le> ubLen ((f1 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))
\<uplus> (f2 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))))"
             
           sorry
       qed
       have y25: "lnmin\<cdot>(lnsuc\<cdot>(ubLen b))\<cdot>(lnsuc\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) = lnsuc\<cdot>(ubLen b) \<or>
lnmin\<cdot>(lnsuc\<cdot>(ubLen b))\<cdot>(lnsuc\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) = (lnsuc\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)))"
        using minOr by blast

      have y99: "(lnmin\<cdot>(lnsuc\<cdot>(ubLen b))\<cdot>(lnsuc\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) \<le> ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)
  = ((lnsuc\<cdot>(ubLen b)) \<le> ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) \<or>
(lnmin\<cdot>(lnsuc\<cdot>(ubLen b))\<cdot>(lnsuc\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) \<le> ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)
 = ((lnsuc\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)))\<le> ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)))"
        using y25 by auto


(*      have y98: "(lnsuc\<cdot>(ubLen b)) \<le> ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<or> 
               (lnsuc\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)))\<le> ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)"
        
        apply auto
        apply (case_tac "(ubLen b) = \<infinity>")
        
        sorry *)

(*         have z1: "ubLen (f1 \<rightleftharpoons> ((b \<uplus> (iterate i\<cdot>((\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> ((b \<uplus> z) \<bar> (ufDom\<cdot>f1))) \<uplus> (f2 \<rightleftharpoons> ((b \<uplus> z)\<bar>(ufDom\<cdot>f2))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))) \<bar> ufDom\<cdot>f1)))
                 (*      \<ge> lnsuc\<cdot>(ubLen (iterate i\<cdot>((\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> ((b \<uplus> z) \<bar> (ufDom\<cdot>f1))) \<uplus> (f2 \<rightleftharpoons> ((b \<uplus> z)\<bar>(ufDom\<cdot>f2))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))) *)"
          sorry *)

(*         have test: "\<And> x (y::'m\<^sup>\<Omega>). ubLen (x \<uplus> y) = ubLen x \<or> ubLen (x \<uplus> y) = ubLen y"
      proof - 
        fix x y
        show "ubLen (x \<uplus> y) = ubLen x \<or> ubLen (x \<uplus> y) = ubLen y"
        proof (cases "ubLen x = \<infinity> \<or> ubLen y = \<infinity>")
          case True
          then show ?thesis sorry
        next
          case False
          then show ?thesis  sorry
        qed
 *)
         have zz1: "ubLen (f1 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))
\<ge> lnsuc\<cdot>(ubLen (iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))"
           apply (simp add: ubclUnion_ubundle_def ubclLeast_ubundle_def)
           
           sorry

         have zz2: "ubLen (f2 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))
 \<ge> lnsuc\<cdot>(ubLen (iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))"

           sorry

         have zz3: "\<And> (z::'m\<^sup>\<Omega>) zz . ubLen (z \<uplus> zz) = ubLen z \<or> ubLen (z \<uplus> zz) = ubLen zz"
         proof -
           fix z zz
           show "ubLen (z \<uplus> zz) = ubLen z \<or> ubLen (z \<uplus> zz) = ubLen zz"
           proof -
             obtain  n::nat where zz31: "Fin n = ubLen z" sorry
             obtain nn::nat where zz32: "Fin n = ubLen zz" sorry
             show ?thesis
      proof (cases "ubLen z = \<infinity> \<or> ubLen zz = \<infinity>")
          case True
          then show ?thesis
            using zz31 zz32 by auto
        next
          case False
          then show ?thesis  
            sorry
        qed
           qed
         qed

         have zz11: "ubLen ((f1 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))) \<uplus> (f2 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))))
\<ge> lnsuc\<cdot>(ubLen ((iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))\<uplus>(iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))))"
           by (smt zz1 zz2 zz3) (*isar proof available*)

(*          have zz12: "(lnsuc\<cdot>(ubLen b)) \<le> ubLen ((f1 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))
\<uplus> (f2 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))))"
            sledgehammer
           sorry  *)
       

     show "ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<ge> lnsuc\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"

      apply (subst y23)
      apply (simp add: ufCompH_def)

      apply (simp only: sucmin_minsuc)
      
       using zz1 zz2 zz3 zz11        

      sorry (*austimende proofs gefunden*)
    qed

  have y3: "\<And>i. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<ge> lnsuc\<cdot>(ubLen b) \<Longrightarrow> 
  ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<ge> ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)"
    using y1 assms by (meson lnle_def po_class.chain_def)

  have z98: "ubLen (\<Squnion>i::nat. iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) 
          = (\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"

    sorry

  have z99: "lnsuc\<cdot>(ubLen b) \<le> (\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
    proof (cases "ubLen b = \<infinity>")
      case True
      have "\<And>i.  ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<ge> lnsuc\<cdot>( ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
        by (metis True fold_inf inf_ub less_le y2 y3)
      then have "(\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) = \<infinity>"
        by (metis (mono_tags, lifting) y1 inf_less_eq is_ub_thelub l42 le2lnle leI less_irrefl po_class.chainE po_eq_conv unique_inf_lub)
      then show ?thesis
        by (metis True fold_inf lnat_po_eq_conv)
    next
      case False
      obtain n where z991: "Fin n = ubLen b" by (metis False infI)
  
      have "lnsuc\<cdot>(Fin n) \<le> (\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
         proof -
          obtain nn :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" where
            f1: "\<forall>f. (\<not> chain f \<or> \<not> finite_chain f) \<or> Lub f = f (nn f)"
            by (metis l42)
          have "\<forall>f. \<not> chain f \<or> finite_chain f \<or> Lub f = \<infinity>"
            by (metis (full_types) unique_inf_lub)
          then have f2: "(\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) \<noteq> \<infinity> \<longrightarrow> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) = ubLen (iter_ubfix2 (ufCompH f1 f2) (nn (\<lambda>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)"
            using f1 y1 by blast
          have f3: "ubLen (iter_ubfix2 (ufCompH f1 f2) (nn (\<lambda>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<sqsubseteq> ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc (nn (\<lambda>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)"
            using po_class.chainE y1 by blast
          have "ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc (nn (\<lambda>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<sqsubseteq> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
            using is_ub_thelub y1 by blast
        then show ?thesis
          using f3 f2 by (metis inf_less_eq inf_ub le2lnle less_irrefl not_le_imp_less po_eq_conv y2 z991)
        qed
    thus ?thesis 
      by (simp add: z991)
    qed

  show "lnsuc\<cdot>(ubLen b) \<le> ubLen (Abs_cufun (\<lambda>x::'m\<^sup>\<Omega>. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)) \<rightleftharpoons> b)"
    apply (simp add: z2)
    apply (simp add: ubclDom_ubundle_def)
    apply (simp_all add: assms y99)
    apply (simp add: ubFix_def)
    by (simp add: z98 z99)
qed