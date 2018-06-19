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
lemma minOr: "\<And> x y. lnmin\<cdot>x\<cdot>y = x \<or> lnmin\<cdot>x\<cdot>y = y"
    sorry (*siehe TStream.thy, muss noch nach lnat*)

lemma test: assumes " ufIsStrong f" and "ubDom\<cdot>x \<noteq> {}" shows "\<And> (f :: 'a ufun) (x :: 'a\<^sup>\<Omega>) . ubLen (f x) \<ge> lnsuc\<cdot>(ubLen x)"


lemma z1: "\<And> (z::'a\<^sup>\<Omega>) zz . ubLen (z \<uplus> zz) = ubLen z \<or> ubLen (z \<uplus> zz) = ubLen zz"
proof (simp add: ubclUnion_ubundle_def)
  fix z zz
  obtain ln1 where "ln1 = ubLen (z::'a\<^sup>\<Omega>)"
    by simp
  obtain ln2 where "ln2 = ubLen (zz::'a\<^sup>\<Omega>)"
    by simp
  have test1: "ln1 < ln2 \<Longrightarrow> ubLen (ubUnion\<cdot>(z::'a\<^sup>\<Omega>)\<cdot>zz) = ubLen zz"
    apply (simp add: ubLen_def)
    apply rule

(*     using usclLen_stream_def / tstream apply simp *)
    sorry
  show "ubLen (ubUnion\<cdot>z\<cdot>zz) = ubLen z \<or> ubLen (ubUnion\<cdot>z\<cdot>zz) = ubLen zz"
  proof (cases "ln1 = \<infinity> \<or> ln2 = \<infinity>")
    case True
    show ?thesis
      using assms
      sorry
  next
    case False
    obtain n1 where "Fin n1 = ln1"
      using False lncases by auto
    obtain n2 where "Fin n2 = ln2"
      using False lncases by auto

    show ?thesis
    proof (cases "n1 < n2")
      case True
      then show ?thesis  sorry
    next
      case False
      then show ?thesis   sorry
    qed
      
  qed
qed

lemma f1: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" and "ufIsStrong f1" and "ufIsStrong f2" and "ubLen b > ubLen ub" and "ubDom\<cdot>b = ufCompI f1 f2" and "ubDom\<cdot>ub = ufCompL f1 f2"
  shows "lnsuc\<cdot>(ubLen ub) \<le> ubLen ((ufCompH f1 f2) b\<cdot>ub)"
proof -
  fix b ub ::"'a ubundle"

  have testf1: "\<forall>u ua ub. ua \<rightleftharpoons> Abs_ubundle (Rep_ubundle ((ub::'a\<^sup>\<Omega>) \<uplus> u) |` ufDom\<cdot>ua) = ufFeedH ua ub\<cdot>u"
    by (simp add: ubclRestrict_ubundle_def ubrestrict_insert ufFeedH_insert)
  have testf2: "\<infinity> = ubclLen (ubclLeast {}::'a\<^sup>\<Omega>)"
    by (simp add: ubLen_def ubclLeast_ubundle_def ubclLen_ubundle_def)
  have testf3: "\<forall>u ua ub. ub \<rightleftharpoons> Abs_ubundle (Rep_ubundle (Abs_ubundle (Rep_ubundle (u::'a\<^sup>\<Omega>) ++ Rep_ubundle ua)) |` ufDom\<cdot>ub) = ufFeedH ub u\<cdot>ua"
    by (metis (full_types) testf1 ubclUnion_ubundle_def ubunion_insert)
  have testf4: "\<forall>u. ubRestrict UNIV\<cdot>(u::'a\<^sup>\<Omega>) = u"
    by simp
  have testf5: "\<forall>u. ubDom\<cdot>(ubRestrict {}\<cdot>(u::'a\<^sup>\<Omega>)) = {}"
    by (meson bot.extremum_uniqueI ubrestrict_ubdom)
  have testf6: "\<forall>u. ubLen (ubRestrict {}\<cdot>(u::'a\<^sup>\<Omega>)) = \<infinity>"
    by (simp add: ubLen_def)
(*   assume a1: "ubDom\<cdot>b \<noteq> {}" *)
  (* fix ub::"'a::uscl_pcpo\<^sup>\<Omega>" *)
(*   assume a1: "ubLen b = \<infinity>" *)

(*   obtain n :: lnat where "n = ubLen b"
    by simp
  obtain nn :: lnat where "nn = ubLen ub"
    by simp
  obtain nnn :: lnat where "nnn = ubLen ((ufCompH f1 f2) b\<cdot>ub)"
    by simp
  have n1: "nn \<noteq> \<infinity>"
    using \<open>(nn::lnat) = ubLen (ub::'a::uscl_pcpo\<^sup>\<Omega>)\<close> assms(4) by auto
  have n2: "lnsuc\<cdot>nn \<noteq> \<infinity>"
    by (simp add: n1) *)


(*
"ubLen b \<equiv> if ubDom\<cdot>b \<noteq> {} then (LEAST ln. ln\<in>{(usclLen\<cdot>(b . c)) | c. c \<in> ubDom\<cdot>b}) else \<infinity>"  
*)


  have f10: "ubDom\<cdot>(ubUnion\<cdot>b\<cdot>ub) = ubDom\<cdot>b \<union> ubDom\<cdot>ub"
    using ubunionDom by blast

  have f11: "ubLen ( b \<uplus> ub) = ubLen ub"
    apply (simp add: ubclUnion_ubundle_def)
    apply (simp add: ubLen_def)
proof (cases "ubDom\<cdot>b = {}")
  case True
  then show " ubDom\<cdot>b \<noteq> {} \<longrightarrow>
    (ubDom\<cdot>ub \<noteq> {} \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(ubUnion\<cdot>b\<cdot>ub  .  c) \<and> (c \<in> ubDom\<cdot>b \<or> c \<in> ubDom\<cdot>ub)) = (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(ub  .  c) \<and> c \<in> ubDom\<cdot>ub)) \<and>
    (ubDom\<cdot>ub = {} \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(b  .  c) \<and> c \<in> ubDom\<cdot>b) = \<infinity>)"
    by simp
next
  case False
  then show " ubDom\<cdot>b \<noteq> {} \<longrightarrow>
    (ubDom\<cdot>ub \<noteq> {} \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(ubUnion\<cdot>b\<cdot>ub  .  c) \<and> (c \<in> ubDom\<cdot>b \<or> c \<in> ubDom\<cdot>ub)) = (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(ub  .  c) \<and> c \<in> ubDom\<cdot>ub)) \<and>
    (ubDom\<cdot>ub = {} \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(b  .  c) \<and> c \<in> ubDom\<cdot>b) = \<infinity>)"
    apply simp
  proof (cases "ubDom\<cdot>ub = {}")
    case True
    have c1: "\<nexists> (c::channel) . (c \<in> ubDom\<cdot>ub)"
      by (simp add: True)
    have c2: "\<exists> c::channel . c \<in> ubDom\<cdot>b \<and> usclLen\<cdot>(b  .  c) < \<infinity> \<Longrightarrow>  ubDom\<cdot>ub \<noteq> {}"
      apply (simp add: True) (*? ? ?*)

      using assms True False

      sorry
    have c3: "\<forall> c::channel . c \<in> ubDom\<cdot>b \<longrightarrow> usclLen\<cdot>(b  .  c) = \<infinity>"
      using True c2 inf_ub less_le by blast
    have f0: "\<forall>u. (\<exists>c. (LEAST l. l \<in> {usclLen\<cdot>(u . c::'a) |c. c \<in> ubDom\<cdot>u}) = usclLen\<cdot>(u . c) \<and> c \<in> ubDom\<cdot>u) \<or> {} = ubDom\<cdot>u"
      using  ublen_min_on_channel by (metis (mono_tags, lifting))
    then obtain cc :: "'a\<^sup>\<Omega> \<Rightarrow> channel" where
      f1: "\<forall>u. (LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u}) = usclLen\<cdot>(u . cc u) \<and> cc u \<in> ubDom\<cdot>u \<or> {} = ubDom\<cdot>u"
      by moura
    show "(ubDom\<cdot>ub \<noteq> {} \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(ubUnion\<cdot>b\<cdot>ub  .  c) \<and> (c \<in> ubDom\<cdot>b \<or> c \<in> ubDom\<cdot>ub)) = (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(ub  .  c) \<and> c \<in> ubDom\<cdot>ub)) \<and> (ubDom\<cdot>ub = {} \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(b  .  c) \<and> c \<in> ubDom\<cdot>b) = \<infinity>)"
      apply (simp add: True)
      using False f1 f0  c3 by fastforce
  next
    case False
    have c1: "\<exists> c . c \<in> ubDom\<cdot>ub \<longrightarrow> c \<in> ubDom\<cdot>(ubUnion\<cdot>b\<cdot>ub)"
      by simp
    show "(ubDom\<cdot>ub \<noteq> {} \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(ubUnion\<cdot>b\<cdot>ub  .  c) \<and> (c \<in> ubDom\<cdot>b \<or> c \<in> ubDom\<cdot>ub)) = (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(ub  .  c) \<and> c \<in> ubDom\<cdot>ub)) \<and> (ubDom\<cdot>ub = {} \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(b  .  c) \<and> c \<in> ubDom\<cdot>b) = \<infinity>)"
      apply (simp add: False)
      apply (simp add: ubUnion_def)

      using c1 False assms ubunionDom
      
      sorry
  qed
qed

  have f121: "\<And> x . \<exists>c::channel. ubLen x = ubLen (ubRestrict {c}\<cdot>x)"
  proof -
    fix x
    show "\<exists>c::channel. ubLen x = ubLen (ubRestrict {c}\<cdot>x)"
      apply (simp add: ubLen_def)
      apply rule
      proof (cases "ubDom\<cdot>x = {}")
        case True
        then show "ubDom\<cdot>x \<noteq> {} \<Longrightarrow> \<exists>c::channel. (c \<in> ubDom\<cdot>x \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(x  .  c) \<and> c \<in> ubDom\<cdot>x) = (LEAST ln::lnat. ln = usclLen\<cdot>(x  .  c))) \<and> (c \<notin> ubDom\<cdot>x \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(x  .  c) \<and> c \<in> ubDom\<cdot>x) = \<infinity>)"
          by simp
      next
        case False
        then show "ubDom\<cdot>x \<noteq> {} \<Longrightarrow> \<exists>c::channel. (c \<in> ubDom\<cdot>x \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(x  .  c) \<and> c \<in> ubDom\<cdot>x) = (LEAST ln::lnat. ln = usclLen\<cdot>(x  .  c))) \<and> (c \<notin> ubDom\<cdot>x \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(x  .  c) \<and> c \<in> ubDom\<cdot>x) = \<infinity>)"
          apply (simp add: False)
          proof (cases "c\<in> ubDom\<cdot>x")
            case True
            then show "\<exists>c::channel. (c \<in> ubDom\<cdot>x \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(x  .  c) \<and> c \<in> ubDom\<cdot>x) = (LEAST ln::lnat. ln = usclLen\<cdot>(x  .  c))) \<and> (c \<notin> ubDom\<cdot>x \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(x  .  c) \<and> c \<in> ubDom\<cdot>x) = \<infinity>)"
              apply (simp add: True)
              sorry
          next
            case False
            then show "\<exists>c::channel. (c \<in> ubDom\<cdot>x \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(x  .  c) \<and> c \<in> ubDom\<cdot>x) = (LEAST ln::lnat. ln = usclLen\<cdot>(x  .  c))) \<and> (c \<notin> ubDom\<cdot>x \<longrightarrow> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(x  .  c) \<and> c \<in> ubDom\<cdot>x) = \<infinity>)"
              apply (simp add: False)
              sorry
          qed
      qed
  qed

  have f122: "\<And> (x::'a\<^sup>\<Omega>) cs . ubDom\<cdot>x \<noteq> {} \<longrightarrow> ubLen (ubRestrict cs\<cdot>x) \<ge> ubLen x"
    apply rule
  proof -
    fix x cs
    assume a1: "ubDom\<cdot>x \<noteq> {}"
    show "ubLen (ubRestrict cs\<cdot>x) \<ge> ubLen x"
      apply (simp add: ubLen_def a1)
      apply rule+

      sorry
  qed

  have f12: "ubLen (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub)) \<ge> ubLen ( b \<uplus> ub)"
    apply (simp add: ubclRestrict_ubundle_def ubclUnion_ubundle_def)
    by (metis (mono_tags, hide_lams) inf_bot_left inf_ub ubLen_def ubrestrict_ubdom2 f122)


  have f13: "ubLen (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub)) \<ge> ubLen ub"
    using f11 f12 by auto

  have f141: "\<And> f (x :: 'a\<^sup>\<Omega>) . ubDom\<cdot>x \<noteq> {} \<longrightarrow> ufIsStrong  f \<longrightarrow>  ubLen (f\<rightleftharpoons>x) \<ge> lnsuc\<cdot>(ubLen x)"
  proof -
    fix f 
    fix x
    show "ubDom\<cdot>x \<noteq> {} \<longrightarrow> ufIsStrong  f \<longrightarrow>  ubLen (f\<rightleftharpoons>x) \<ge> lnsuc\<cdot>(ubLen x)"
      apply rule+
    proof -
      assume a1: "ubDom\<cdot>x \<noteq> {}"
      assume a2: "ufIsStrong  f"
      show "ubDom\<cdot>x \<noteq> {} \<Longrightarrow> ufIsStrong f \<Longrightarrow> lnsuc\<cdot>(ubLen x) \<le> ubLen (f \<rightleftharpoons> x)"
        apply (simp add: a1 a2)
        apply (simp add: ubLen_def a1)
        apply rule
        proof (cases "ubDom\<cdot>(f \<rightleftharpoons> x) = {}")
          case True
          then show "ubDom\<cdot>(f \<rightleftharpoons> x) \<noteq> {} \<Longrightarrow> lnsuc\<cdot>(LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(x  .  c) \<and> c \<in> ubDom\<cdot>x) \<le> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>((f \<rightleftharpoons> x)  .  c) \<and> c \<in> ubDom\<cdot>(f \<rightleftharpoons> x))"
            by simp
        next
          case False
          then show "ubDom\<cdot>(f \<rightleftharpoons> x) \<noteq> {} \<Longrightarrow> lnsuc\<cdot>(LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>(x  .  c) \<and> c \<in> ubDom\<cdot>x) \<le> (LEAST ln::lnat. \<exists>c::channel. ln = usclLen\<cdot>((f \<rightleftharpoons> x)  .  c) \<and> c \<in> ubDom\<cdot>(f \<rightleftharpoons> x))"
            apply (simp add: False)

            sorry
        qed
      
  qed
qed

  have f14: "ubLen (f1 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub)) \<ge> lnsuc\<cdot>(ubLen (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub)))"
    apply (simp add: ubclRestrict_ubundle_def)
    apply (subst f141)
    defer
    apply (simp_all add: assms)
    using  assms(4) f141 leD sorry

(* ubLen ( b \<uplus> ub) = ubLen ub *)
(* ubLen (b \<uplus> ub\<bar>ufDom\<cdot>f1 ) \<ge> ubLen  ( b \<uplus> ub) *)
(* ubLen (f1 \<rightleftharpoons> b \<uplus> ub\<bar>ufDom\<cdot>f1) \<ge> lnsuc\<cdot> ubLen (b \<uplus> ub\<bar>ufDom\<cdot>f1 ) *)
(* f2*)
(*union \<ge> lnsuc ubLen ub*)


  show "lnsuc\<cdot>(ubLen ub) \<le> ubLen ((ufCompH f1 f2) b\<cdot>ub)"
    apply (simp add: ufCompH_def)
    apply (simp add: ubclUnion_ubundle_def ubclRestrict_ubundle_def)
    
    using assms z1 minOr f14 f141 f13 f12 f121 f122 f11 f10

  sorry
qed



lemma f2: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" and "ufIsStrong f1" and "ufIsStrong f2" and "ubLen b \<le> ubLen ub" and "ubDom\<cdot>b = ufCompI f1 f2" and "ubDom\<cdot>ub = ufCompL f1 f2"
  shows"ubLen ((ufCompH f1 f2) b\<cdot>ub) \<ge> ubLen b"

  sorry 


lemma ufComp_strongCausal: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" and "ufIsStrong f1" and "ufIsStrong f2"
  shows "ufIsStrong (ufComp f1 (f2::'m ubundle ufun))"
  apply (simp add: ufIsStrong_def ufComp_def ubclLen_ubundle_def)
  apply rule+
proof -

  fix b::"'m ubundle"
  assume a0: "b \<in> dom (Rep_cufun (Abs_cufun (\<lambda>x . (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))"

  have y98: "b \<in> dom (\<lambda>u. (ubclDom\<cdot>u = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 u) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
    using a0 by (simp add: assms(1))
  have y99: "ubDom\<cdot>b = ufCompI f1 f2"
    using  y98 by (simp add: domIff2 ubclDom_ubundle_def)
  have chain_def: "chain (\<lambda>a::nat. iter_ubfix2 (ufCompH f1 f2) a (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)"
    by (simp add: ubclDom_ubundle_def y99)

  have z2: "ufWell (\<Lambda>(x::'m\<^sup>\<Omega>). (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
    apply (rule ufun_wellI)
    apply (simp_all)
    apply (simp_all add: domIff2)
    apply (simp_all add: ubclDom_ubundle_def)
    apply auto
  proof -
    fix x
    show "\<And>(b::'m\<^sup>\<Omega>). ubDom\<cdot>b = ufCompI f1 f2 \<Longrightarrow> x \<in> ubDom\<cdot>(ubFix (ufCompH f1 f2 b) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
      using y99 assms       
      
      sorry
  qed

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
(*      show "ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<ge> lnsuc\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
        apply simp
        apply (subst f1) 
        apply (simp_all add: assms)
        defer
        apply (simp add: y99)
*)

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
(*                by (metis (no_types) a41 assms(1) assms(2) assms(3) f1 ufCompH_def ufcomph_insert) *)
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
           apply (simp add: ubclUnion_ubundle_def ubclLeast_ubundle_def ubclRestrict_ubundle_def)
           
           sorry

         have zz2: "ubLen (f2 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))
 \<ge> lnsuc\<cdot>(ubLen (iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))"
           apply (simp add: ubclUnion_ubundle_def ubclLeast_ubundle_def ubclRestrict_ubundle_def ubUnion_def)
           using assms
           sorry

         have zz3: "\<And> (z::'a\<^sup>\<Omega>) zz . ubLen (z \<uplus> zz) = ubLen z \<or> ubLen (z \<uplus> zz) = ubLen zz"
         proof -
   fix z zz
           show "ubLen (z \<uplus> zz) = ubLen z \<or> ubLen (z \<uplus> zz) = ubLen zz"
           proof (cases "ubLen z = \<infinity> \<or> ubLen zz = \<infinity>")
             case True
             obtain  n::lnat where zz31: "n = ubLen z"
               by simp
             obtain  nn::lnat where zz32: "nn = ubLen zz"  
               by simp
             have zz3T1: "n = \<infinity> \<or> nn = \<infinity>"
               by (simp add: True zz31 zz32)
             obtain b::"'b\<^sup>\<Omega>" where zz33: "ubLen b = \<infinity>"
               by (metis ubclLen_ubundle_def ubcllen_inf_ex)
             have zz3T2: "ubLen (b \<uplus> zz) = \<infinity>"
               apply (simp add: ubclUnion_ubundle_def ubunion_insert)
               sorry
             show ?thesis  sorry
           next
             case False
             obtain  n::nat where zz31: "Fin n = ubLen z"
               by (metis False infI)
              obtain nn::nat where zz32: "Fin nn = ubLen zz" 
                by (metis False infI)
             have zz3F1: "(Fin n < \<infinity> \<and> Fin nn < \<infinity>)"
               by simp

             show "ubLen (z \<uplus> zz) = ubLen z \<or> ubLen (z \<uplus> zz) = ubLen zz"
                using  zz3F1 zz31 zz32 False 
               sorry
           qed

           qed

         have zz11: "ubLen ((f1 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))) \<uplus> (f2 \<rightleftharpoons> ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))))
\<ge> lnsuc\<cdot>(ubLen ((iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))\<uplus>(iterate i\<cdot>(\<Lambda> (z::'m\<^sup>\<Omega>). (f1 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> z))) \<uplus> (f2 \<rightleftharpoons> (ubclRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> z))))\<cdot>(ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)))))"
           by (smt zz1 zz2 zz3) (*isar proof available*)

         have zz12: "lnsuc\<cdot> (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) \<le> ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)"
    by (simp add: ufCompH_def zz11)

  show "ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<ge> lnsuc\<cdot>(ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
      by (metis zz3 zz12)

(* proof -
  have "lnsuc\<cdot> (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) \<le> ubLen ((f1 \<rightleftharpoons> b \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> b \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b\<bar>ufDom\<cdot>f2))"
    by (simp add: ufCompH_def zz11)
  then have "lnsuc\<cdot> (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) \<le> ubLen ((f1 \<rightleftharpoons> b \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> b \<uplus> iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b\<bar>ufDom\<cdot>f2))"
    by (metis (no_types) zz3)
  then show "lnsuc\<cdot> (lnmin\<cdot>(ubLen b)\<cdot> (ubLen (iterate i\<cdot> (\<Lambda> u. (f1 \<rightleftharpoons> b \<uplus> u\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> b \<uplus> u\<bar>ufDom\<cdot>f2))\<cdot> (ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))) \<le> ubLen ((f1 \<rightleftharpoons> b \<uplus> iterate i\<cdot> (\<Lambda> u. (f1 \<rightleftharpoons> b \<uplus> u\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> b \<uplus> u\<bar>ufDom\<cdot>f2))\<cdot> (ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> b \<uplus> iterate i\<cdot> (\<Lambda> u. (f1 \<rightleftharpoons> b \<uplus> u\<bar>ufDom\<cdot>f1) \<uplus> (f2 \<rightleftharpoons> b \<uplus> u\<bar>ufDom\<cdot>f2))\<cdot> (ubclLeast (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))\<bar>ufDom\<cdot>f2))"
    by (metis (no_types) ufCompH_def y23)
qed *)
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