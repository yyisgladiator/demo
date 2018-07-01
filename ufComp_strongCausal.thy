theory ufComp_strongCausal
  imports UFun_Comp UBundle_Pcpo
begin

default_sort uscl_pcpo

declare [[show_types]]
declare [[show_sorts]]
declare [[show_consts]]


abbreviation lnatGreater :: "lnat \<Rightarrow> lnat \<Rightarrow> bool" (infix ">\<^sup>l" 65) where
"n >\<^sup>l m \<equiv>  n \<ge> lnsuc\<cdot>m"

abbreviation lnatLess :: "lnat \<Rightarrow> lnat \<Rightarrow> bool" (infix "<\<^sup>l" 65) where
"n <\<^sup>l m \<equiv>  lnsuc\<cdot>n \<le> m"


lemma z1: assumes "ubDom\<cdot>z \<inter> ubDom\<cdot>zz = {}" shows "ubLen (z \<uplus> zz) = ubLen z \<or> ubLen (z \<uplus> zz) = ubLen zz"
  apply (simp add: ubclUnion_ubundle_def)
  apply (case_tac "ubDom\<cdot>z = {}")
  apply simp
  apply (case_tac "ubDom\<cdot>zz = {}")
  apply (metis Int_empty_right empty_subsetI ubunion_commutative ubunion_idL)
proof -
  assume a0: "ubDom\<cdot>z \<noteq> {}"
  assume a1: "ubDom\<cdot>zz \<noteq> {}"

  (*
    obtain least channel c1 of z
    obtain least channel c2 of zz
    case distiction length c1 < length c2
  *)

  obtain c1 where c1_def: "c1 \<in> ubDom\<cdot>z \<and> ubLen z = usclLen\<cdot>(z . c1)"
    using a0 ublen_min_on_channel
    by (metis (no_types, lifting) ubLen_def)
  then have c1_min: "\<forall> c\<in>ubDom\<cdot>z. usclLen\<cdot>(z . c1) \<le> usclLen\<cdot>(z . c)"
    proof -
      have f1: "\<forall>p l. \<not> p (l::lnat) \<or> Least p \<le> l"
        using Least_le by auto
      have f2: "ubLen z = (LEAST l. l \<in> {usclLen\<cdot>(z . c) |c. c \<in> ubDom\<cdot>z})"
        by (simp add: a0 ubLen_def)
      { assume "\<exists>c. usclLen\<cdot>(z . v0_1) = usclLen\<cdot>(z . c) \<and> c \<in> ubDom\<cdot>z"
        then have "(LEAST l. l \<in> {usclLen\<cdot>(z . c) |c. c \<in> ubDom\<cdot>z}) \<le> usclLen\<cdot>(z . v0_1)"
          using f1 by simp
        then have "v0_1 \<notin> ubDom\<cdot>z \<or> usclLen\<cdot>(z . c1) \<le> usclLen\<cdot>(z . v0_1)"
          using f2 c1_def by force }
      then have f3: "v0_1 \<notin> ubDom\<cdot>z \<or> usclLen\<cdot>(z . c1) \<le> usclLen\<cdot>(z . v0_1)"
        by force
      obtain cc :: channel where
        "(\<exists>v0. v0 \<in> ubDom\<cdot>z \<and> \<not> usclLen\<cdot>(z . c1) \<le> usclLen\<cdot>(z . v0)) = (cc \<in> ubDom\<cdot>z \<and> \<not> usclLen\<cdot>(z . c1) \<le> usclLen\<cdot>(z . cc))"
        by moura
      then show ?thesis
        by (metis (mono_tags, lifting) c1_def f1 f2 f3 mem_Collect_eq)
    qed
  obtain c2 where c2_def: "c2 \<in> ubDom\<cdot>zz \<and> ubLen zz = usclLen\<cdot>(zz . c2)"
    using a1 ublen_min_on_channel
    by (metis (no_types, lifting) ubLen_def)
  then have c2_min: "\<forall> c\<in>ubDom\<cdot>zz. usclLen\<cdot>(zz . c2) \<le> usclLen\<cdot>(zz . c)"
    proof -
      have f1: "ubLen zz = (LEAST l. l \<in> {usclLen\<cdot>(zz . c) |c. c \<in> ubDom\<cdot>zz})"
        by (simp add: a1 ubLen_def)
      obtain cc :: channel where
        "(\<exists>v0. v0 \<in> ubDom\<cdot>zz \<and> \<not> usclLen\<cdot>(zz . c2) \<le> usclLen\<cdot>(zz . v0)) = (cc \<in> ubDom\<cdot>zz \<and> \<not> usclLen\<cdot>(zz . c2) \<le> usclLen\<cdot>(zz . cc))"
        by moura
      moreover
      { assume "\<exists>c. usclLen\<cdot>(zz . cc) = usclLen\<cdot>(zz . c) \<and> c \<in> ubDom\<cdot>zz"
        then have "(LEAST l. l \<in> {usclLen\<cdot>(zz . c) |c. c \<in> ubDom\<cdot>zz}) \<le> usclLen\<cdot>(zz . cc)"
          by (simp add: Least_le)
        then have "cc \<notin> ubDom\<cdot>zz \<or> usclLen\<cdot>(zz . c2) \<le> usclLen\<cdot>(zz . cc)"
          using f1 c2_def by fastforce }
      ultimately show ?thesis
        by blast
    qed

  show "ubLen (ubUnion\<cdot>z\<cdot>zz) = ubLen z \<or> ubLen (ubUnion\<cdot>z\<cdot>zz) = ubLen zz"
  proof(cases "usclLen\<cdot>(z . c1) \<le> usclLen\<cdot>(zz . c2)")
    case True
    then have "\<forall> c\<in>ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz). usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c1) \<le> usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c)"
      apply(simp)
      apply(subst ubunion_getchL)
      using assms c1_def apply blast
      by (metis (no_types, lifting) Un_iff c1_min c2_min dual_order.trans ubunion_getchL ubunion_getchR)
    moreover have "c1 \<in>ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)"
      by (simp add: c1_def)
    ultimately have "ubLen (ubUnion\<cdot>z\<cdot>zz) = usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c1)"
      proof -
        have f1: "\<forall>p l. \<not> p (l::lnat) \<or> Least p \<le> l"
          using Least_le by blast
        have f2: "\<forall>c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz) \<longrightarrow> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) \<le> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c)"
          by (metis \<open>\<forall>c::channel\<in>ubDom\<cdot> (ubUnion\<cdot> (z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>)). usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . (c1::channel)) \<le> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c)\<close>)
        have f3: "\<forall>u. ubDom\<cdot>u \<noteq> {} \<longrightarrow> (\<exists>c. c \<in> ubDom\<cdot>u \<and> usclLen\<cdot>(u . c::'a) = (LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u}))"
          using ublen_min_on_channel by blast
        obtain cc :: "channel set \<Rightarrow> channel" where
          "\<forall>x0. (\<exists>v1. v1 \<in> x0) = (cc x0 \<in> x0)"
          by moura
        then have "\<forall>C. (cc C \<in> C \<or> C = {}) \<and> ((\<forall>c. c \<notin> C) \<or> C \<noteq> {})"
          by auto
        then have f4: "ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz) \<noteq> {}"
          by (metis (no_types) \<open>(c1::channel) \<in> ubDom\<cdot> (ubUnion\<cdot>(z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>))\<close>)
        then obtain cca :: "'a\<^sup>\<Omega> \<Rightarrow> channel" where
          f5: "usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) \<le> usclLen\<cdot> (ubUnion\<cdot>z\<cdot>zz . cca (ubUnion\<cdot>z\<cdot>zz))"
          using f3 f2 by meson
        obtain ccb :: "'a\<^sup>\<Omega> \<Rightarrow> channel" where
          f6: "ccb (ubUnion\<cdot>z\<cdot>zz) \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz) \<and> usclLen\<cdot> (ubUnion\<cdot>z\<cdot>zz . ccb (ubUnion\<cdot>z\<cdot>zz)) = (LEAST l. l \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)})"
          using f4 f3 by meson
          have "\<forall>x0. (if ubDom\<cdot>x0 \<noteq> {} then LEAST uua. uua \<in> {usclLen\<cdot>(x0 . c::'a) |c. c \<in> ubDom\<cdot>x0} else \<infinity>) = (if ubDom\<cdot>x0 = {} then \<infinity> else LEAST uua. uua \<in> {usclLen\<cdot>(x0 . c) |c. c \<in> ubDom\<cdot>x0})"
            by auto
          then have f7: "\<forall>u. ubLen u = (if ubDom\<cdot>u = {} then \<infinity> else LEAST l. l \<in> {usclLen\<cdot>(u . c::'a) |c. c \<in> ubDom\<cdot>u})"
            by (simp add: ubLen_def)
          have "\<exists>c. usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) = usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) \<and> c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)"
            using \<open>(c1::channel) \<in> ubDom\<cdot> (ubUnion\<cdot>(z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>))\<close> by auto
          then have "usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)}"
            by blast
          then have "(LEAST l. l \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)}) \<le> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) \<and> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1) \<le> (LEAST l. l \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)})"
            using f6 f5 f1 by (metis (no_types, lifting) \<open>\<forall>c::channel\<in>ubDom\<cdot> (ubUnion\<cdot> (z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>)). usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . (c1::channel)) \<le> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c)\<close>)
          then have "(LEAST l. l \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)}) = usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c1)"
            using eq_iff by blast
          then show ?thesis
            using f7 f4 by presburger
        qed
    then show ?thesis
      using assms c1_def ubunion_getchL by fastforce
  next
    case False
    then have "\<forall> c\<in>ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz). usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c2) \<le> usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c)"
      apply(simp)
      apply(subst ubunion_getchR)
      using assms c2_def apply blast
      by (metis (no_types, lifting) Un_iff c1_min c2_min dual_order.trans le_cases ubunion_getchL ubunion_getchR)
    moreover have "c2 \<in>ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)"
      by (simp add: c2_def)
    ultimately have "ubLen (ubUnion\<cdot>z\<cdot>zz) = usclLen\<cdot>((ubUnion\<cdot>z\<cdot>zz) . c2)"
      proof -
        have f1: "ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz) \<noteq> {}"
          by (metis \<open>(c2::channel) \<in> ubDom\<cdot> (ubUnion\<cdot>(z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>))\<close> all_not_in_conv)
        obtain cc :: "'a\<^sup>\<Omega> \<Rightarrow> channel" where
          f2: "\<And>u. (cc u \<in> ubDom\<cdot>u \<or> ubDom\<cdot>u = {}) \<and> (usclLen\<cdot>(u . cc u) = (LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u}) \<or> ubDom\<cdot>u = {})"
          using ublen_min_on_channel by moura
        then have f3: "\<And>u. ubDom\<cdot>u = {} \<or> usclLen\<cdot>Rep_ubundle u\<rightharpoonup>cc u = (LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u})"
          proof -
            fix u :: "'a\<^sup>\<Omega>"
            { assume "(LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u}) \<noteq> usclLen\<cdot>(u . cc u)"
              then have "ubDom\<cdot>u = {} \<or> usclLen\<cdot>Rep_ubundle u\<rightharpoonup>cc u = (LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u})"
                using f2 by force }
            then show "ubDom\<cdot>u = {} \<or> usclLen\<cdot>Rep_ubundle u\<rightharpoonup>cc u = (LEAST l. l \<in> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u})"
              by (metis (no_types) ubgetch_insert)
          qed
        then have "\<And>l u. l \<notin> {usclLen\<cdot>(u . c) |c. c \<in> ubDom\<cdot>u} \<or> ubDom\<cdot>u = {} \<or> usclLen\<cdot>Rep_ubundle u\<rightharpoonup>cc u \<le> l"
          by (metis (no_types, lifting) Least_le mem_Collect_eq)
        then have f4: "\<And>l u. (\<forall>c. l \<noteq> usclLen\<cdot>(u . c) \<or> c \<notin> ubDom\<cdot>u) \<or> usclLen\<cdot>Rep_ubundle u\<rightharpoonup>cc u \<le> l"
          by auto
        have "cc (ubUnion\<cdot>z\<cdot>zz) \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)"
          using f2 f1 by blast
        then have "usclLen\<cdot> Rep_ubundle (ubUnion\<cdot>z\<cdot>zz)\<rightharpoonup>cc (ubUnion\<cdot>z\<cdot>zz) = usclLen\<cdot>Rep_ubundle (ubUnion\<cdot>z\<cdot>zz)\<rightharpoonup>c2"
          using f4 by (metis (no_types) \<open>(c2::channel) \<in> ubDom\<cdot> (ubUnion\<cdot>(z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>))\<close> \<open>\<forall>c::channel\<in>ubDom\<cdot> (ubUnion\<cdot> (z::'a::uscl_pcpo\<^sup>\<Omega>)\<cdot> (zz::'a::uscl_pcpo\<^sup>\<Omega>)). usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . (c2::channel)) \<le> usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c)\<close> dual_order.antisym ubgetch_insert)
        then have "(LEAST l. l \<in> {usclLen\<cdot>(ubUnion\<cdot>z\<cdot>zz . c) |c. c \<in> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz)}) = usclLen\<cdot> Rep_ubundle (ubUnion\<cdot>z\<cdot>zz)\<rightharpoonup>c2 \<and> ubDom\<cdot>(ubUnion\<cdot>z\<cdot>zz) \<noteq> {}"
          using f3 f1 by fastforce
        then show ?thesis
          by (simp add: ubLen_def ubgetch_insert)
      qed
    then show ?thesis
      by (simp add: c2_def)
  qed
qed

lemma ufcompH_len_step:
  assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}"
  and "ufIsStrong f1"
  and "ufIsStrong f2"
  and "(ubLen (ub :: 'a ubundle)) < lnsuc\<cdot>(ubLen b)"
  and "ubDom\<cdot>b = ufCompI f1 f2"
  and "ubDom\<cdot>ub = ufCompO f1 f2"
  shows "(ubLen ub) <\<^sup>l ubLen ((ufCompH f1 f2) b\<cdot>ub)"
proof -
  have y0: "ubDom\<cdot>b \<inter> ubDom\<cdot>ub = {}"
    using assms ufCompI_def ufCompO_def by simp

  have y1: "ubDom\<cdot>ub \<noteq> {}"
    by (metis assms(4) inf_ub not_less ubLen_def)

  have y2: "ubLen (b \<uplus> ub) = ubLen ub"
    proof (cases "ubDom\<cdot>b = {}")
      case True
      then show ?thesis
        by (simp add: ubclUnion_ubundle_def)
    next
      case False
      obtain c_b_min where c_b_def: "c_b_min \<in> ubDom\<cdot>b \<and> ubLen b = usclLen\<cdot>(b . c_b_min)"
        by (metis (no_types, lifting) False ubLen_def ublen_min_on_channel)
      obtain c_ub_min where c_ub_def: "c_ub_min \<in> ubDom\<cdot>ub \<and> ubLen ub = usclLen\<cdot>(ub . c_ub_min)"
        by (metis (no_types, lifting) ubLen_def ublen_min_on_channel y1)

      have f1: "dom (Rep_ubundle (b \<uplus> ub)) \<inter> ubclDom\<cdot>ub = ubDom\<cdot>(ubRestrict (ubclDom\<cdot>ub)\<cdot>(b \<uplus> ub))"
        using ubdom_insert by auto
      have f2: "(ubRestrict (ubclDom\<cdot>ub)\<cdot>(b \<uplus> ub)) = ub"
        by (metis ubclRestrict_ubundle_def ubclunion_restrict2)
      then have "c_ub_min \<in> dom (Rep_ubundle (b \<uplus> ub)) \<inter> ubclDom\<cdot>ub"
        using f1 c_ub_def by presburger
      then have f3: "c_ub_min \<in> dom (Rep_ubundle (b \<uplus> ub)) \<and> c_ub_min \<in> ubclDom\<cdot>ub"
        by blast
      have "\<forall>x0 x1. (x1 (x0::lnat) \<longrightarrow> Least x1 \<le> x0) = (\<not> x1 x0 \<or> Least x1 \<le> x0)"
        by fastforce
      then have f5: "\<forall>p l. \<not> p (l::lnat) \<or> Least p \<le> l"
        by (simp add: Least_le)
      have f6: "c_ub_min \<in> ubDom\<cdot>(b \<uplus> ub)"
        by (simp add: f3 ubdom_insert)
      have "\<forall>x0 x1 x2. (x2 \<in> x1 \<longrightarrow> (ubRestrict x1\<cdot>x0) . x2 = (x0 . x2::'a)) = (x2 \<notin> x1 \<or> (ubRestrict x1\<cdot>x0) . x2 = x0 . x2)"
        by fastforce
      then have "\<forall>c C u. c \<notin> C \<or> (ubRestrict C\<cdot>u) . c = (u . c::'a)"
        using ubgetch_ubrestrict by blast
      then have "\<exists>c. usclLen\<cdot>(ub . c_ub_min) = usclLen\<cdot>(b \<uplus> ub . c) \<and> c \<in> ubDom\<cdot>(b \<uplus> ub)"
        using f6 f3 f2 by (metis (no_types))
      then have "\<exists>c. usclLen\<cdot>(ub . c_ub_min) = usclLen\<cdot>(b \<uplus> ub . c) \<and> c \<in> ubDom\<cdot>(b \<uplus> ub)"
        by fastforce
      then have "usclLen\<cdot>(ub . c_ub_min) \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}"
        by simp
      then have f7: "(LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}) \<le> usclLen\<cdot>(ub . c_ub_min)"
        using f5 by presburger

      have f8: "{} \<noteq> dom (Rep_ubundle (b \<uplus> ub))"
        using f3 by blast

    show ?thesis
      proof -
        have f1: "\<And>u. ubLen u = (LEAST l. l \<in> {usclLen\<cdot>(u . c::'a) |c. c \<in> ubDom\<cdot>u}) \<or> dom (Rep_ubundle u) = {}"
          by (simp add: ubLen_def ubdom_insert)
        { assume "usclLen\<cdot>(ub . c_ub_min) \<le> ubLen (b \<uplus> ub)"
          then have "(LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}) \<le> usclLen\<cdot>(ub . c_ub_min) \<and> usclLen\<cdot>(ub . c_ub_min) \<le> ubLen (b \<uplus> ub) \<and> dom (Rep_ubundle (b \<uplus> ub)) \<noteq> {}"
            using f8 f7 by blast
          then have "ubLen (b \<uplus> ub) = usclLen\<cdot>(ub . c_ub_min)"
            using f1 by force
        }
      then show ?thesis
          by (metis (full_types) assms(4) c_ub_def lnle2le y0 z1)
      qed
    qed

  have y21: "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub))"
    (* restricting a bundle can only increase the length
       Proof idea:
       obtain least channel c of (b \<uplus> ub)
       case distinction ubDom\<cdot>(ubRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub)) = {}
    *)
  proof-
    obtain c_min where c_def: "c_min \<in> ubDom\<cdot>(b \<uplus> ub) \<and> ubLen (b \<uplus> ub) = usclLen\<cdot>((b \<uplus> ub) . c_min)"
      by (metis (no_types, lifting) assms(4) inf_ub not_less ubLen_def ublen_min_on_channel y2)
    then have cmin_channels: "\<forall> c\<in>ubDom\<cdot>(b \<uplus> ub). usclLen\<cdot>((b \<uplus> ub) . c_min) \<le>  usclLen\<cdot>((b \<uplus> ub) . c)"
      proof -
        have f1: "\<forall>u. ubLen u = (if ubDom\<cdot>u = {} then \<infinity> else LEAST l. l \<in> {usclLen\<cdot>(u . c::'a) |c. c \<in> ubDom\<cdot>u})"
          by (simp add: ubLen_def)
        obtain cc :: channel where
          "(\<exists>v0. v0 \<in> ubDom\<cdot>(b \<uplus> ub) \<and> \<not> usclLen\<cdot>(b \<uplus> ub . c_min) \<le> usclLen\<cdot>(b \<uplus> ub . v0)) = (cc \<in> ubDom\<cdot>(b \<uplus> ub) \<and> \<not> usclLen\<cdot>(b \<uplus> ub . c_min) \<le> usclLen\<cdot>(b \<uplus> ub . cc))"
          by moura
        moreover
        { assume "\<exists>c. usclLen\<cdot>(b \<uplus> ub . cc) = usclLen\<cdot>(b \<uplus> ub . c) \<and> c \<in> ubDom\<cdot>(b \<uplus> ub)"
          then have "\<exists>c. usclLen\<cdot>(b \<uplus> ub . cc) = usclLen\<cdot>(b \<uplus> ub . c) \<and> c \<in> ubDom\<cdot>(b \<uplus> ub)"
            by presburger
          then have "(LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}) \<le> usclLen\<cdot>(b \<uplus> ub . cc)"
            by (simp add: Least_le)
          moreover
          { assume "(LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}) \<noteq> usclLen\<cdot>(b \<uplus> ub . c_min)"
            then have "ubLen (b \<uplus> ub) \<noteq> (LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)})"
              using c_def by presburger
            then have "ubDom\<cdot>(b \<uplus> ub) = {}"
              using f1 by meson
            then have "cc \<notin> ubDom\<cdot>(b \<uplus> ub) \<or> usclLen\<cdot>(b \<uplus> ub . c_min) \<le> usclLen\<cdot>(b \<uplus> ub . cc)"
              by (metis (full_types) all_not_in_conv) }
          ultimately have "cc \<notin> ubDom\<cdot>(b \<uplus> ub) \<or> usclLen\<cdot>(b \<uplus> ub . c_min) \<le> usclLen\<cdot>(b \<uplus> ub . cc)"
            by fastforce }
        ultimately show ?thesis
          by auto
      qed
    show ?thesis
    proof(cases "ubDom\<cdot>(ubRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub)) = {}")
      case True
      then show ?thesis
        by (simp add: ubLen_def)
    next
      case False
      then show ?thesis
        by (metis (no_types, lifting) IntE c_def cmin_channels ubLen_geI ubdom_insert ubgetch_ubrestrict ubrestrict_ubdom2 y2)
    qed
  qed

  then have y3: "(ubLen ub) <\<^sup>l (ubLen (f1 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub))))"
  proof -
    have y1: "(ubRestrict (ufDom\<cdot>f1)\<cdot>(b \<uplus> ub)) \<in> dom (Rep_cufun f1)"
      by (metis (no_types, lifting) Un_Diff_cancel2 Un_assoc assms(5) assms(6) le_iff_sup sup_left_idem ubclDom_ubundle_def ubclRestrict_ubundle_def ubcldom_least_cs ubclunion_ubcldom ubresrict_dom2 ufCompI_def ufCompO_def ufunLeastIDom ufun_ufundom2dom)
    then  show ?thesis
    using assms(2) ufIsStrong_def ubclRestrict_ubundle_def
    by (smt dual_order.trans lnsuc_lnle_emb ubclLen_ubundle_def y21)
  qed

  (* Same for f2 *)
  have y22: "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub))"
    proof(cases "ubDom\<cdot>(ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) = {}")
      case True
      then show ?thesis
        by (simp add: ubLen_def)
    next
      case False
      then show ?thesis
       proof -
         have f1: "\<forall>u l. (\<exists>c. c \<in> ubDom\<cdot>u \<and> \<not> l \<le> usclLen\<cdot>(u . c::'a)) \<or> l \<le> ubLen u"
           using ubLen_geI by auto
        obtain cc :: "lnat \<Rightarrow> 'a\<^sup>\<Omega> \<Rightarrow> channel" where
          "\<forall>x0 x1. (\<exists>v2. v2 \<in> ubDom\<cdot>x1 \<and> \<not> x0 \<le> usclLen\<cdot>(x1 . v2)) = (cc x0 x1 \<in> ubDom\<cdot>x1 \<and> \<not> x0 \<le> usclLen\<cdot>(x1 . cc x0 x1))"
          by moura
        then have f2: "\<forall>u l. cc l u \<in> ubDom\<cdot>u \<and> \<not> l \<le> usclLen\<cdot>(u . cc l u) \<or> l \<le> ubLen u"
          using f1 by metis
        then have f3: "ubDom\<cdot>(b \<uplus> ub) \<noteq> {}"
          by (metis (no_types) all_not_in_conv assms(4) leD y2)
        have "\<forall>u. ubLen u = (if ubDom\<cdot>u = {} then \<infinity> else LEAST l. l \<in> {usclLen\<cdot>(u . c::'a) |c. c \<in> ubDom\<cdot>u})"
          by (simp add: ubLen_def)
        then have f4: "\<forall>u. if ubDom\<cdot>u = {} then ubLen u = \<infinity> else ubLen u = (LEAST l. l \<in> {usclLen\<cdot>(u . c::'a) |c. c \<in> ubDom\<cdot>u})"
          by force
        { assume "usclLen\<cdot> ((ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) . cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub))) = usclLen\<cdot> (b \<uplus> ub . cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)))"
          moreover
          { assume "\<exists>c. usclLen\<cdot> ((ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) . cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub))) = usclLen\<cdot>(b \<uplus> ub . c) \<and> c \<in> ubDom\<cdot>(b \<uplus> ub)"
            then have "usclLen\<cdot> ((ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) . cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub))) \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}"
              by force
            then have "(LEAST l. l \<in> {usclLen\<cdot>(b \<uplus> ub . c) |c. c \<in> ubDom\<cdot>(b \<uplus> ub)}) \<le> usclLen\<cdot> ((ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) . cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)))"
              by (meson wellorder_Least_lemma(2))
            then have ?thesis
              using f4 f3 f2 y2 by auto
          }
          ultimately have "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<or> cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<notin> ubDom\<cdot>(b \<uplus> ub) \<or> cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<notin> ufDom\<cdot>f2"
            by blast
        }
        then have "ubLen ub \<le> ubLen (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<or> cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<notin> ubDom\<cdot>(b \<uplus> ub) \<or> cc (ubLen ub) (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<notin> ufDom\<cdot>f2"
          by (metis (no_types) ubgetch_ubrestrict)
        then show ?thesis
          using f2 by (metis (no_types) IntE ubrestrict_ubdom2)
       qed 
    qed

  then have y4: "(ubLen ub) <\<^sup>l (ubLen (f2 \<rightleftharpoons> (ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub))))"
  proof -
    have y1: "(ubRestrict (ufDom\<cdot>f2)\<cdot>(b \<uplus> ub)) \<in> dom (Rep_cufun f2)"
      using assms(5) assms(6) ufCompI_def
      by (metis (no_types, lifting) Un_Diff_cancel Un_assoc sup.absorb_iff1 sup.right_idem ubclDom_ubundle_def ubclRestrict_ubundle_def ubclUnion_ubundle_def ubcldom_least_cs ubclunion_ubcldom ubresrict_dom2 ubunion_commutative ufCompO_def ufunLeastIDom ufun_ufundom2dom y0)
    then show ?thesis
      using assms(3) ufIsStrong_def ubclRestrict_ubundle_def
      by (smt dual_order.trans lnsuc_lnle_emb ubclLen_ubundle_def y22)
  qed

  show ?thesis
    apply(simp add: ufCompH_def)
    by (smt Un_Diff_cancel2 assms(1) assms(5) assms(6) le_supI1 sup_ge1 sup_ge2 ubclDom_ubundle_def ubclRestrict_ubundle_def ubclunion_ubcldom ufCompI_def ufCompO_def ufRanRestrict y3 y4 z1)
qed

lemma ufComp_strongCausal: assumes "ufRan\<cdot>f1 \<inter> ufRan\<cdot>f2 = {}" and "ufIsStrong f1" and "ufIsStrong f2"
  shows "ufIsStrong (ufComp f1 (f2::'m ubundle ufun))"
  apply (simp add: ufIsStrong_def ufComp_def ubclLen_ubundle_def)
  apply rule+
proof -
  fix b ::"'m ubundle"
  assume a0: "b \<in> dom (Rep_cufun (Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))))"
  then have "b \<in> dom (\<lambda>u. (ubclDom\<cdot>u = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 u) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
    by (simp add: assms(1))
  then have a1: "ubDom\<cdot>b = ufCompI f1 f2"
    by (simp add: domIff2 ubclDom_ubundle_def)

  have comp_well: "ufWell (\<Lambda> x. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2))"
    using assms(1) ufcomp_well by blast

  have ubLen_cont: "ubLen (\<Squnion>i::nat. iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)
                        = (\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
    (* Not possible with infinite channels *)
    sorry

  have comp_chain: "chain (\<lambda>i. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
    by (metis (no_types) a1 ch2ch_monofun iter_ufCompH_chain ubclDom_ubundle_def ublen_monofun)


  have ufcompH_iterate_len: "\<And>i. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) < lnsuc\<cdot>(ubLen b) \<Longrightarrow>
    ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) >\<^sup>l (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
  proof -
    fix i
    assume a2: "ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) < lnsuc\<cdot>(ubLen b)"
    show "ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) >\<^sup>l (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
      apply(unfold iterate_Suc)
      apply(subst ufcompH_len_step)
      apply(simp_all add: assms a1 a2)
      by (metis a1 iter_ufCompH_dom ubclDom_ubundle_def ufCompO_def)
  qed

  have f10: "(ubLen b) <\<^sup>l (\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
  proof (cases "ubLen b = \<infinity>")
    case True
    have "\<And>i. ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) >\<^sup>l (ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
      by (metis (no_types, lifting) True antisym_conv2 comp_chain fold_inf inf_ub lnle_def po_class.chain_def ufcompH_iterate_len)
    then have "(\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) = \<infinity>"
      proof -
        have f1: "\<forall>l. \<not> l <\<^sup>l l \<or> \<not> l < \<infinity>"
          by (metis (lifting) ln_less not_le)
        have f2: "\<forall>n l f. ((l::lnat) \<sqsubseteq> Lub f \<or> \<not> l \<le> f n) \<or> \<not> chain f"
          by (metis (lifting) below_lub lnle_conv)
        have f3: "\<forall>l. l \<sqsubseteq> lnsuc\<cdot>l"
          by (metis less_lnsuc lnle_conv)
        have "lnsuc\<cdot> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) = (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) \<longrightarrow> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) = \<infinity>"
          using f1 by (metis (lifting) dual_order.order_iff_strict inf_ub)
        then show ?thesis
          using f3 f2 by (metis (no_types, lifting) \<open>\<And>i::nat. ubLen (iter_ubfix2 (ufCompH (f1::('m::uscl_pcpo\<^sup>\<Omega>) ufun) (f2::('m::uscl_pcpo\<^sup>\<Omega>) ufun)) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) (b::'m::uscl_pcpo\<^sup>\<Omega>)) <\<^sup>l ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc i) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)\<close> below_antisym comp_chain l42 unique_inf_lub)
      qed
    then show ?thesis
      by (metis True fold_inf lnat_po_eq_conv)
  next
    case False
    obtain n where f101: "Fin n = ubLen b" by (metis False infI)

    have "(Fin n) <\<^sup>l (\<Squnion>i::nat. ubLen (iter_ubfix2 (ufCompH f1 f2) i (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
      proof -
        obtain nn :: "(nat \<Rightarrow> lnat) \<Rightarrow> nat" where
          f1: "\<forall>f. f (nn f) = Lub f \<or> \<not> finite_chain f \<or> \<not> chain f"
          by (metis (no_types) l42)
        have f2: "\<forall>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<sqsubseteq> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
          using comp_chain is_ub_thelub by blast
        have f3: "\<forall>l la. \<not> la < l \<or> la < \<infinity>"
          by (metis inf_ub less_le_trans)
        { assume "\<exists>n. \<not> ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) < ubLen (iter_ubfix2 (ufCompH f1 f2) (Suc n) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)"
          then have "\<exists>na. \<not> ubLen (iter_ubfix2 (ufCompH f1 f2) na (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) < Fin (Suc n)"
            using f3 by (metis (full_types) Fin_Suc f101 le2lnle ufcompH_iterate_len)
          then have "(\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) < Fin (Suc n) \<and> ubLen (iter_ubfix2 (ufCompH f1 f2) (nn (\<lambda>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) = (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) \<longrightarrow> (\<exists>n. \<not> ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<le> ubLen (iter_ubfix2 (ufCompH f1 f2) (nn (\<lambda>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))"
            using le_less_trans by auto }
        then have "ubLen (iter_ubfix2 (ufCompH f1 f2) (nn (\<lambda>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b))) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b) \<noteq> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) \<or> \<not> (\<Squnion>n. ubLen (iter_ubfix2 (ufCompH f1 f2) n (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2) b)) < Fin (Suc n)"
          using f2 by (metis leD lnle_conv)
        then show ?thesis
          using f1 comp_chain unique_inf_lub
          by (metis (no_types, lifting) Fin_Suc inf_ub leI)
      qed

    then show ?thesis
      by (metis Fin_Suc Fin_leq_Suc_leq f101)
  qed

  show "(ubLen b) <\<^sup>l ubLen (Abs_cufun (\<lambda>x. (ubclDom\<cdot>x = ufCompI f1 f2)\<leadsto>ubFix (ufCompH f1 f2 x) (ufRan\<cdot>f1 \<union> ufRan\<cdot>f2)) \<rightleftharpoons> b)"
    apply(simp add: comp_well)
    apply(simp add: ubclDom_ubundle_def a1)
    apply(simp add: ubFix_def)
    by (simp add: f10 ubLen_cont)
qed