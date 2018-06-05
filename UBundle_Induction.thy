theory UBundle_Induction
  imports UBundle UBundle_Pcpo UBundle_Conc "untimed/Streams" "untimed/SPF"
begin

  
default_sort uscl


(****************************************************)
section\<open>Induction\<close>
(****************************************************) 

definition ubMaxLen:: "'M\<^sup>\<Omega> \<Rightarrow> lnat " where
"ubMaxLen b \<equiv> if ubDom\<cdot>b \<noteq> {} then (GREATEST ln. ln\<in>{(usclLen\<cdot>(b . c)) | c. c \<in> ubDom\<cdot>b}) else \<infinity>"  

lemma ubmaxlen_mono: "monofun (\<lambda>b. if ubDom\<cdot>b \<noteq> {} then (GREATEST ln. ln\<in>{(usclLen\<cdot>(b . c)) | c. c \<in> ubDom\<cdot>b}) else \<infinity>)"
  sorry

lemma ubmaxlen_mono2: "monofun ubMaxLen"
  using ubmaxlen_mono by (simp add: monofun_def ubMaxLen_def)

lemma ubmaxlen_least: "ubMaxLen (ubLeast cs) = Fin 0"
  sorry




(*
lemma ind: 
  "\<lbrakk>adm P; P \<epsilon>; \<And>a s. P s  \<Longrightarrow> P (\<up>a \<bullet> s)\<rbrakk> \<Longrightarrow> P x"
apply (unfold adm_def)
apply (erule_tac x="\<lambda>i. stake i\<cdot>x" in allE, auto)
apply (simp add: stakeind)
by (simp add: reach_stream)
*)

default_sort message

lemma ind_ub: 
  "\<lbrakk> adm P; 
     P (ubLeast (ubDom\<cdot>x)); 
     \<And>u ub. P ub \<and> ubDom\<cdot>u = (ubDom\<cdot>x) \<and> ubDom\<cdot>ub = (ubDom\<cdot>x) \<and> ubMaxLen u \<le> Fin 1 \<Longrightarrow> P (ubConc u\<cdot>ub) \<rbrakk>
     \<Longrightarrow> P (x :: 'a stream ubundle)"
proof - 
  fix x :: "'a stream\<^sup>\<Omega>"
  assume ind_adm: "adm P"
  assume ind_least: "P (ubLeast (ubDom\<cdot>x))"
  assume ind_step: "\<And>u ub. P ub \<and> ubDom\<cdot>u = (ubDom\<cdot>x) \<and> ubDom\<cdot>ub = (ubDom\<cdot>x) \<and> ubMaxLen u \<le> Fin 1 \<Longrightarrow> P (ubConc u\<cdot>ub)"

  have ind_sbTake: "P (\<Squnion>n. sbTake n\<cdot>x)"
  proof - 
    have "\<forall>i. P (sbTake i\<cdot>x)"
      apply rule
    proof - 
      fix i
      show "P (sbTake i\<cdot>x)"
      proof(induct i)
        case 0
        then show ?case 
          apply(simp add: sbtake_zero)
          using ind_least by simp
      next
        case (Suc i)
        hence ia: "P (sbTake i\<cdot>x)"
          by blast
        
        show ?case
          sorry
      qed  
    qed 
    thus ?thesis
      using ind_adm adm_def by (metis (mono_tags, lifting) lub_eq sbtake_chain)
  qed

  thus "P x"
    using sbtake_lub by simp 
qed

(*


        (*have "\<exists> u . (sbTake (Suc i)\<cdot>x) = ubConc (sbTake i\<cdot>x)\<cdot>u"
            apply(rule_tac x = "sbTake 1\<cdot>(sbDrop i\<cdot>x)" in exI)
          apply(rule ub_eq)
           apply simp
        proof - 
          fix c
          assume c_dom: "c \<in> ubDom\<cdot>(sbTake (Suc i)\<cdot>x)"
          hence c_dom2: "c \<in> ubDom\<cdot>x"
            by simp
          have ubwell_stake: "\<forall>c s i. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(stake i\<cdot>s)\<subseteq>(ctype c))"
            sorry
          have ubwell_sdrop: "\<forall>c s i. (sdom\<cdot>s\<subseteq>(ctype c) \<longrightarrow> sdom\<cdot>(sdrop i\<cdot>s)\<subseteq>(ctype c))"
            sorry
          show " sbTake (Suc i)\<cdot>x . c = ubConc (sbTake i\<cdot>x)\<cdot>(sbTake (1::nat)\<cdot>(sbDrop i\<cdot>x)) . c"
            apply(simp add: sbTake_def)
            apply(simp add: sbMapStream_def)
            apply(subst ubConc_usclConc_eq)

            defer
            defer

            apply(simp add: ubGetCh_def c_dom2)
              apply(simp add: sbdrop_insert usclConc_stream_def)
            apply(subst ubrep_ubabs)

               defer

            apply(simp add: c_dom2)
            
            
            sorry
        qed
          sorry
  then obtain u where sbtake_conc:"(sbTake (Suc i)\<cdot>x) = ubConc (sbTake i\<cdot>x)\<cdot>u"
          by blast
        then have sbtake_conc_length: "ubMaxLen u \<le> Fin 1"
          
          sorry
        have sbtake_conc_dom: "ubDom\<cdot>u = ubDom\<cdot>x"
          using sbtake_conc
          by (metis (mono_tags, lifting) Fin_0 Fin_leq_Suc_leq inf_ub lnle_Fin_0 lnle_def ubMaxLen_def ubleast_ubdom ubmaxlen_least zero_neq_one)
        have sbtake_dom: "ubDom\<cdot>(sbTake i\<cdot>x) = ubDom\<cdot>x"
          by simp*)
        show ?case
          apply(subst sbtake_conc)
          using ia sbtake_conc_length ind_step sbtake_conc_dom sbtake_dom
          by blast
*)


end