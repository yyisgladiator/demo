theory sMed

imports stream.Streams

begin

(* ----------------------------------------------------------------------- *)
section {* definition *}
(* ----------------------------------------------------------------------- *)


text{* Untimed version of a medium, that loses messages. *}
definition sMed :: "'a stream \<rightarrow> bool stream \<rightarrow> 'a stream" where
"sMed \<equiv> \<Lambda> msg ora. sprojfst\<cdot>(sfilter {x. snd x}\<cdot>(szip\<cdot>msg\<cdot>ora))"


(* ----------------------------------------------------------------------- *)
section {* basic properties *}
(* ----------------------------------------------------------------------- *)

lemma oracases [case_names bottom true false]:
  assumes bottom: "ts=\<bottom> \<Longrightarrow> P ts"
    and true: "\<And>as. ts= (\<up>True \<bullet> as) \<Longrightarrow> P ts"
    and false: "\<And>as. ts=(\<up>False \<bullet> as) \<Longrightarrow> P ts"
  shows "P ts"
  by (metis (full_types) bottom false scases true)

text {* In the following we assume fairness for all medium lemmata: #({True} \<ominus> ora)=\<infinity> *}

(* ----------------------------------------------------------------------- *)
subsection {* basic properties of newOracle *}
(* ----------------------------------------------------------------------- *)

text{* Two oracles can be combined in one oracle. *}
fixrec newOracle :: "bool stream \<rightarrow> bool stream \<rightarrow> bool stream" where
"newOracle\<cdot>\<bottom>\<cdot>bs = \<bottom> " |
"newOracle\<cdot>as\<cdot>\<bottom> = \<bottom> " |
"newOracle\<cdot>((up\<cdot>a)&&as)\<cdot>((up\<cdot>b)&&bs) = 
  (* First oracle is not transmitting the message *)
  (if(a = Discr False) then (updis False)&&newOracle\<cdot>as\<cdot>((up\<cdot>b)&&bs)
  
  (* First oracle is transmitting *)
  else  up\<cdot>b && newOracle\<cdot>as\<cdot>bs)"

(* Testing that it works *)
lemma neworacle_test:
  "newOracle\<cdot>(<[True, True, False, True]>)\<cdot>(<[True, False, True]>) = <[True, False, False, True]>"
  proof-
    have test_simp: "newOracle\<cdot>(updis True && updis True && updis False && updis True && \<epsilon>)\<cdot>
      (updis True && updis False && updis True && \<epsilon>) =
       updis True && updis False && updis False && updis True && \<epsilon>"
      by fixrec_simp
    thus ?thesis 
      by (simp only: list2s_0 list2s_Suc)
  qed

(* Integration in newora_f2 *)
lemma newora_f [simp]: 
  "(newOracle\<cdot>(\<up>False \<bullet> ora1)\<cdot>(\<up>ora \<bullet> ora2)) = \<up>False \<bullet> newOracle\<cdot>ora1\<cdot>(\<up>ora \<bullet> ora2)"
  by (metis lscons_conv newOracle.simps(3))

text{* If the first element of the first oracle is false, then the resulting oracle emits false. *}
lemma newora_f2 [simp]: 
  "ora2\<noteq>\<bottom> \<Longrightarrow> (newOracle\<cdot>(\<up>False \<bullet> ora1)\<cdot>ora2) = \<up>False \<bullet> newOracle\<cdot>ora1\<cdot>ora2"
  by (metis scases newora_f)

text{* The resulting oracle emits true iff the first element of both oracles is true. *}
lemma newora_t [simp]: "(newOracle\<cdot>(\<up>True \<bullet> ora1)\<cdot>(\<up>ora \<bullet> ora2)) = \<up>ora \<bullet> newOracle\<cdot>ora1\<cdot>ora2"
  by (metis (no_types, lifting) discr.simps(1) lscons_conv newOracle.simps(3))

text{* Admissibility of the fairness predicate of newOracle. *}
lemma newora_fair_adm: 
  "adm (\<lambda>a. \<forall>x. #a \<le> #({True} \<ominus> x) \<longrightarrow> #({True} \<ominus> newOracle\<cdot>x\<cdot>a) = #({True} \<ominus> a))"
  proof-
    have adm_chain: "\<And>x Y. chain Y \<Longrightarrow> \<forall>i. #(Y i) \<le> #({True} \<ominus> x) \<longrightarrow> #({True} \<ominus> newOracle\<cdot>x\<cdot>(Y i)) = #({True} \<ominus> Y i) \<Longrightarrow>
      #(\<Squnion>i. Y i) \<le> #({True} \<ominus> x) \<Longrightarrow> #({True} \<ominus> newOracle\<cdot>x\<cdot>(\<Squnion>i. Y i)) = #({True} \<ominus> (\<Squnion>i. Y i))"
      proof-
        fix x Y
        assume ch_Y: "chain Y" and as1:"\<forall>i. #(Y i) \<le> #({True} \<ominus> x) \<longrightarrow> #({True} \<ominus> newOracle\<cdot>x\<cdot>(Y i)) = #({True} \<ominus> Y i)"
          and as2: " #(\<Squnion>i. Y i) \<le> #({True} \<ominus> x)"
        have "\<And>i. #(Y i) \<sqsubseteq> #(\<Squnion>i. Y i)"
          using ch_Y is_ub_thelub monofun_cfun_arg by blast
        hence "\<And>i. #(Y i) \<le> #({True} \<ominus> x)"
          using as2 lnle_conv trans_lnle by blast
        thus "#({True} \<ominus> newOracle\<cdot>x\<cdot>(\<Squnion>i. Y i)) = #({True} \<ominus> (\<Squnion>i. Y i))"
          proof -
            have "(\<Squnion>n. #({True} \<ominus> newOracle\<cdot>x\<cdot>(Y n))) = (\<Squnion>n. #({True} \<ominus> Y n))"
              using \<open>\<And>i. #(Y i) \<le> #({True} \<ominus> x)\<close> as1 by presburger
            then show ?thesis
              by (simp add: ch_Y contlub_cfun_arg)
          qed
      qed     
    then have "\<And>x. adm (\<lambda>a. #a \<le> #({True} \<ominus> x) \<longrightarrow> #({True} \<ominus> newOracle\<cdot>x\<cdot>a) = #({True} \<ominus> a))"
      using adm_def by blast 
    thus ?thesis
      by(rule adm_all)
  qed

text{* If the first n elements of the first oracle are false, then the first n elements of the 
       resulting oracle are false. *}
lemma new_ora_ntimes: 
  assumes "ora2\<noteq>\<bottom>" 
  shows "newOracle\<cdot>((sntimes n (\<up>False)) \<bullet> ora1)\<cdot>ora2 =(sntimes n (\<up>False)) \<bullet> newOracle\<cdot>ora1\<cdot>ora2"
  using assms
  proof (induction n)
    case 0
    then show ?case
      by simp
  next
    case (Suc n)
    then show ?case
      by simp
  qed

(* Integration in newora_fair? *)
lemma newora_fair_h:  
  "#ora2 \<le> #({True} \<ominus> ora1) \<longrightarrow> #({True} \<ominus> (newOracle\<cdot>ora1\<cdot>ora2))=#({True} \<ominus> ora2)"  
  proof(induction ora2 arbitrary: ora1 rule: ind)
    case 1
    then show ?case
      using newora_fair_adm by blast
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    show ?case 
      proof
        assume as: "#(\<up>a \<bullet> s) \<le> #({True} \<ominus> ora1)"
        hence "0 < #({True} \<ominus> ora1)" 
          using lnless_def by auto
        obtain n where n_def: "(sntimes n (\<up>False)) \<bullet> \<up>True \<sqsubseteq> ora1"
          using \<open>0 < #({True} \<ominus> ora1)\<close> lnless_def sbool_ntimes_f by fastforce
        obtain newora where newora_def: "ora1 = (sntimes n (\<up>False)) \<bullet> \<up>True \<bullet> newora"
          using approxl3 assoc_sconc n_def by blast
        have h1: "newOracle\<cdot>ora1\<cdot>(\<up>a \<bullet> s) = (sntimes n (\<up>False)) \<bullet> \<up>a \<bullet> (newOracle\<cdot>newora\<cdot>s) "
          by (simp add: n_def new_ora_ntimes newora_def)
        have h2: "#({True} \<ominus> ora1) = lnsuc\<cdot>(#({True} \<ominus> newora))"
          by (simp add: n_def newora_def)
        thus "#({True} \<ominus> newOracle\<cdot>ora1\<cdot>(\<up>a \<bullet> s)) = #({True} \<ominus> \<up>a \<bullet> s)"
          by (metis "3.IH" as h1 lnsuc_lnle_emb sfilter_in sfilter_nin sfilter_ntimes slen_scons)        
      qed
  qed

  text{* If both oracles are fair, then the resulting oracle is fair.  *}
lemma newora_fair: 
  assumes "#({True} \<ominus> ora1)=\<infinity>" 
    and "#({True} \<ominus> ora2)=\<infinity>"
  shows "#({True} \<ominus> (newOracle\<cdot>ora1\<cdot>ora2))=\<infinity>"
  by (simp add: assms(1) assms(2) newora_fair_h)

(* ----------------------------------------------------------------------- *)
subsection {* basic properties of sMed *}
(* ----------------------------------------------------------------------- *)

text{* "Lossy" medium that gets messages and an oracle and will transmit the k-th message if
       the k-th element in the oracle is True, otherwise the message will be discarded. *}
lemma smed_insert: "sMed\<cdot>msg\<cdot>ora = sprojfst\<cdot>(sfilter {x. snd x}\<cdot>(szip\<cdot>msg\<cdot>ora))"
  by (simp add: sMed_def)

text{* If the first element in the oracle is True then the current message will be transmitted. *}
lemma smed_t [simp]: "sMed\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>True \<bullet> ora) = \<up>a \<bullet> (sMed\<cdot>as\<cdot>ora)"
  by (simp add: sMed_def)

text{* If the first element in the oracle is False then the current messages will not be transmitted. *}
lemma smed_f [simp]: "sMed\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>False \<bullet> ora) = (sMed\<cdot>as\<cdot>ora)"
  by (simp add: sMed_def) 

text{* If the message stream is empty then the medium will not transmit anything. *}
lemma smed_bot1 [simp]: "sMed\<cdot>\<bottom>\<cdot>ora = \<bottom>"
  by (simp add: sMed_def)

text{* If the oracle is empty then the medium will not transmit anything. *}
lemma smed_bot2 [simp]: "sMed\<cdot>msg\<cdot>\<bottom> = \<bottom>"
  by (simp add: sMed_def)    

text{* If there are infinitely many messages, infinitely many messages will be transmitted. *}
lemma smed_slen_inf [simp]: 
  assumes "#msg=\<infinity>"
  shows "#(sMed\<cdot>msg\<cdot>ora) = #({True} \<ominus> ora)"
  using assms
  proof (induction ora arbitrary: msg rule:ind)
    case 1
    then show ?case 
      by simp
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    have h1: "a = True \<Longrightarrow> ?case"
      using "3.IH" "3.prems" inf_scase by force 
    have h2: "a = False \<Longrightarrow> ?case"
      using "3.IH" "3.prems" inf_scase by force      
    then show ?case 
      using h1 h2 by blast
  qed

text{* Medium without oracle will transmit all messages.*}
lemma smed_inftrue: "sMed\<cdot>msg\<cdot>((\<up>True) \<infinity>) = msg"  
  proof (induction msg rule: ind)
    case 1
    then show ?case 
      by simp
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    have lscons_simp: "\<And>a s. sprojfst\<cdot>({x. snd x} \<ominus> szip\<cdot>s\<cdot>\<up>True\<infinity>) = s 
      \<Longrightarrow> sprojfst\<cdot>({x. snd x} \<ominus> szip\<cdot>(\<up>a \<bullet> s)\<cdot>\<up>True\<infinity>) = \<up>a \<bullet> s"
      by (metis sinftimes_unfold smed_insert smed_t)
    thus "\<And>a s. sMed\<cdot>s\<cdot>\<up>True\<infinity> = s \<Longrightarrow> sMed\<cdot>(\<up>a \<bullet> s)\<cdot>\<up>True\<infinity> = \<up>a \<bullet> s"
      by (simp add: smed_insert) 
  qed


(* ----------------------------------------------------------------------- *)
section {* additional properties *}
(* ----------------------------------------------------------------------- *)  

(* used by smed_slen2smed2*)
text{* The duplicates that are removed from a zipped stream are at least as much as the 
       duplicates that are removed from the second stream of a zipped stream. *}
lemma sprojsnd_srcdups_slen: "#(srcdups\<cdot>(sprojsnd\<cdot>s)) \<le> #(sprojsnd\<cdot>(srcdups\<cdot>s))"
  proof (induction s rule: ind)
    case 1
    then show ?case 
      proof (rule admI)
        fix Y :: "nat \<Rightarrow> ('b \<times> 'a) stream"
        assume Y_chain: "chain Y"
        assume adm_assump: "\<forall>i. #(srcdups\<cdot>(sprojsnd\<cdot>(Y i))) \<le> #(sprojsnd\<cdot>(srcdups\<cdot>(Y i)))"
        then show "#(srcdups\<cdot>(sprojsnd\<cdot>(\<Squnion>i. Y i))) \<le> #(sprojsnd\<cdot>(srcdups\<cdot>(\<Squnion>i. Y i)))"
          by (simp add: Y_chain adm_assump contlub_cfun_arg lub_mono2)
      qed
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    then show ?case 
      proof (cases rule: scases [of s])
        case bottom
        then show ?thesis
          by simp
      next
        case (scons b bs)
        then show ?thesis
          proof (case_tac "a=b")
            have "a = b \<Longrightarrow> s = \<up>b \<bullet> bs \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>(\<up>b \<bullet> \<up>b \<bullet> bs))) \<le> #(sprojsnd\<cdot>(srcdups\<cdot>(\<up>b \<bullet> bs)))"
              proof (case_tac a)
                show ?thesis
                  proof (case_tac b)                 
                    show ?thesis
                      by (metis "3.IH" prod.exhaust scons sprojsnd_scons srcdups_eq)
                  qed
              qed
            thus srcdups_sprojsnd: "s = \<up>b \<bullet> bs \<Longrightarrow> a = b \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>(\<up>a \<bullet> s))) \<le> #(sprojsnd\<cdot>(srcdups\<cdot>(\<up>a \<bullet> s)))"
                by simp
            have "a \<noteq> b \<Longrightarrow> s = \<up>b \<bullet> bs \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>(\<up>a \<bullet> \<up>b \<bullet> bs))) \<le> #(sprojsnd\<cdot>(\<up>a \<bullet> srcdups\<cdot>(\<up>b \<bullet> bs)))"
              proof (case_tac a)
                show "\<And>aa ba. a \<noteq> b \<Longrightarrow> s = \<up>b \<bullet> bs \<Longrightarrow> a = (aa, ba) \<Longrightarrow>
                  #(srcdups\<cdot>(sprojsnd\<cdot>(\<up>a \<bullet> \<up>b \<bullet> bs))) \<le> #(sprojsnd\<cdot>(\<up>a \<bullet> srcdups\<cdot>(\<up>b \<bullet> bs)))"
                  proof (case_tac b)
                    show "\<And>aa ba ab bb. a \<noteq> b \<Longrightarrow> s = \<up>b \<bullet> bs \<Longrightarrow> a = (aa, ba) \<Longrightarrow> b = (ab, bb) \<Longrightarrow>
                      #(srcdups\<cdot>(sprojsnd\<cdot>(\<up>a \<bullet> \<up>b \<bullet> bs))) \<le> #(sprojsnd\<cdot>(\<up>a \<bullet> srcdups\<cdot>(\<up>b \<bullet> bs)))"
                      proof (case_tac "aa=ab")
                        show "\<And>aa ba ab bb. a \<noteq> b \<Longrightarrow> s = \<up>b \<bullet> bs \<Longrightarrow> a = (aa, ba) \<Longrightarrow> b = (ab, bb) \<Longrightarrow> 
                          aa = ab \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>(\<up>a \<bullet> \<up>b \<bullet> bs))) \<le> #(sprojsnd\<cdot>(\<up>a \<bullet> srcdups\<cdot>(\<up>b \<bullet> bs)))"
                          using "3.IH" by auto
                        show "\<And>aa ba ab bb. a \<noteq> b \<Longrightarrow> s = \<up>b \<bullet> bs \<Longrightarrow> a = (aa, ba) \<Longrightarrow> b = (ab, bb) \<Longrightarrow> 
                          aa \<noteq> ab \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>(\<up>a \<bullet> \<up>b \<bullet> bs))) \<le> #(sprojsnd\<cdot>(\<up>a \<bullet> srcdups\<cdot>(\<up>b \<bullet> bs)))"
                          proof (case_tac "ba=bb")
                            show "\<And>aa ba ab bb. a \<noteq> b \<Longrightarrow> s = \<up>b \<bullet> bs \<Longrightarrow> a = (aa, ba) \<Longrightarrow> b = (ab, bb) \<Longrightarrow>
                              aa \<noteq> ab \<Longrightarrow> ba = bb \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>(\<up>a \<bullet> \<up>b \<bullet> bs))) \<le> #(sprojsnd\<cdot>(\<up>a \<bullet> srcdups\<cdot>(\<up>b \<bullet> bs)))"
                              by (metis (no_types, lifting) "3.IH" less_lnsuc slen_scons sprojsnd_scons srcdups_eq trans_lnle)
                            show " \<And>aa ba ab bb. a \<noteq> b \<Longrightarrow> s = \<up>b \<bullet> bs \<Longrightarrow> a = (aa, ba) \<Longrightarrow> b = (ab, bb) \<Longrightarrow>
                              aa \<noteq> ab \<Longrightarrow> ba \<noteq> bb \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>(\<up>a \<bullet> \<up>b \<bullet> bs))) \<le> #(sprojsnd\<cdot>(\<up>a \<bullet> srcdups\<cdot>(\<up>b \<bullet> bs)))"
                              using "3.IH" by auto
                          qed
                      qed
                  qed                     
              qed 
            thus ?thesis
              using srcdups_sprojsnd scons by fastforce
          qed
      qed
  qed

(* used by a lot of srcdups lemmata, subsection srcdups? *)
lemma srcdups_nfst2snd: 
  assumes "a \<noteq> shd s" 
  shows "srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> srcdups\<cdot>s" 
  using assms by (metis srcdups_neq srcdups_shd srcdups_srt strict_sdropwhile surj_scons)
    
lemma srcdups_fst2snd: 
  assumes "s \<noteq> \<epsilon>" 
    and "a = shd s" 
  shows "srcdups\<cdot>(\<up>a \<bullet> s) = srcdups\<cdot>s"
  using assms by (metis srcdups_eq surj_scons)

(* used by dropwhile_smed *)
lemma dropwhile_shd_f: 
  assumes "shd s \<noteq> a" 
  shows "sdropwhile (\<lambda>x. x = a)\<cdot>s = s"
  using assms by (metis (full_types) sdropwhile_f strict_sdropwhile surj_scons)

(* used by slen_dropwhile_takewhile (for dropwhile2smed) *)
lemma dropwhile_inf_bot: "sdropwhile (\<lambda>x. x = a)\<cdot>\<up>a\<infinity> = \<epsilon>"
  proof -
    have h2:"\<forall>a. sdom\<cdot>\<up>a\<infinity> = {a}" 
      by simp
    have "\<And>a b s. sdropwhile (\<lambda>x. x = a)\<cdot>\<up>a\<infinity> = \<up>b \<bullet> s \<Longrightarrow> False"
      proof(case_tac "b=a")
        show "\<And>a b s. sdropwhile (\<lambda>x. x = a)\<cdot>\<up>a\<infinity> = \<up>b \<bullet> s \<Longrightarrow> b = a \<Longrightarrow> False"
          using sdropwhile_resup by blast
        show "\<And>a b s. sdropwhile (\<lambda>x. x = a)\<cdot>\<up>a\<infinity> = \<up>b \<bullet> s \<Longrightarrow> b \<noteq> a \<Longrightarrow> False"
          by (metis (no_types) Un_absorb h2 insert_commute insert_is_Un sdom2un 
              singleton_insert_inj_eq' srcdups_dom srcdups_step)
      qed
    then have "\<forall>a.(sdropwhile (\<lambda>x. x = a)\<cdot>(sinftimes (\<up>a))) = \<epsilon>"
      by (metis scases)
    thus ?thesis 
      by auto
  qed

(* used by  dropwhile2drop (for dropwhile2smed) *)
lemma slen_dropwhile_takewhile: 
  assumes "sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon>" 
  shows "#(stakewhile (\<lambda>x. x = a)\<cdot>s) \<noteq> \<infinity>"
  using assms
  proof (erule_tac contrapos_pp)
    have "#(stakewhile (\<lambda>x. x = a)\<cdot>s) = \<infinity> \<Longrightarrow> sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> False"
      using dropwhile_inf_bot stakewhile_sinftimesup by auto
    from this show "\<not> #(stakewhile (\<lambda>x. x = a)\<cdot>s) \<noteq> \<infinity> \<Longrightarrow> \<not> sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon>"
      by auto
  qed

(*used by dropwhile2smed*)
lemma dropwhile2drop: 
  "sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> \<exists>n .sdropwhile (\<lambda>x. x = a)\<cdot>s = sdrop n\<cdot>s"
  by (metis stakewhile_sdropwhilel1 ninf2Fin slen_dropwhile_takewhile)

(*used by  dropwhile_smed*)
lemma stakewhileDropwhile_rev: "s = stakewhile f\<cdot>s \<bullet> (sdropwhile f\<cdot>s)"
  by (simp add: stakewhileDropwhile)

(* used by smed_conc *)
lemma szip_slen_conc: "#ora \<le> #sa \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora =  szip\<cdot>sa\<cdot>ora"
  proof (induction k arbitrary: ora sa sb)
    case 0
    then show ?case
      by simp
  next
    case (Suc k)
    then show ?case 
      proof(rule_tac x=sa in scases)
        show "(\<And>ora sa sb. #ora \<le> #sa \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora) \<Longrightarrow>
          #ora \<le> #sa \<Longrightarrow> #sa = Fin (Suc k) \<Longrightarrow> sa = \<epsilon> \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora"
          by simp
        show "\<And>a s. (\<And>ora sa sb. #ora \<le> #sa \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora) \<Longrightarrow>
          #ora \<le> #sa \<Longrightarrow> #sa = Fin (Suc k) \<Longrightarrow> sa = \<up>a \<bullet> s \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora"    
          proof (rule_tac x=ora in scases)
              show "\<And>a s. (\<And>ora sa sb. #ora \<le> #sa \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora) \<Longrightarrow>
                #ora \<le> #sa \<Longrightarrow> #sa = Fin (Suc k) \<Longrightarrow> sa = \<up>a \<bullet> s \<Longrightarrow> ora = \<epsilon> \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora"
                by simp
              show "\<And>a s aa ss. (\<And>ora sa sb. #ora \<le> #sa \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora) \<Longrightarrow>
                #ora \<le> #sa \<Longrightarrow> #sa = Fin (Suc k) \<Longrightarrow> sa = \<up>a \<bullet> s \<Longrightarrow> ora = \<up>aa \<bullet> ss \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora"
                by (simp add: Suc(1) slen_scons)
          qed            
      qed
  qed

(* used by smed_conc *)
lemma szip_slen_conc2: 
  "#ora > #sa \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop k\<cdot>ora)"
  proof (induction k arbitrary: ora sa sb)
    case 0
    then show ?case
      by simp
  next
    case (Suc k)
    then show ?case
      proof (rule_tac x=sa in scases)
        show "(\<And>sa ora sb. #sa < #ora \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop k\<cdot>ora)) \<Longrightarrow>
          #sa < #ora \<Longrightarrow> #sa = Fin (Suc k) \<Longrightarrow> sa = \<epsilon> \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop (Suc k)\<cdot>ora)"
          by simp
        show "\<And>a s. (\<And>sa ora sb. #sa < #ora \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop k\<cdot>ora)) \<Longrightarrow>
          #sa < #ora \<Longrightarrow> #sa = Fin (Suc k) \<Longrightarrow> sa = \<up>a \<bullet> s \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop (Suc k)\<cdot>ora)"
          proof (rule_tac x=ora in scases)
            show "\<And>a s. (\<And>sa ora sb. #sa < #ora \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = 
              szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop k\<cdot>ora)) \<Longrightarrow> #sa < #ora \<Longrightarrow> #sa = Fin (Suc k) \<Longrightarrow> 
              sa = \<up>a \<bullet> s \<Longrightarrow> ora = \<epsilon> \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop (Suc k)\<cdot>ora)"
              by simp
            show "\<And>a s aa ss. (\<And>sa ora sb. #sa < #ora \<Longrightarrow> #sa = Fin k \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora =
              szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop k\<cdot>ora)) \<Longrightarrow> #sa < #ora \<Longrightarrow> #sa = Fin (Suc k) \<Longrightarrow> 
              sa = \<up>a \<bullet> s \<Longrightarrow> ora = \<up>aa \<bullet> ss \<Longrightarrow> szip\<cdot>(sa \<bullet> sb)\<cdot>ora = szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop (Suc k)\<cdot>ora)"
              by (simp add: Suc.IH)
          qed
      qed
  qed

(* used by smed_conc*)
lemma add_sfilter_rev:
  assumes "#x = Fin k" 
  shows "sfilter t\<cdot>x \<bullet> sfilter t\<cdot>y = sfilter t\<cdot>(x \<bullet> y)" 
  using assms
  by (simp add: add_sfilter)

(* used by dropwhile_smed *)
lemma sdropwhile_conc: 
  assumes "#sa = Fin k" 
  shows "sdropwhile (\<lambda>x. x = a)\<cdot>sa = \<epsilon> \<Longrightarrow> 
    sdropwhile (\<lambda>x. x = a)\<cdot>(sa \<bullet> sb) = sdropwhile (\<lambda>x. x = a)\<cdot>sb"
  proof (induction sa arbitrary: a sb rule: finind)
    show "#sa = Fin k"
      using assms by auto[1]
    show "\<And>a sb. sdropwhile (\<lambda>x. x = a)\<cdot>\<epsilon> = \<epsilon> \<Longrightarrow>
            sdropwhile (\<lambda>x. x = a)\<cdot>(\<epsilon> \<bullet> sb) = sdropwhile (\<lambda>x. x = a)\<cdot>sb"
      by simp
    show "\<And>a s aa sb. (\<And>a sb. sdropwhile (\<lambda>x. x = a)\<cdot>s = \<epsilon> \<Longrightarrow>
      sdropwhile (\<lambda>x. x = a)\<cdot>(s \<bullet> sb) = sdropwhile (\<lambda>x. x = a)\<cdot>sb) \<Longrightarrow> 
      sdropwhile (\<lambda>x. x = aa)\<cdot>(\<up>a \<bullet> s) = \<epsilon> \<Longrightarrow>
      sdropwhile (\<lambda>x. x = aa)\<cdot>((\<up>a \<bullet> s) \<bullet> sb) = sdropwhile (\<lambda>x. x = aa)\<cdot>sb" 
      proof (case_tac "aa=a")
        show "\<And>a s aa sb. (\<And>a sb. sdropwhile (\<lambda>x. x = a)\<cdot>s = \<epsilon> \<Longrightarrow>
          sdropwhile (\<lambda>x. x = a)\<cdot>(s \<bullet> sb) = sdropwhile (\<lambda>x. x = a)\<cdot>sb) \<Longrightarrow>
          sdropwhile (\<lambda>x. x = aa)\<cdot>(\<up>a \<bullet> s) = \<epsilon> \<Longrightarrow> aa = a \<Longrightarrow> 
          sdropwhile (\<lambda>x. x = aa)\<cdot>((\<up>a \<bullet> s) \<bullet> sb) = sdropwhile (\<lambda>x. x = aa)\<cdot>sb"
          by simp
        show "\<And>a s aa sb. (\<And>a sb. sdropwhile (\<lambda>x. x = a)\<cdot>s = \<epsilon> \<Longrightarrow>
          sdropwhile (\<lambda>x. x = a)\<cdot>(s \<bullet> sb) = sdropwhile (\<lambda>x. x = a)\<cdot>sb) \<Longrightarrow>
          sdropwhile (\<lambda>x. x = aa)\<cdot>(\<up>a \<bullet> s) = \<epsilon> \<Longrightarrow> aa \<noteq> a \<Longrightarrow> 
          sdropwhile (\<lambda>x. x = aa)\<cdot>((\<up>a \<bullet> s) \<bullet> sb) = sdropwhile (\<lambda>x. x = aa)\<cdot>sb"
          by (metis (full_types) sdropwhile_f srcdups_srt srcdups_step srcdupsimposs2 
          stream.sel_rews(2) strict_srcdups)
      qed
  qed

(* used by smed_newOra_srcdups_ex *)
lemma dropwhile_f: "s \<noteq> \<epsilon> \<Longrightarrow> shd s \<noteq> a \<Longrightarrow> s =  sdropwhile (\<lambda>x. x = a)\<cdot>s"
  by (metis (full_types) sdropwhile_f surj_scons)

(* used by smed_newOra_srcdups_ex *)
lemma ora_t_ex: "\<exists>ora1. P (\<up>True\<bullet>ora1) \<Longrightarrow> \<exists>ora2. P ora2"
  by auto    
    
lemma ora_f_ex: "\<exists>ora1. P (\<up>False\<bullet>ora1) \<Longrightarrow> \<exists>ora2. P ora2"
  by auto   

(*used by prop0 lemmata *)
lemma prop0_h:"#(srcdups\<cdot>(s\<bullet>s2)) \<le> #(srcdups\<cdot>(s\<bullet>\<up>b\<bullet>s2))"
  proof(induction rule: ind [of _ s])
    case 1
    then show ?case
      proof (rule admI)
        show "\<And>Y. chain Y \<Longrightarrow> \<forall>i. #(srcdups\<cdot>(Y i \<bullet> s2)) \<le> #(srcdups\<cdot>(Y i \<bullet> \<up>b \<bullet> s2)) \<Longrightarrow>
          #(srcdups\<cdot>((\<Squnion>i. Y i) \<bullet> s2)) \<le> #(srcdups\<cdot>((\<Squnion>i. Y i) \<bullet> \<up>b \<bullet> s2))"
          by (metis inf_chainl4 l42 order_refl sconc_fst_inf)
      qed
  next
    case 2
    then show ?case 
    proof -
      { assume "\<not> #(srcdups\<cdot>(\<epsilon> \<bullet> s2)) \<le> #(srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2))"
        { assume "srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2) \<noteq> \<up>b \<bullet> srcdups\<cdot>(\<up>(shd s2) \<bullet> srt\<cdot>s2)"
          { assume "srcdups\<cdot> (\<up>b \<bullet> \<up>(shd s2) \<bullet> srt\<cdot>s2) \<noteq> \<up>b \<bullet> srcdups\<cdot>(\<up>(shd s2) \<bullet> srt\<cdot>s2)"
            moreover
            { assume "srcdups\<cdot>(\<up>b \<bullet> \<up>(shd s2) \<bullet> srt\<cdot>s2) = srcdups\<cdot>(\<up>(shd s2) \<bullet> srt\<cdot>s2) 
                      \<and> srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2) \<noteq> srcdups\<cdot>(\<epsilon> \<bullet> s2)"
              then have "\<up>(shd s2) \<bullet> srt\<cdot>s2 \<noteq> s2"
                by force }
            ultimately have "\<up>(shd s2) \<bullet> srt\<cdot>s2 = s2 \<longrightarrow> #(srcdups\<cdot>(\<epsilon> \<bullet> s2)) \<le> #(srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2))"
              by (metis (no_types) eq_iff srcdups_eq2 srcdups_neq) }
          then have "\<up>(shd s2) \<bullet> srt\<cdot>s2 = s2 \<longrightarrow> #(srcdups\<cdot>(\<epsilon> \<bullet> s2)) \<le> #(srcdups\<cdot>(\<epsilon> \<bullet> \<up>b \<bullet> s2))"
            by force }
        moreover
        { assume "\<up>(shd s2) \<bullet> srt\<cdot>s2 \<noteq> s2"
          then have "s2 = \<epsilon>"
            by (metis surj_scons)
          then have ?thesis
            by force }
        ultimately have ?thesis
          by fastforce }
      then show ?thesis
        by metis
    qed
  next
    case (3 a s)
    then have case_epseq:"a=b \<Longrightarrow> #(srcdups\<cdot>(\<up>a \<bullet> s2)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> \<up>b \<bullet> s2))"
      by simp
    have case_epsneq:"a\<noteq>b \<Longrightarrow> #(srcdups\<cdot>(\<up>a \<bullet> s2)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> \<up>b \<bullet> s2))"
      proof (subst srcdups_neq)
        show "a \<noteq> b \<Longrightarrow> a \<noteq> b"
          by simp
        show "a \<noteq> b \<Longrightarrow> #(srcdups\<cdot>(\<up>a \<bullet> s2)) \<le> #(\<up>a \<bullet> srcdups\<cdot>(\<up>b \<bullet> s2))"
          proof (cases "s2=\<epsilon>")
            case True
            then show ?thesis
              by simp
          next
            case False
            then show ?thesis
              proof (cases "b=shd s2")
                case True
                then show ?thesis
                  by (metis False eq_iff less_lnsuc slen_scons srcdups_eq srcdups_nfst2snd surj_scons)        
              next
                case False
                then show ?thesis
                  using surj_scons[of s2] srcdups_neq[of b "shd s2" "srt\<cdot>s2"]
                  proof (simp)
                    have "\<up>(shd s2) \<bullet> srt\<cdot>s2 = s2 \<Longrightarrow> #(srcdups\<cdot>s2) \<le> lnsuc\<cdot>(lnsuc\<cdot>(#(srcdups\<cdot>s2)))"
                      by (meson dual_order.trans less_lnsuc)
                    then have "\<up>(shd s2) \<bullet> srt\<cdot>s2 = s2 \<Longrightarrow> #(srcdups\<cdot>(\<up>a \<bullet> s2)) \<le> lnsuc\<cdot>(lnsuc\<cdot>(#(srcdups\<cdot>s2)))"
                      by (metis (no_types) less_lnsuc slen_scons srcdups_eq2 srcdups_neq)
                    then show "b \<noteq> shd s2 \<Longrightarrow> (s2 \<noteq> \<epsilon> \<Longrightarrow> \<up>(shd s2) \<bullet> srt\<cdot>s2 = s2) \<Longrightarrow> 
                      #(srcdups\<cdot>(\<up>a \<bullet> s2)) \<le> lnsuc\<cdot>(#(srcdups\<cdot>(\<up>b \<bullet> s2)))"
                      using srcdups_nfst2snd by force
                  qed
              qed
          qed
      qed
    have case_eq: "s\<noteq>\<epsilon> \<Longrightarrow> a = shd s \<Longrightarrow> ?case"
      by (metis "3.IH" sconc_scons srcdups_eq surj_scons)
    have "s\<noteq>\<epsilon> \<Longrightarrow> a\<noteq>shd s \<Longrightarrow> ?case"
    proof -
      assume a1: "s \<noteq> \<epsilon>"
      assume a2: "a \<noteq> shd s"
      have "\<up>(shd s) \<bullet> srt\<cdot>s = s"
        using a1 by (meson surj_scons)
      then show ?thesis
        using a2 by (metis (no_types) "3.IH" lnsuc_lnle_emb sconc_scons slen_scons srcdups_neq)
    qed
    then show ?case
      using case_epseq case_epsneq case_eq by fastforce
  qed

(* ----------------------------------------------------------------------- *)
subsection {* additional properties of sMed *}
(* ----------------------------------------------------------------------- *)

lemma smed2med: 
  shows "sMed\<cdot>(sMed\<cdot>msg\<cdot>ora1)\<cdot>ora2 = sMed\<cdot>msg\<cdot>(newOracle\<cdot>ora1\<cdot>ora2 )"
  proof(induction msg arbitrary: ora1 ora2 rule: ind)
    case 1
    then show ?case
      by simp
  next
    case 2
    then show ?case
      by simp
  next
    case (3 a s)
    then show ?case
      proof (cases rule: oracases [of ora1])
        case bottom
        then show ?thesis by simp
      next
        case (true as)
        then show ?thesis 
          by (cases rule: oracases [of ora2], auto simp add: "3.IH")
      next
        case (false as)
        then show ?thesis       
          by (cases rule: oracases [of ora2], auto simp add: "3.IH")
      qed
  qed

lemma smed_smap: "sMed\<cdot>(smap f\<cdot>msg)\<cdot>ora = smap f\<cdot>(sMed\<cdot>msg\<cdot>ora)"
  proof (induct msg arbitrary: ora rule: ind)
    case 1
    then show ?case
      by simp
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    then show ?case
      by (cases rule: oracases [of ora], simp_all)
  qed

lemma smed_slen: "#(sMed\<cdot>msg\<cdot>ora) \<le> #msg"
  proof-
    have thesis_simp: "#(sprojfst\<cdot>({x. snd x} \<ominus> szip\<cdot>msg\<cdot>ora)) \<le> #msg"
      by (metis min.bounded_iff slen_sfilterl1 slen_sprojfst szip_len)
    thus ?thesis
      by (simp add: smed_insert)
  qed

text{* If there are k messages and k messages have been transmitted then the first message and 
       the first transmitted message are the same. *}
lemma smed_slen2shd:
  assumes "#msg \<noteq> \<infinity>"
    and "#(sMed\<cdot>msg\<cdot>ora) = #msg" 
  shows "shd (sMed\<cdot>msg\<cdot>ora) = shd msg"
  using assms
  proof (rule_tac x=msg in scases)
    show "msg = \<epsilon> \<Longrightarrow> shd (sMed\<cdot>msg\<cdot>ora) = shd msg"
      by simp
    show "\<And>a s. #msg \<noteq> \<infinity> \<Longrightarrow> #(sMed\<cdot>msg\<cdot>ora) = #msg \<Longrightarrow> msg = \<up>a \<bullet> s \<Longrightarrow> shd (sMed\<cdot>msg\<cdot>ora) = shd msg"
      proof(simp)
        fix a :: "'a" and s :: "'a stream" and as :: "bool stream"
        assume s_fin: "#s \<noteq> \<infinity>"
        assume msg_lscons: "msg = \<up>a \<bullet> s"
        show "#(sMed\<cdot>(\<up>a \<bullet> s)\<cdot>ora) = lnsuc\<cdot>(#s) \<Longrightarrow> shd (sMed\<cdot>(\<up>a \<bullet> s)\<cdot>ora) = a"
          proof (rule_tac ts=ora in oracases, simp_all)
            show "\<And>as. #(sMed\<cdot>s\<cdot>as) = lnsuc\<cdot>(#s) \<Longrightarrow> ora = \<up>False \<bullet> as \<Longrightarrow> shd (sMed\<cdot>s\<cdot>as) = a"
              by (metis antisym_conv2 dual_order.refl inf_ub le2lnle s_fin smed_slen)
          qed
      qed
  qed

lemma smed_slen2s:
  "#msg \<noteq> \<infinity> \<and> #(sMed\<cdot>msg\<cdot>ora) = #msg \<Longrightarrow> sMed\<cdot>msg\<cdot>ora = msg"
  proof (induction msg arbitrary: ora rule: ind)
    case 1
      have "\<And>x. adm (\<lambda>xa. #xa \<noteq> \<infinity> \<and> #(sMed\<cdot>xa\<cdot>x) = #xa \<longrightarrow> sMed\<cdot>xa\<cdot>x = xa)"
      proof (rule adm_imp)
        fix x :: "bool stream"
        have "adm (\<lambda>xa. #xa = \<infinity> \<or> #(sMed\<cdot>xa\<cdot>x) \<noteq> #xa)"
          by (metis (mono_tags, lifting) admI inf_chainl4 l42)
        from this show "adm (\<lambda>xa. \<not> (#xa \<noteq> \<infinity> \<and> #(sMed\<cdot>xa\<cdot>x) = #xa))"
          by simp
        show "\<And>x. adm (\<lambda>xa. sMed\<cdot>xa\<cdot>x = xa)"
          by simp
      qed
      then show ?case 
        by (rule adm_all)
  next
    case 2
    then show ?case 
      by simp
  next
    case (3 a s)
    then show ?case
      proof (rule_tac oracases [of ora])
        fix as :: "bool stream"
        assume s1: "\<And>ora. #s \<noteq> \<infinity> \<and> #(sMed\<cdot>s\<cdot>ora) = #s \<Longrightarrow> sMed\<cdot>s\<cdot>ora = s"
        assume s2: "#(\<up>a \<bullet> s) \<noteq> \<infinity> \<and> #(sMed\<cdot>(\<up>a \<bullet> s)\<cdot>ora) = #(\<up>a \<bullet> s)"
        show "ora = \<epsilon> \<Longrightarrow> sMed\<cdot>(\<up>a \<bullet> s)\<cdot>ora = \<up>a \<bullet> s"
          using s2 by auto
        show "ora = \<up>True \<bullet> as \<Longrightarrow> sMed\<cdot>(\<up>a \<bullet> s)\<cdot>ora = \<up>a \<bullet> s"
          using s1 s2 by fastforce
        show "ora = \<up>False \<bullet> as \<Longrightarrow> sMed\<cdot>(\<up>a \<bullet> s)\<cdot>ora = \<up>a \<bullet> s"
          by (metis "3.prems" antisym_conv1 inf_ub ln_less not_less slen_scons 
              smed_f smed_inftrue smed_slen)
      qed
  qed

lemma drop2smed: "sdrop n\<cdot>s = sMed\<cdot>s\<cdot>((sntimes n (\<up>False)) \<bullet> ((\<up>True)\<infinity>))" 
  proof (induction n arbitrary: s)
    case 0
    then show ?case 
      by (simp add: smed_inftrue)
  next
    case (Suc n)
    then show ?case 
      by (rule_tac x=s in scases, simp_all)
  qed

lemma dropwhile2smed: "\<exists>ora. sdropwhile (\<lambda>x. x = a)\<cdot>s = sMed\<cdot>s\<cdot>ora"
  proof (case_tac "sdropwhile (\<lambda>x. x = a)\<cdot>s = \<epsilon>")
    show "sdropwhile (\<lambda>x. x = a)\<cdot>s = \<epsilon> \<Longrightarrow> \<exists>ora. sdropwhile (\<lambda>x. x = a)\<cdot>s = sMed\<cdot>s\<cdot>ora"
      by (metis (no_types) smed_bot2)
    show "sdropwhile (\<lambda>x. x = a)\<cdot>s \<noteq> \<epsilon> \<Longrightarrow> \<exists>ora. sdropwhile (\<lambda>x. x = a)\<cdot>s = sMed\<cdot>s\<cdot>ora"
      by (metis dropwhile2drop drop2smed)
  qed

lemma smed_dtw: "sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>(stakewhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora) = \<epsilon>"
  proof (induction s arbitrary: a ora rule: ind,simp_all)
    show "\<And>a s aa ora. (\<And>a ora. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>(stakewhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora) = \<epsilon>) \<Longrightarrow>
      sdropwhile (\<lambda>x. x = aa)\<cdot>(sMed\<cdot>(stakewhile (\<lambda>x. x = aa)\<cdot>(\<up>a \<bullet> s))\<cdot>ora) = \<epsilon>" 
      proof (case_tac "aa=a",simp_all)
        show "\<And>a s aa ora. (\<And>a ora. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>(stakewhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora) = \<epsilon>) \<Longrightarrow>
          aa = a \<Longrightarrow> sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>(\<up>a \<bullet> stakewhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora) = \<epsilon>"
          by (rule_tac ts=ora in oracases, simp_all)
      qed
  qed

lemma smed_conc: "\<exists>ora2. sMed\<cdot>(sa \<bullet> sb)\<cdot>ora = sMed\<cdot>sa\<cdot>ora \<bullet> sMed\<cdot>sb\<cdot>ora2"
  proof (case_tac "#sa = \<infinity>", simp)
    show "#sa = \<infinity> \<Longrightarrow> \<exists>ora2. sMed\<cdot>sa\<cdot>ora = sMed\<cdot>sa\<cdot>ora \<bullet> sMed\<cdot>sb\<cdot>ora2"
      by (metis (no_types) sconc_snd_empty smed_bot2)
    show "#sa \<noteq> \<infinity> \<Longrightarrow> \<exists>ora2. sMed\<cdot>(sa \<bullet> sb)\<cdot>ora = sMed\<cdot>sa\<cdot>ora \<bullet> sMed\<cdot>sb\<cdot>ora2"
      using ninf2Fin [of "#sa"] 
      proof (case_tac "#ora \<le> #sa",auto)
        show "\<And>k. #ora \<le> Fin k \<Longrightarrow> #sa = Fin k \<Longrightarrow> 
          \<exists>ora2. sMed\<cdot>(sa \<bullet> sb)\<cdot>ora = sMed\<cdot>sa\<cdot>ora \<bullet> sMed\<cdot>sb\<cdot>ora2"
          by (rule_tac x=\<epsilon> in exI, simp add: smed_insert szip_slen_conc)
        show "\<And>k. \<not> #ora \<le> Fin k \<Longrightarrow> #sa = Fin k \<Longrightarrow> 
          \<exists>ora2. sMed\<cdot>(sa \<bullet> sb)\<cdot>ora = sMed\<cdot>sa\<cdot>ora \<bullet> sMed\<cdot>sb\<cdot>ora2"
          proof (rule_tac x="sdrop k\<cdot>ora" in exI, simp add: smed_insert sprojfst_def, 
                 fold smap_split, subst add_sfilter_rev [of "szip\<cdot>sa\<cdot>ora" k]) 
            show "\<And>k. \<not> #ora \<le> Fin k \<Longrightarrow> #sa = Fin k \<Longrightarrow> #(szip\<cdot>sa\<cdot>ora) = Fin k"
              by (simp add: min.absorb1)
            show "\<And>k. \<not> #ora \<le> Fin k \<Longrightarrow> #sa = Fin k \<Longrightarrow> smap fst\<cdot>(Collect snd \<ominus> szip\<cdot>(sa \<bullet> sb)\<cdot>ora) =
              smap fst\<cdot>(Collect snd \<ominus> szip\<cdot>sa\<cdot>ora \<bullet> szip\<cdot>sb\<cdot>(sdrop k\<cdot>ora))"
              by (simp add: szip_slen_conc2)
          qed
      qed
    qed


lemma dropwhile_smed: 
  "\<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>s\<cdot>ora) = sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2"
  proof (case_tac "s= \<epsilon>", simp) 
    show "s \<noteq> \<epsilon> \<Longrightarrow> \<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>s\<cdot>ora) = sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2"
      proof (case_tac "(sMed\<cdot>s\<cdot>ora) = \<epsilon>", simp)
        show "s \<noteq> \<epsilon> \<Longrightarrow> sMed\<cdot>s\<cdot>ora = \<epsilon> \<Longrightarrow> \<exists>ora2. sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2 = \<epsilon>"
          using smed_bot2 by blast
        show "s \<noteq> \<epsilon> \<Longrightarrow> sMed\<cdot>s\<cdot>ora \<noteq> \<epsilon> \<Longrightarrow>
          \<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>s\<cdot>ora) = sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2"
          proof (case_tac "shd s \<noteq> a")
            show "s \<noteq> \<epsilon> \<Longrightarrow> sMed\<cdot>s\<cdot>ora \<noteq> \<epsilon> \<Longrightarrow> shd s \<noteq> a \<Longrightarrow>
              \<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>s\<cdot>ora) = sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2"
              proof (case_tac "shd (sMed\<cdot>s\<cdot>ora) \<noteq> a")
                show "s \<noteq> \<epsilon> \<Longrightarrow> sMed\<cdot>s\<cdot>ora \<noteq> \<epsilon> \<Longrightarrow> shd s \<noteq> a \<Longrightarrow> shd (sMed\<cdot>s\<cdot>ora) \<noteq> a \<Longrightarrow>
                  \<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>s\<cdot>ora) = sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2"
                  by (simp add: dropwhile_shd_f,blast)
                show "s \<noteq> \<epsilon> \<Longrightarrow> sMed\<cdot>s\<cdot>ora \<noteq> \<epsilon> \<Longrightarrow> shd s \<noteq> a \<Longrightarrow> \<not> shd (sMed\<cdot>s\<cdot>ora) \<noteq> a \<Longrightarrow>
                  \<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>s\<cdot>ora) = sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2"
                  by (metis dropwhile2smed dropwhile_shd_f smed2med)
              qed
            show "s \<noteq> \<epsilon> \<Longrightarrow> sMed\<cdot>s\<cdot>ora \<noteq> \<epsilon> \<Longrightarrow> \<not> shd s \<noteq> a \<Longrightarrow>
              \<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>s\<cdot>ora) = sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2"
              proof (subst stakewhileDropwhile_rev [of s "(\<lambda>x. x = a)"], simp)
                show "s \<noteq> \<epsilon> \<Longrightarrow> sMed\<cdot>s\<cdot>ora \<noteq> \<epsilon> \<Longrightarrow> shd s = a \<Longrightarrow>
                  \<exists>ora2. sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>(stakewhile (\<lambda>x. x = a)\<cdot>s \<bullet> 
                  sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora) = sMed\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)\<cdot>ora2"
                  using smed_conc [of "stakewhile (\<lambda>x. x = a)\<cdot>s" "sdropwhile (\<lambda>x. x = a)\<cdot>s" ora]
                  proof (case_tac "#(sMed\<cdot>(stakewhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora) = \<infinity>", auto)
                    show "s \<noteq> \<epsilon> \<Longrightarrow> sMed\<cdot>s\<cdot>ora \<noteq> \<epsilon> \<Longrightarrow> #(sMed\<cdot>(stakewhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora) = \<infinity> 
                      \<Longrightarrow> sMed\<cdot>(stakewhile (\<lambda>x. x = shd s)\<cdot>s \<bullet> sdropwhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora =
                      sMed\<cdot>(stakewhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora \<Longrightarrow> a = shd s \<Longrightarrow>
                      \<exists>ora2. sdropwhile (\<lambda>x. x = shd s)\<cdot>(sMed\<cdot>(stakewhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora) =
                      sMed\<cdot>(sdropwhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora2"
                      by (metis smed_bot2 smed_dtw)
                    show "\<And>ora2. s \<noteq> \<epsilon> \<Longrightarrow> sMed\<cdot>s\<cdot>ora \<noteq> \<epsilon> \<Longrightarrow> #(sMed\<cdot>(stakewhile(\<lambda>x. x =shd s)\<cdot>s)\<cdot>ora) 
                      \<noteq> \<infinity> \<Longrightarrow> a = shd s \<Longrightarrow> sMed\<cdot>(stakewhile (\<lambda>x. x = shd s)\<cdot>s \<bullet> 
                      sdropwhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora = sMed\<cdot>(stakewhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora \<bullet> 
                      sMed\<cdot>(sdropwhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora2 \<Longrightarrow> \<exists>ora2a. sdropwhile (\<lambda>x. x = shd s)\<cdot>
                      (sMed\<cdot>(stakewhile(\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora \<bullet> sMed\<cdot>(sdropwhile(\<lambda>x. x =shd s)\<cdot>s)\<cdot>ora2) 
                      = sMed\<cdot>(sdropwhile (\<lambda>x. x = shd s)\<cdot>s)\<cdot>ora2a"
                      by (metis sdropwhile_conc smed_dtw ninf2Fin dropwhile2smed smed2med)
                  qed
              qed
          qed
      qed
  qed

lemma smed_dropwhile_t: 
  "(sMed\<cdot>sa\<cdot>as) \<noteq> \<epsilon> \<Longrightarrow> shd (sMed\<cdot>sa\<cdot>as) = a \<Longrightarrow> srcdups\<cdot>(sMed\<cdot>sa\<cdot>as) = \<up>a \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>(sMed\<cdot>sa\<cdot>as))"
  proof (rule_tac x="sMed\<cdot>sa\<cdot>as" in scases, simp_all)
    show "\<And>aa s. aa = a \<Longrightarrow> sMed\<cdot>sa\<cdot>as = \<up>a \<bullet> s \<Longrightarrow> 
      srcdups\<cdot>(\<up>a \<bullet> s) = \<up>a \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = a)\<cdot>s)"
      by (simp add: srcdups_step)
  qed

lemma srcdups_smed_h: " #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)"
  proof (induction s arbitrary: p rule: ind)
    case 1
    then show ?case 
      proof (rule adm_all, rule admI)
        show "\<And>x Y. chain Y \<Longrightarrow> \<forall>i. #(srcdups\<cdot>(sMed\<cdot>(Y i)\<cdot>x)) \<le> #(srcdups\<cdot>(Y i)) \<Longrightarrow>
          #(srcdups\<cdot>(sMed\<cdot>(\<Squnion>i. Y i)\<cdot>x)) \<le> #(srcdups\<cdot>(\<Squnion>i. Y i))"
          by(simp add: contlub_cfun_arg contlub_cfun_fun lub_mono2)
      qed
  next
    case 2
    then show ?case by simp
  next
    case (3 a s)
    then show ?case 
      proof (case_tac "s= \<epsilon>")
        show "(\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow>
          s = \<epsilon> \<Longrightarrow> #(srcdups\<cdot>(sMed\<cdot>(\<up>a \<bullet> s)\<cdot>p)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
          proof (cases rule: oracases, simp)
            show "\<And>as. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow>
              s = \<epsilon> \<Longrightarrow> p = \<up>True \<bullet> as \<Longrightarrow> #(srcdups\<cdot>(sMed\<cdot>(\<up>a \<bullet> s)\<cdot>p)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
              by (metis eq_refl smed_bot1 smed_t)
            show "\<And>as. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow>
              s = \<epsilon> \<Longrightarrow> p = \<up>False \<bullet> as \<Longrightarrow> #(srcdups\<cdot>(sMed\<cdot>(\<up>a \<bullet> s)\<cdot>p)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
              by (metis bot_is_0 eq_bottom_iff le_cases lnle_def 
                  smed_bot1 smed_f strict_slen strict_srcdups)
          qed
        show "(\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow> 
          s \<noteq> \<epsilon> \<Longrightarrow> #(srcdups\<cdot>(sMed\<cdot>(\<up>a \<bullet> s)\<cdot>p)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
          proof (cases rule: oracases, simp_all)
            show "\<And>as. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow>
              s \<noteq> \<epsilon> \<Longrightarrow> p = \<up>True \<bullet> as \<Longrightarrow> #(srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>as)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
              proof (case_tac "sMed\<cdot>s\<cdot>as = \<epsilon>")
                show "\<And>as. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow> s \<noteq> \<epsilon> \<Longrightarrow> p = \<up>True \<bullet> as 
                  \<Longrightarrow> sMed\<cdot>s\<cdot>as = \<epsilon> \<Longrightarrow> #(srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>as)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
                  by (simp add: neq02Suclnle srcdups_nbot)
                show " \<And>as. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow> s \<noteq> \<epsilon> \<Longrightarrow> p = \<up>True \<bullet> as 
                  \<Longrightarrow> sMed\<cdot>s\<cdot>as \<noteq> \<epsilon> \<Longrightarrow> #(srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>as)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))" 
                  proof (case_tac "shd s = a")
                    show "\<And>as. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow> s \<noteq> \<epsilon> \<Longrightarrow>
                      p = \<up>True \<bullet> as \<Longrightarrow> sMed\<cdot>s\<cdot>as \<noteq> \<epsilon> \<Longrightarrow> shd s = a \<Longrightarrow> 
                      #(srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>as)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
                      proof (case_tac "shd (sMed\<cdot>s\<cdot>as) = a")
                        show "\<And>as. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow> s \<noteq> \<epsilon> \<Longrightarrow>
                          p = \<up>True \<bullet> as \<Longrightarrow> sMed\<cdot>s\<cdot>as \<noteq> \<epsilon> \<Longrightarrow> shd s = a \<Longrightarrow> shd (sMed\<cdot>s\<cdot>as) = a \<Longrightarrow> 
                          #(srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>as)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
                          by (simp add: srcdups_fst2snd)
                        show "\<And>as. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow> s \<noteq> \<epsilon> \<Longrightarrow>
                          p = \<up>True \<bullet> as \<Longrightarrow> sMed\<cdot>s\<cdot>as \<noteq> \<epsilon> \<Longrightarrow> shd s = a \<Longrightarrow> shd (sMed\<cdot>s\<cdot>as) \<noteq> a \<Longrightarrow> 
                          #(srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>as)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
                          proof (cases rule: oracases,simp_all)
                            show "\<And>as asa. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow> s \<noteq> \<epsilon> \<Longrightarrow>
                              p = \<up>True \<bullet> \<up>True \<bullet> asa \<Longrightarrow> sMed\<cdot>s\<cdot>(\<up>True \<bullet> asa) \<noteq> \<epsilon> \<Longrightarrow> shd s = a \<Longrightarrow>
                              shd (sMed\<cdot>s\<cdot>(\<up>True \<bullet> asa)) \<noteq> a \<Longrightarrow> as = \<up>True \<bullet> asa \<Longrightarrow> 
                              #(srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>(\<up>True \<bullet> asa))) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
                              by (metis inject_scons smed_t surj_scons)
                            show "\<And>as asa. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow> s \<noteq> \<epsilon> \<Longrightarrow>
                              p = \<up>True \<bullet> \<up>False \<bullet> asa \<Longrightarrow> sMed\<cdot>s\<cdot>(\<up>False \<bullet> asa) \<noteq> \<epsilon> \<Longrightarrow> shd s = a 
                              \<Longrightarrow> shd (sMed\<cdot>s\<cdot>(\<up>False \<bullet> asa)) \<noteq> a \<Longrightarrow> as = \<up>False \<bullet> asa \<Longrightarrow> 
                              #(srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>(\<up>False \<bullet> asa))) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
                              by (metis smed_f smed_t srcdups_fst2snd surj_scons)
                          qed
                      qed
                    show "\<And>as. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow> s \<noteq> \<epsilon> \<Longrightarrow>
                      p = \<up>True \<bullet> as \<Longrightarrow> sMed\<cdot>s\<cdot>as \<noteq> \<epsilon> \<Longrightarrow> shd s \<noteq> a \<Longrightarrow> 
                      #(srcdups\<cdot>(\<up>a \<bullet> sMed\<cdot>s\<cdot>as)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))"
                      by (metis srcdups_nfst2snd dropwhile2smed lnsuc_lnle_emb 
                          slen_scons smed2med srcdups_step)
                  qed
              qed
            show "\<And>as. (\<And>p. #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<le> #(srcdups\<cdot>s)) \<Longrightarrow> s \<noteq> \<epsilon> \<Longrightarrow> p = \<up>False \<bullet> as \<Longrightarrow> 
              #(srcdups\<cdot>(sMed\<cdot>s\<cdot>as)) \<le> #(srcdups\<cdot>(\<up>a \<bullet> s))" 
              by (metis (no_types, lifting) srcdups_nfst2snd less_lnsuc srcdups_nfst2snd 
                  srcdups_fst2snd slen_scons trans_lnle)
          qed
      qed
    qed    

lemma smed_newOra_srcdups_ex: 
  assumes "#(srcdups\<cdot>msg) = Fin n" 
  shows "\<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2"
  proof (induction "srcdups\<cdot>msg"  arbitrary: msg  ora1 rule: finind)
    show "#(srcdups\<cdot>msg) = Fin n"
      using assms by simp
    show "\<And>msg ora1. \<epsilon> = srcdups\<cdot>msg \<Longrightarrow> \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2"
      by (metis smed_bot1 srcdups_nbot)
    show "\<And>a s msg ora1. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
      \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = srcdups\<cdot>msg \<Longrightarrow> 
      \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2 "
      proof (rule_tac x=msg in scases, simp)
        show "\<And>a s msg ora1 aa sa. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
          \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = srcdups\<cdot>msg \<Longrightarrow>
          msg = \<up>aa \<bullet> sa \<Longrightarrow> \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2"       
          proof (rule_tac ts=ora1 in oracases,simp_all)
            show "\<And>a s msg ora1 aa sa. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
              \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = srcdups\<cdot>(\<up>aa \<bullet> sa) 
              \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow> ora1 = \<epsilon> \<Longrightarrow> \<exists>ora2. sMed\<cdot>(srcdups\<cdot>(\<up>aa \<bullet> sa))\<cdot>ora2 = \<epsilon>"
              using smed_bot2 by blast
            show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
              \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = srcdups\<cdot>(\<up>aa \<bullet> sa) 
              \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow> ora1 = \<up>True \<bullet> as \<Longrightarrow> 
              \<exists>ora2. srcdups\<cdot>(\<up>aa \<bullet> sMed\<cdot>sa\<cdot>as) = sMed\<cdot>(srcdups\<cdot>(\<up>aa \<bullet> sa))\<cdot>ora2"
              proof (rule ora_t_ex, simp add: srcdups_step)
                show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
                  \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = 
                  \<up>aa \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa) \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow> ora1 = \<up>True \<bullet> as 
                  \<Longrightarrow> \<exists>ora1. \<up>aa \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>(sMed\<cdot>sa\<cdot>as)) =
                  \<up>aa \<bullet> sMed\<cdot>(srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa))\<cdot>ora1"
                  by (metis inject_scons dropwhile_smed)
              qed
            show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
              \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = srcdups\<cdot>(\<up>aa \<bullet> sa) 
              \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow> ora1 = \<up>False \<bullet> as \<Longrightarrow> \<exists>ora2. srcdups\<cdot>(sMed\<cdot>sa\<cdot>as) = 
              sMed\<cdot>(srcdups\<cdot>(\<up>aa \<bullet> sa))\<cdot>ora2"
              proof (case_tac "sa = \<epsilon>")
                show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
                  \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = 
                  srcdups\<cdot>(\<up>aa \<bullet> sa) \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow> ora1 = \<up>False \<bullet> as \<Longrightarrow>
                  sa = \<epsilon> \<Longrightarrow> \<exists>ora2. srcdups\<cdot>(sMed\<cdot>sa\<cdot>as) = sMed\<cdot>(srcdups\<cdot>(\<up>aa \<bullet> sa))\<cdot>ora2"
                  by (metis smed_bot1 smed_bot2 strict_srcdups)
                show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
                  \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = 
                  srcdups\<cdot>(\<up>aa \<bullet> sa) \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow> ora1 = \<up>False \<bullet> as \<Longrightarrow> sa \<noteq> \<epsilon> \<Longrightarrow> 
                  \<exists>ora2. srcdups\<cdot>(sMed\<cdot>sa\<cdot>as) = sMed\<cdot>(srcdups\<cdot>(\<up>aa \<bullet> sa))\<cdot>ora2"
                  proof (case_tac "shd sa \<noteq> aa", simp add: srcdups_nfst2snd, rule ora_f_ex, simp)
                    show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
                      \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = 
                      \<up>aa \<bullet> srcdups\<cdot>sa \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow> ora1 = \<up>False \<bullet> as \<Longrightarrow> sa \<noteq> \<epsilon> \<Longrightarrow> 
                      shd sa \<noteq> aa \<Longrightarrow> \<exists>ora1. srcdups\<cdot>(sMed\<cdot>sa\<cdot>as) = sMed\<cdot>(srcdups\<cdot>sa)\<cdot>ora1"
                      by (meson inject_scons)
                    show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
                      \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = 
                      srcdups\<cdot>(\<up>aa \<bullet> sa) \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow> ora1 = \<up>False \<bullet> as \<Longrightarrow> sa \<noteq> \<epsilon> \<Longrightarrow> 
                      \<not> shd sa \<noteq> aa \<Longrightarrow> \<exists>ora2. srcdups\<cdot>(sMed\<cdot>sa\<cdot>as) = sMed\<cdot>(srcdups\<cdot>(\<up>aa \<bullet> sa))\<cdot>ora2"
                      proof (simp add: srcdups_step, case_tac "sMed\<cdot>sa\<cdot>as = \<epsilon>")
                        show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
                          \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = 
                          \<up>aa \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa) \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow> ora1 = 
                          \<up>False \<bullet> as \<Longrightarrow> sa \<noteq> \<epsilon> \<Longrightarrow> shd sa = aa \<Longrightarrow> sMed\<cdot>sa\<cdot>as = \<epsilon> \<Longrightarrow> \<exists>ora2. 
                          srcdups\<cdot>(sMed\<cdot>sa\<cdot>as) = sMed\<cdot>(\<up>aa \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa))\<cdot>ora2"                  
                          by (metis smed_bot2 strict_srcdups)
                        show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
                          \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow> \<up>a \<bullet> s = 
                          \<up>aa \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa) \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow>
                          ora1 = \<up>False \<bullet> as \<Longrightarrow> sa \<noteq> \<epsilon> \<Longrightarrow> shd sa = aa \<Longrightarrow> sMed\<cdot>sa\<cdot>as \<noteq> \<epsilon> \<Longrightarrow>
                          \<exists>ora2. srcdups\<cdot>(sMed\<cdot>sa\<cdot>as) = 
                          sMed\<cdot>(\<up>aa \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa))\<cdot>ora2"
                          proof (case_tac "shd (sMed\<cdot>sa\<cdot>as) = aa", rule ora_t_ex, simp, 
                                 simp add: smed_dropwhile_t)
                            show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
                              \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow>
                              \<up>a \<bullet> s = \<up>aa \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa) \<Longrightarrow> msg = \<up>aa \<bullet> sa 
                              \<Longrightarrow> ora1 = \<up>False \<bullet> as \<Longrightarrow> sa \<noteq> \<epsilon> \<Longrightarrow> shd sa = aa \<Longrightarrow> sMed\<cdot>sa\<cdot>as \<noteq> \<epsilon> 
                              \<Longrightarrow> shd (sMed\<cdot>sa\<cdot>as) = aa \<Longrightarrow> \<exists>ora1. \<up>aa \<bullet> 
                              srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>(sMed\<cdot>sa\<cdot>as)) =
                              \<up>aa \<bullet> sMed\<cdot>(srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa))\<cdot>ora1"
                              by (metis inject_scons dropwhile_smed)
                            show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
                              \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow>
                              \<up>a \<bullet> s = \<up>aa \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa) \<Longrightarrow> msg = \<up>aa \<bullet> sa 
                              \<Longrightarrow> ora1 = \<up>False \<bullet> as \<Longrightarrow> sa \<noteq> \<epsilon> \<Longrightarrow> shd sa = aa \<Longrightarrow> sMed\<cdot>sa\<cdot>as \<noteq> \<epsilon> 
                              \<Longrightarrow> shd (sMed\<cdot>sa\<cdot>as) \<noteq> aa \<Longrightarrow> \<exists>ora2. srcdups\<cdot>(sMed\<cdot>sa\<cdot>as) = 
                              sMed\<cdot>(\<up>aa \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa))\<cdot>ora2"
                              proof (rule ora_f_ex,simp, subst dropwhile_f [of "sMed\<cdot>sa\<cdot>as" aa], 
                                     simp_all)
                                show "\<And>a s msg ora1 aa sa as. (\<And>msg ora1. s = srcdups\<cdot>msg \<Longrightarrow> 
                                  \<exists>ora2. srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora1) = sMed\<cdot>(srcdups\<cdot>msg)\<cdot>ora2) \<Longrightarrow>
                                  \<up>a \<bullet> s = \<up>aa \<bullet> srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa) \<Longrightarrow>
                                  msg = \<up>aa \<bullet> sa \<Longrightarrow> ora1 = \<up>False \<bullet> as \<Longrightarrow> sa \<noteq> \<epsilon> \<Longrightarrow> shd sa = aa 
                                  \<Longrightarrow> sMed\<cdot>sa\<cdot>as \<noteq> \<epsilon> \<Longrightarrow> shd (sMed\<cdot>sa\<cdot>as) \<noteq> aa \<Longrightarrow> 
                                  \<exists>ora1. srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>(sMed\<cdot>sa\<cdot>as)) =
                                  sMed\<cdot>(srcdups\<cdot>(sdropwhile (\<lambda>x. x = aa)\<cdot>sa))\<cdot>ora1"
                                  by (metis inject_scons dropwhile_smed)
                              qed
                          qed
                      qed
                  qed
              qed
          qed
      qed
    qed
        
 (* Frage? haves *)
lemma smed_slen2smed2: 
  assumes "#(srcdups\<cdot>s) \<noteq> \<infinity>" "#({True} \<ominus> p) = \<infinity>" 
    and "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) = #(srcdups\<cdot>s)"  
    and "#(srcdups\<cdot>(sprojsnd\<cdot>s))= #(srcdups\<cdot>s)" 
  shows "(srcdups\<cdot>s) = (srcdups\<cdot>(sMed\<cdot>s\<cdot>p))" 
  using assms proof (erule_tac contrapos_np)
    have h1: "srcdups\<cdot>s \<noteq> srcdups\<cdot>(sMed\<cdot>s\<cdot>p) \<Longrightarrow> #(srcdups\<cdot>s) = \<infinity> \<or> #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<noteq> #(srcdups\<cdot>s)"
      by (metis infI smed_newOra_srcdups_ex smed_slen2s)   
    have "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) \<noteq> #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<Longrightarrow>  
      #(srcdups\<cdot>(sprojsnd\<cdot>s)) \<noteq> #(srcdups\<cdot>s)"
      by (metis (no_types) antisym_conv assms(3) slen_sprojsnd sprojsnd_srcdups_slen srcdups_smed_h) 
    then have "#({True} \<ominus> p) = \<infinity> \<Longrightarrow>
      #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) = #(srcdups\<cdot>s) \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>s)) = #(srcdups\<cdot>s) 
      \<Longrightarrow> srcdups\<cdot>s \<noteq> srcdups\<cdot>(sMed\<cdot>s\<cdot>p) \<Longrightarrow> #(srcdups\<cdot>s) \<noteq> #(srcdups\<cdot>(sMed\<cdot>s\<cdot>p)) \<Longrightarrow> #(srcdups\<cdot>s) = \<infinity>"
      by simp   
    from this h1 show "#({True} \<ominus> p) = \<infinity> \<Longrightarrow>
      #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>s\<cdot>p))) = #(srcdups\<cdot>s) \<Longrightarrow>
      #(srcdups\<cdot>(sprojsnd\<cdot>s)) = #(srcdups\<cdot>s) \<Longrightarrow> srcdups\<cdot>s \<noteq> srcdups\<cdot>(sMed\<cdot>s\<cdot>p) \<Longrightarrow> #(srcdups\<cdot>s) = \<infinity>"
    by fastforce
  qed

lemma smed_slen2smed:
  "#(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>msg\<cdot>ora))) \<noteq> \<infinity> \<Longrightarrow> #({True} \<ominus> ora) = \<infinity> 
     \<Longrightarrow> #(sprojfst\<cdot>(srcdups\<cdot>msg)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>msg\<cdot>ora))) 
     \<Longrightarrow> #(srcdups\<cdot>(sprojsnd\<cdot>msg)) = #(srcdups\<cdot>(sprojsnd\<cdot>(sMed\<cdot>msg\<cdot>ora))) 
     \<Longrightarrow> sprojfst\<cdot>(srcdups\<cdot>msg) = sprojfst\<cdot>(srcdups\<cdot>(sMed\<cdot>msg\<cdot>ora))"
  by (metis slen_sprojfst smed_slen2smed2)




(* property 4 *)
lemma ora_inf: 
  assumes "#({True} \<ominus> p) = \<infinity>" 
  shows " #p = \<infinity>"
  using sfilterl4 assms  by auto

text {* @{term sdropwhile} after @{term stakewhile} gives the empty stream *}
lemma dtw: "sdropwhile f\<cdot>(stakewhile f\<cdot>s) = \<epsilon>"
  proof (rule ind [of _ s], auto)
    show "\<And>a s. sdropwhile f\<cdot>(stakewhile f\<cdot>s) = \<epsilon> \<Longrightarrow> sdropwhile f\<cdot>(stakewhile f\<cdot>(\<up>a \<bullet> s)) = \<epsilon>"
      by (case_tac "f a", auto)
  qed

lemma split_stream_rev: "s = stake n\<cdot>s \<bullet> sdrop n\<cdot>s " 
  by simp

lemma srcdups_fin:"#(srcdups\<cdot>msg) = Fin n \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow>\<exists>n2.  #(srcdups\<cdot>sa) = Fin n2" 
  proof (case_tac "shd sa = aa")
    show "#(srcdups\<cdot>msg) = Fin n \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow> shd sa = aa \<Longrightarrow> \<exists>n2. #(srcdups\<cdot>sa) = Fin n2"
      by (metis Fin_02bot lnzero_def only_empty_has_length_0 srcdups_eq strict_srcdups surj_scons)
    show "#(srcdups\<cdot>msg) = Fin n \<Longrightarrow> msg = \<up>aa \<bullet> sa \<Longrightarrow> shd sa \<noteq> aa \<Longrightarrow> \<exists>n2. #(srcdups\<cdot>sa) = Fin n2"
      by (metis fold_inf infI slen_scons srcdups_nfst2snd)
  qed


end
