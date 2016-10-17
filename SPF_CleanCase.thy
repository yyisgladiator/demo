theory SPF_CleanCase
imports SPF StreamTheorie

begin


setup_lifting type_definition_StBundle
setup_lifting type_definition_SPF
setup_lifting type_definition_SPS


(* to simplify the welltyped proofs define that alle Channels have the type "Nat" *)
lemma ctype_simp [simp]: "ctype c = range Nat"
using ctype.elims by blast



  (* sSum takes 2 nat-streams and adds them component-wise *)
definition sSum:: "nat stream \<rightarrow> nat stream \<rightarrow> nat stream" where
"sSum \<equiv> \<Lambda> s1 s2 . smap (\<lambda> s3. (fst s3) + (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2)"


  (* sSum takes 2 M-streams and adds them component-wise. *)
  (* all elements need to be in "range Nat" *)
definition sSumLift:: "M stream \<rightarrow> M stream \<rightarrow> M stream" where
"sSumLift \<equiv> \<Lambda> s1 s2. Nat_st\<cdot>(sSum\<cdot>(Nat_st_inv\<cdot>s1)\<cdot>(Nat_st_inv\<cdot>s2))"


      (* First general lemmas about the newly defined function "sSum" *)
      
      
        (* sZip is strict. Used to show strictness of sSum *)
      lemma szip2eps[simp]: assumes "xs=\<epsilon> \<or> ys=\<epsilon>"
        shows "szip\<cdot>xs\<cdot>ys = \<epsilon>"
      using assms strict_szip_fst strict_szip_snd by blast
      
        (* sSum is strict *)
      lemma ssum2eps[simp]: assumes "xs=\<epsilon> \<or> ys=\<epsilon>"
        shows "sSum\<cdot>xs\<cdot>ys = \<epsilon>"
      by(simp add: sSum_def assms)
      
        (* one iteration of sSum *)
      lemma ssum_unfold: "sSum\<cdot>(\<up>x \<bullet> xs)\<cdot>(\<up>y \<bullet> ys) = \<up>(x+y) \<bullet> sSum\<cdot>xs\<cdot>ys "
      by(simp add: sSum_def)
      
      
      lemma ssum2sinftimes[simp]: "sSum\<cdot>(\<up>x\<infinity>)\<cdot>(\<up>y\<infinity>) = sinftimes (\<up>(x+y))"
      by(simp add: smap2sinf2 sSum_def)
      
      
      lemma ssum_one [simp]: "sSum\<cdot>(\<up>x)\<cdot>(\<up>y) = \<up>(x+y)"
      by (metis nat_1_add_1 numeral_Bit1 numeral_One one_plus_numeral_commute sconc_snd_empty ssum2eps ssum_unfold)
      
       
      lemma ssumlift_well[simp]: "sdom\<cdot>(sSumLift\<cdot>s1\<cdot>s2) \<subseteq> range Nat "
      by (simp add: nat_st_sdom sSumLift_def)
      
      lemma ssumlift_unfold: "sSumLift\<cdot>((\<up>\<N> x) \<bullet> xs)\<cdot>((\<up>\<N> y) \<bullet> ys) = (\<up>\<N> (x+y)) \<bullet> sSumLift\<cdot>xs\<cdot>ys "
      by(simp add: sSumLift_def Nat_st_inv_def ssum_unfold Nat_st_def)
      


definition mAdd:: "M \<Rightarrow> M \<Rightarrow> M" where
"mAdd m1 m2 = \<N> (\<inverse>\<N> m1 + \<inverse>\<N> m2)"

definition addStream:: "M stream \<rightarrow> M stream" where
"addStream = sscanl mAdd (\<N> 0)"

lemma madd_range [simp]:"mAdd i1 i2 \<in> range Nat"
by (simp add: mAdd_def)

lemma addstream_sdom [simp]: "sdom\<cdot>(addStream\<cdot>b) \<subseteq> range Nat"
proof
  fix x
  assume "x \<in> sdom\<cdot>(addStream\<cdot>b)"
  obtain n where "Fin n < #(addStream\<cdot>b) \<and> x = snth n (addStream\<cdot>b)" using \<open>x \<in> sdom\<cdot>(addStream\<cdot>b)\<close> sdom_def2 by auto
  thus "x \<in> range M.Nat" sorry
qed

lemma [simp]: assumes "x\<in>range Nat"
  shows "mAdd (\<N> 0) x = x"
by (simp add: assms f_inv_into_f mAdd_def)

lemma [simp]: assumes "x\<in>range Nat"
  shows "mAdd x (\<N> 0) = x"
by (simp add: assms f_inv_into_f mAdd_def)

lemma [simp]: "mAdd (\<N> x) (\<N> y) = \<N> (x+y)"
by (simp add: mAdd_def)

lemma [simp]: "addStream\<cdot>\<epsilon> = \<epsilon>"
by (simp add: addStream_def)

lemma [simp]: assumes "x\<in>range Nat" shows "addStream\<cdot>(\<up>x) = \<up>x"
proof -
  have "x = mAdd \<N> 0 x"
    by (simp add: assms f_inv_into_f)
  then show ?thesis
    by (metis addStream_def lscons_conv sscanl_empty sscanl_scons sup'_def)
qed

lemma rek2addstream [simp]:  assumes "x\<in>range Nat" and "y\<in>range Nat" and "sdom\<cdot>bs \<subseteq> range Nat"
  shows "addStream\<cdot>(\<up>x \<bullet> \<up>y \<bullet> bs) = \<up>x \<bullet> addStream\<cdot>(\<up>(mAdd x y) \<bullet> bs)"
by (simp add: addStream_def assms(1) f_inv_into_f)


lemma ssum2addstream: assumes "sdom\<cdot>b \<subseteq> range Nat" shows "sSumLift\<cdot>(\<up>\<N> 0 \<bullet> addStream\<cdot>b)\<cdot>b = addStream\<cdot>b"
sorry


(* Fingerübung internal channel *)
lift_definition f :: SPF is "\<Lambda> b. ({c1,c2} = sbDom\<cdot>b) \<leadsto> 
    let outSum = sSumLift\<cdot>(b . c1)\<cdot>(b . c2) in
      [c3 \<mapsto> outSum, c2\<mapsto> \<up>\<N> 0 \<bullet> outSum]\<Omega>"
apply(simp add: spf_wellformed_def Let_def)
sorry

definition f_hidden:: "M stream \<Rightarrow> SPF" where 
"f_hidden j \<equiv> Abs_CSPF (\<lambda> b. (sbDom\<cdot>b = {c1}) \<leadsto> 
  let input = b \<uplus> ([c2 \<mapsto> j]\<Omega>) in
    (Rep_CSPF f\<rightharpoonup>input)\<bar> {c3}) "

lift_definition h :: SPS is "{f_hidden j | j. sdom\<cdot>j \<subseteq> ctype c2}"
sorry


















definition internalC:: "M stream \<Rightarrow> StBundle" where 
"internalC inSt = (\<lambda>c. if (c=c1) then Some (\<up>\<N> 0 \<bullet> addStream\<cdot>inSt) else 
                       if (c=c2) then Some inSt else
                       (* c=c3\<or>c=c4*) Some (addStream\<cdot>inSt) )\<Omega>"

lemma internalc_well [simp]: assumes "sdom\<cdot>inSt \<subseteq> range Nat"
  shows "welltyped (\<lambda>c. if (c=c1) then Some (\<up>\<N> 0 \<bullet> addStream\<cdot>inSt) else 
                       if (c=c2) then Some inSt else
                       (* c=c3\<or>c=c4*) Some (addStream\<cdot>inSt) )"
by(simp add: welltyped_def assms)

lemma internalC_rep_eq: assumes "sdom\<cdot>inSt \<subseteq> range Nat"
  shows "Rep_StBundle (internalC inSt) =  (\<lambda>c. if (c=c1) then Some (\<up>\<N> 0 \<bullet> addStream\<cdot>inSt) else 
                       if (c=c2) then Some inSt else
                       (* c=c3\<or>c=c4*) Some (addStream\<cdot>inSt) )"
by (simp add: internalC_def assms)


lemma internalc_sbdom [simp]: assumes "sdom\<cdot>s \<subseteq> range Nat" shows "sbDom\<cdot>(internalC s) = UNIV"
by(simp add: internalC_def sbdom_insert dom_def assms)


  (* example input for the SPF *)
lift_definition in2 :: "StBundle" is "([c2\<mapsto><[\<N> 3, \<N> 1, \<N> 0]>])"
by(simp add: welltyped_def)

  lemma in2_dom [simp]: "sbDom\<cdot>in2 = {c2}"
  by(simp add: in2.rep_eq sbdom_insert)

  lemma in2_c2: "in2 . c2 = <[\<N> 3, \<N> 1, \<N> 0]>"
  by(simp add: sbgetch_insert in2.rep_eq)

  lemma in2_sdom [simp]: "sdom\<cdot>(in2. c2) \<subseteq> range Nat"
  by(simp add: in2_c2)

  (* expected output for input = in1 *)
lift_definition out2 :: "StBundle" is "([c4\<mapsto><[\<N> 3, \<N> 4, \<N> 4]>])"
by(simp add: welltyped_def)

  lemma out2_dom [simp]: "sbDom\<cdot>out2 = {c4}"
  by(simp add: out2.rep_eq sbdom_insert)

  lemma out2_c4: "out2 . c4 = <[\<N> 3, \<N> 4, \<N> 4]>"
  by(simp add: sbgetch_insert out2.rep_eq)

lemma add_in2out: "addStream\<cdot>(in2. c2) = out2. c4"
by(simp add: addStream_def mAdd_def sbgetch_insert in2.rep_eq out2.rep_eq)

lemma sumcomp_cont[simp]: "cont (\<lambda> b . (sbDom\<cdot>b = {c1,c2}) \<leadsto> ((\<lambda> c. (c=c3) \<leadsto> sSumLift\<cdot>(b . c1)\<cdot>(b . c2))\<Omega>))"
sorry

(* define dummy SPF's *)
lift_definition sumComp:: SPF is
"\<Lambda> b . (sbDom\<cdot>b = {c1,c2}) \<leadsto> ((\<lambda> c. (c=c3) \<leadsto> sSumLift\<cdot>(b . c1)\<cdot>(b . c2))\<Omega>)"
sorry

  lemma conc0_well [simp]: "welltyped (\<lambda>c. Some ((\<up>(\<N> 0) \<bullet> (\<up>b . c3))))"
  apply(simp add: sbup_insert sbgetch_insert welltyped_def welltyped1)
  apply(rule )
  using welltyped1 by auto
 
  lemma conc0_cont [simp]: "cont (\<lambda> b. (\<lambda>c. Some ((\<up>(\<N> 0) \<bullet> (\<up>b . c3))))\<Omega>)"
  sorry

  definition conc0 ::"StBundle \<rightarrow> StBundle" where
  "conc0 \<equiv> \<Lambda> b. (\<lambda>c. if c=c3 then Some ((\<up>(\<N> 0) \<bullet> (\<up>b . c3))) else Some (b . c3))\<Omega>"

definition feedComp:: SPF where
"feedComp =  spfSbLift conc0  {c3} {c1,c4}"


(* define behaviour of dummy SPF's *)
lemma sum_comp_dom [simp]: "spfDom\<cdot>sumComp = {c1,c2}"
sorry

lemma sum_comp_ran [simp]: "spfRan\<cdot>sumComp = {c3}"
sorry

lemma sum_comp_fun: "(the ((Rep_CSPF sumComp) b)) . c3 = sSumLift\<cdot>(b . c1)\<cdot>(b. c2)"
sorry


lemma feed_comp_dom [simp]: "spfDom\<cdot>feedComp = {c3}"
by (simp add: feedComp_def)


lemma feed_comp_ran [simp]: "spfRan\<cdot>feedComp = {c1,c4}"
by (simp add: feedComp_def)


lemma feed_comp_fun_c1: assumes "sbDom\<cdot>b = {c3}"
  shows "(the ((Rep_CSPF feedComp) b)) . c1 = (\<up>(\<N> 0) \<bullet> (b . c3))"
apply(simp add: feedComp_def spfSbLift_def assms)
apply(simp add: conc0_def)
apply(simp add: sbgetch_insert sbup_insert)
sorry

lemma feed_comp_fun_c4: "(the ((Rep_CSPF feedComp) b)) . c4 = (b . c3)"
sorry


(*
lemma test1: assumes "\<exists>z. z\<bar>{c4, c3} - {c3, c1} = y \<and>
             z\<bar>{c2} = in2 \<and> z\<bar>{c3} = the (Rep_CSPF sumComp (z\<bar>{c1, c2})) \<and> z\<bar>{c1, c4} = the (Rep_CSPF feedComp (z\<bar>{c3}))"
      shows "y = internalC (in2 . c2)"
sorry  *)

lemma internalC_id: "(internalC (in2 .c2)) \<bar> {c2} = in2"
apply(rule stbundle_eq)
  apply(simp add: sbdom_insert internalC_def sbrestrict_insert welltyped_def)
  using domIff fun_upd_apply in2.rep_eq in2_c2 welltyped_def apply auto[1]
by(simp add: internalC_def sbgetch_insert sbrestrict_insert in2.rep_eq welltyped_def)


lemma internalC2out: " internalC (in2 . c2) \<bar> {c4} = out2" (is "?L = ?R")
proof (rule stbundle_eq)
  show "sbDom\<cdot>?L = sbDom\<cdot>?R" by (simp add: in2_c2)
  fix c
  assume "c\<in>sbDom\<cdot>?L"
  hence "c = c4" by simp
  have "addStream\<cdot>(<[\<N> 3, \<N> 1, \<N> 0]>) = <[\<N> 3, \<N> 4, \<N> 4]>" using add_in2out in2_c2 out2_c4 by auto 
  thus "?L . c = out2 . c"  by(simp add: \<open>c = c4\<close> internalC_def welltyped_def sbgetch_insert sbrestrict_insert in2.rep_eq out2.rep_eq) 
qed


lemma test: assumes "z\<bar>{c2} = in2" and "z\<bar>{c3} = the (Rep_CSPF sumComp (z\<bar>{c1, c2}))" 
    and "z\<bar>{c1, c4} = the (Rep_CSPF feedComp (z\<bar>{c3}))"
      shows "z = internalC (in2 . c2)"
sorry

lemma feedback2internal1: "internalC (in2 . c2)\<bar>{c3} = the (Rep_CSPF sumComp (internalC (in2 . c2)\<bar>{c1, c2}))" (is "?L = ?R")
proof(rule stbundle_eq)
  have "sbDom\<cdot>?R = {c3}" 
    by (smt Abs_cfun_inverse2 Int_insert_right_if1 Rep_CSPF_def UNIV_I ctype.simps(2) dom_fun_upd eq_onp_same_args fun_upd_apply in2.rsp in2_c2 in2_dom insertI1 internalC_id internalc_sbdom option.sel option.simps(3) sbrestrict_sbdom spfran2sbdom sumComp.rep_eq sum_comp_ran sumcomp_cont welltyped_def)
 thus "sbDom\<cdot>?L = sbDom\<cdot>?R" by simp 
 fix c
 assume "c\<in>sbDom\<cdot>?L"
 hence "c = c3" by simp
 have " the ((Rep_StBundle (internalC (in2 . c2))) c3) = addStream\<cdot>(in2 .c2)" by(simp add: internalC_def )
 hence l2add: "?L . c3 = addStream\<cdot>(in2 .c2)" using sbrestrict2sbgetch sbgetch_insert by auto

 have r2add: "?R . c3 = addStream\<cdot>(in2 .c2)"
  by (smt Abs_StBundle_inverse ctype.simps(2) dom_fun_upd eq_onp_same_args in2.rep_eq in2.rsp insertI1 internalC_def internalC_id internalc_well mem_Collect_eq option.sel option.simps(3) sbgetch_insert sbrestrict2sbgetch ssum2addstream subsetCE subset_insertI sum_comp_fun welltyped_def) 
 show "?L .c = ?R. c" by (simp add: \<open>c = c3\<close> l2add r2add)  
qed

lemma internalC_c1: assumes "sdom\<cdot>s \<subseteq> range Nat"
  shows "(internalC s) . c1 =  (\<up>(\<N> 0)) \<bullet> (addStream\<cdot>s)"
by(simp add: sbgetch_insert internalC_def assms)

lemma internalC_c4: assumes "sdom\<cdot>s \<subseteq> range Nat"
  shows "(internalC s) . c4 =  (addStream\<cdot>s)"
by(simp add: sbgetch_insert internalC_def assms)


lemma feedback2internal2: "internalC (in2 . c2)\<bar>{c1, c4} = the (Rep_CSPF feedComp (internalC (in2 . c2)\<bar>{c3}))" (is "?L = ?R")
proof(rule stbundle_eq)
  have "sbDom\<cdot>?R = {c1,c4}" by(simp add: feedComp_def Rep_CSPF_def)
  thus "sbDom\<cdot>?L = sbDom\<cdot>?R" by simp
  fix c
  assume "c\<in>sbDom\<cdot>?L"
  hence "c=c1 \<or> c=c4" by simp 
  have r_c4: "?R . c4 = addStream\<cdot>(in2 . c2)"
    by (smt feed_comp_fun_c4 feedback2internal1 in2_sdom insertI1 internalC_c1 internalC_id sbrestrict2sbgetch ssum2addstream subsetCE subset_insertI sum_comp_fun)
  hence "?R . c1 = \<up>\<N> 0 \<bullet>  addStream\<cdot>(in2. c2)" by (simp add: feed_comp_fun_c1 feed_comp_fun_c4) 
  thus "?L . c = ?R . c"
    using \<open>c \<in> sbDom\<cdot>(internalC (in2 . c2)\<bar>{c1, c4})\<close> internalC_c1 internalC_c4 r_c4 by auto
qed

lemma "the ((spfcompMyHelper sumComp feedComp) in2) = out2"
apply(auto simp add: spfcompMyHelper_def Let_def)
apply(rule the1_equality)
apply(rule +)
proof -
  show "(internalC (in2 .c2)) \<bar> {c2} = in2" by (simp add: internalC_id)
  show "internalC (in2 . c2)\<bar>{c3} = the (Rep_CSPF sumComp (internalC (in2 . c2)\<bar>{c1, c2})) \<and>
    internalC (in2 . c2)\<bar>{c1, c4} = the (Rep_CSPF feedComp (internalC (in2 . c2)\<bar>{c3}))"
      using feedback2internal1 feedback2internal2 by blast
  fix y
  assume "\<exists>z. z\<bar>{c4, c3} - {c3, c1} = y \<and>
             z\<bar>{c2} = in2 \<and> z\<bar>{c3} = the (Rep_CSPF sumComp (z\<bar>{c1, c2})) \<and> z\<bar>{c1, c4} = the (Rep_CSPF feedComp (z\<bar>{c3}))"
  thus "y = internalC (in2 . c2)\<bar>{c4, c3} - {c3, c1}"
    using test by blast
next
  have " internalC (in2 . c2) \<bar> {c4} = out2" by (simp add: internalC2out) 
  thus "\<exists>z. z\<bar>{c4, c3} - {c3, c1} = out2 \<and>
        z\<bar>{c2} = in2 \<and> z\<bar>{c3} = the (Rep_CSPF sumComp (z\<bar>{c1, c2})) \<and> z\<bar>{c1, c4} = the (Rep_CSPF feedComp (z\<bar>{c3}))"
     by (smt Diff_insert2 Diff_insert_absorb channel.distinct(11) channel.distinct(5) feedback2internal1 feedback2internal2 insertI1 insert_Diff_if internalC_id singletonD)
 
qed




end