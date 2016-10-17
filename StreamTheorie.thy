(*  Title:        StreamTheorie.thy
    Author:       Sebastian Stüber
    e-mail:       sebastian.stueber@rwth-aachen.de

    Description:  General Lemmas about Streams. 
                    Especially about: sinftimes, sntimes, siterate
*)

theory StreamTheorie

imports Streams
begin


(* stream is defined on countables, hence the default type is set to countable *)
default_sort countable




(* deletes the Rule "1 = Suc 0" *)
 declare One_nat_def[simp del] 


(* Abbreviation for sntimes *)
abbreviation sntimes_abbr :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a stream" ("_\<star>_" [60,80] 90)
where "(n \<star> s)  == (sntimes n s)"


(* Für Prelude *)
lemma lub_range_shift2: "chain Y \<Longrightarrow> (\<Squnion>i. Y i) = (\<Squnion>i. Y (i+j))"
  apply(simp add: lub_def)
  using is_lub_range_shift lub_def by fastforce


(* the lub of any finite chain is a member of the chain *)
lemma l42: "chain S \<Longrightarrow> finite_chain S \<Longrightarrow> \<exists>t. (\<Squnion> j. S j) = S t"
using lub_eqI lub_finch2 by auto

lemma finite_chain_lub: fixes Y :: "nat \<Rightarrow> 'a ::cpo"
  assumes "finite_chain Y" and "chain Y" and "monofun f"
  shows "f (\<Squnion>i. Y i) = (\<Squnion>i. f (Y i))"
proof -
  obtain nn :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat" where
    f1: "Lub Y = Y (nn Y)"
    by (meson assms(1) assms(2) l42)
  then have "\<forall>n. f (Y n) \<sqsubseteq> f (Y (nn Y))"
    by (metis (no_types) assms(2) assms(3) is_ub_thelub monofun_def)
  then show ?thesis
    using f1 by (simp add: lub_chain_maxelem)
qed 





(* ----------------------------------------------------------------------- *)
section {* Lemmas about Lnat *}
  (* später in Lnat.thy reinkopieren...  *)
(* ----------------------------------------------------------------------- *)


(* instanciate lnat as linorder *)
  (* now min/max can be used with lnat *)
instantiation lnat :: linorder
begin
  instance
  apply(intro_classes)
  using lnat_po_eq_conv lnle_def lnless_def apply blast
  apply simp
  using trans_lnle apply blast
  using lnat_po_eq_conv apply blast
  by (metis inf_ub less2nat linear ninf2Fin)
end

(* any lazy natural number ln is smaller than its successor *)
lemma ln_less[simp]: assumes "ln<\<infinity>"
  shows "ln < lnsuc\<cdot>ln"
proof -
  have "ln \<le> lnsuc\<cdot>ln" by simp
  obtain n where "Fin n = ln" by (metis assms dual_order.strict_implies_not_eq infI)
  have "Fin n < Fin (Suc n)" by force
  thus ?thesis using \<open>Fin n = ln\<close> by auto 
qed

(* a few lemmas simplifying min *)

(* \<infinity> is greater than or equal to any lazy natural number ln *)
lemma [simp]: fixes ln :: lnat
  shows "min \<infinity> ln = ln"
by (simp add: min_def)

lemma [simp]: fixes ln :: lnat
  shows "min ln \<infinity> = ln"
by (simp add: min_def)

(* 0 is less than or equal to any lazy natural number ln *) 
lemma [simp]: fixes ln :: lnat
  shows "min ln 0 = 0"
by (simp add: min_def)

lemma [simp]: fixes ln :: lnat
  shows "min 0 ln = 0"
by (simp add: min_def)





(* ----------------------------------------------------------------------- *)
section {* Lemmas about sinftimes and sntimes *}
  (* und allgemeine Lemmas über conc, shd, sdrop, stake ... *)
(* ----------------------------------------------------------------------- *)



(* prepending an element a to a stream and extracting it with lshd is equivalent to imposing the
   discrete order on a *)
lemma lshd_updis [simp]: "lshd\<cdot>(\<up>a \<bullet> s) = updis a"
by (metis lscons_conv stream.sel_rews(4))

(* converting the element x to a singleton stream, repeating the singleton and re-extracting x with
   lshd is equivalent to imposing the discrete order on x *)
lemma lshd_sinf [simp]: "lshd\<cdot>\<up>x\<infinity> = updis x"
by (metis lshd_updis sinftimes_unfold)

(* the infinite repetition of the stream x has the same head as x *)
lemma shd_sinf[simp]: "shd x\<infinity> = shd x"
by (metis assoc_sconc shd1 sinftimes_unfold strict_icycle surj_scons)

(* srt has no effect on an infinite constant stream of x *)
lemma srt_sinf [simp]: "srt\<cdot>(\<up>x\<infinity>) = \<up>x\<infinity>"
by (metis lscons_conv sinftimes_unfold stream.sel_rews(5) up_defined)

(* dropping k+x elements is equivalent to dropping x elements first and then k elements *) 
lemma sdrop_plus: "sdrop (k+x)\<cdot>xs = sdrop k\<cdot>(sdrop x\<cdot>xs)"
by (simp add: iterate_iterate sdrop_def)

(* if the stream x contains y elements then the first y elements of the infinite repetition of x will
   be x again *)
lemma stake_y [simp]: assumes "#x = Fin y"
    shows "stake y\<cdot>(sinftimes x) = x"
by (metis approxl1 assms minimal monofun_cfun_arg sconc_snd_empty sinftimes_unfold)

(* concatenating streams corresponds to concatenating lists *)
lemma listConcat: "<l1> \<bullet> <l2> = <(l1 @ l2)>"
apply(induction l1)
by auto


(* easy to use rule to show equality on infinite streams *)
(* if two finite streams x, s are identical at every position then x and s are identical *) 
lemma sinf_snt2eq: assumes "#s=\<infinity>" and "#x=\<infinity>" and "\<And>i. (snth i s = snth i x)"
  shows "s=x"
by (simp add: assms snths_eq)

(* the infinite repetitions of the singleton stream \<up>s consists only of the element s *)
lemma snth_sinftimes[simp]: "snth i (\<up>s\<infinity>)  = s"
apply (induction i)
apply (simp) 
by (simp add: snth_rt) 

(* dropping any finite number of elements from an infinite constant stream doesn't affect the stream *)
lemma sdrops_sinf[simp]: "sdrop i\<cdot>\<up>x\<infinity> = \<up>x\<infinity>"
apply (induction i)
apply(simp)
by (simp add: sdrop_forw_rt)


(* after repeating the stream \<up>s n-times the head is s *)
  (* n>0 otherwise \<open>0 \<star> \<up>s = \<epsilon>\<close> *)
lemma shd_sntime [simp]: assumes "n>0" shows "shd (n \<star> \<up>s) = s"
by (metis assms gr0_implies_Suc shd1 sntimes.simps(2))


(* For a finite natural number "i", following relation between sntimes and stake holds:  *)
lemma sntimes_stake: "i \<star> \<up>x = stake i\<cdot>\<up>x\<infinity>"
apply(induction i)
apply simp
by (metis sinftimes_unfold sntimes.simps(2) stake_Suc) 


(* For every finite number "i" is sntimes \<noteq> sinftimes. *)
lemma snNEqSinf [simp]: "i \<star> \<up>x \<noteq> \<up>x\<infinity>"
by (metis lshd_sinf sdropostake sdrops_sinf sntimes_stake stream.sel_rews(3) up_defined)


(* for every natural number i, dropping the first (i*y) elements results in the same infinite stream *)
  (* the first i "blocks" of x are dropped *)
lemma sdrop_sinf[simp]: assumes "Fin y = #x"
  shows "sdrop (i * y)\<cdot>(sinftimes x) = x\<infinity>"
apply(induction i)
apply(simp)
by (metis assms mult_Suc sdrop_plus sdropl6 sinftimes_unfold) 

(* repeating the empty stream again produces the empty stream *)
lemma sinf_notEps[simp]: assumes "xs \<noteq> \<epsilon>" shows "(sinftimes xs) \<noteq> \<epsilon>"
using assms slen_sinftimes by fastforce

(* sinftimes has no effect on streams that are already infinite *)
lemma sinf_inf [simp]: assumes "#s = \<infinity>" 
  shows "s\<infinity> = s"
by (metis assms sconc_fst_inf sinftimes_unfold)

(* sinftimes is idempotent *)
lemma sinf_dupE [simp]: "(sinftimes s) \<infinity> = (s\<infinity>)"
using sinf_inf slen_sinftimes by force

(* alternative unfold rule for sntimes, new element is appended on the end *)
lemma sntimes_Suc2: "(Suc i) \<star> s = (i\<star>s) \<bullet> s"
apply (induction i)
apply simp
by (metis assoc_sconc sntimes.simps(2))


(* 2 very specific lemmas, used in \<open>stake_add\<close> *)
  lemma stake_conc: "stake i\<cdot>s \<bullet> x = stake (Suc i)\<cdot>s \<Longrightarrow> x = stake 1\<cdot>(sdrop i\<cdot>s)"
  apply (induction i arbitrary: s)
  apply (simp add: One_nat_def)
  by (smt assoc_sconc inject_scons sdrop_forw_rt stake_Suc stream.take_strict strict_sdrop surj_scons) 
  
  
  lemma stake_concat:"stake i\<cdot>s \<bullet> stake (Suc j)\<cdot>(sdrop i\<cdot>s) = stake (Suc i)\<cdot>s \<bullet> stake j\<cdot>(sdrop (Suc i)\<cdot>s)"
  proof -
    obtain x where x_def: "stake i\<cdot>s \<bullet> x = stake (Suc i)\<cdot>s" 
      by (metis (no_types, hide_lams) Suc_n_not_le_n linear min_def split_streaml1 stream.take_take)  
    thus ?thesis
      by (smt One_nat_def Rep_cfun_strict1 assoc_sconc sconc_snd_empty sdrop_back_rt stake_Suc stake_conc stream.take_0 stream.take_strict strict_sdrop surj_scons)
  qed


(* for arbitrary natural numbers i, j and any streams s the following lemma holds: *)
lemma stake_add: "stake (i+j)\<cdot>s = (stake i\<cdot>s) \<bullet> (stake j\<cdot>(sdrop i\<cdot>s))"
apply (induction i arbitrary: j)
apply simp
by (metis add_Suc_shift stake_concat)
 

(* Blockwise stake from sinftimes to sntimes. *)
lemma sinf2sntimes: assumes "Fin y = #x"
  shows "stake (i*y)\<cdot>(x\<infinity>) = i\<star>x"
apply(induction i)
apply simp
by (metis assms mult_Suc sdrop_plus sdrop_sinf sntimes.simps(2) stake_add stake_y) 

(* for any natural number i, sntimes is a prefix of sinftimes *)
lemma snT_le_sinfT [simp]: "i\<star>s \<sqsubseteq> s\<infinity>"
by (metis minimal monofun_cfun_arg ninf2Fin sconc_fst_inf sconc_snd_empty sinf2sntimes sinf_inf sntimes.simps(2) sntimes_Suc2 ub_stake)

(* repeating the stream s i times produces a prefix of repeating s i+1 times *)
lemma sntimes_leq: "i\<star>s \<sqsubseteq> (Suc i)\<star>s"
by (metis minimal monofun_cfun_arg sconc_snd_empty sntimes_Suc2)

(* the repetitions of a stream constitute a chain *)
lemma sntimes_chain: "chain (\<lambda>i. i\<star>s)"
by (meson po_class.chainI sntimes_leq)

(* xs is an infinite repetition of the finite stream x. Then dropping any fixed number i of repetitions
   of x leaves xs unchanged. *)
lemma sdrop_sinf2: assumes "xs = x\<bullet>xs" and "#x = Fin y"
  shows "sdrop (y*i)\<cdot>xs = xs"
apply (induction i)
apply simp 
by (metis assms mult_Suc_right sdrop_plus sdropl6) 

(* the recursive definition for a stream (xs = x\<bullet>xs) is identical to the infinite repetition of x at
   every multiple of the length of x *)
lemma stake_eq_sinf: assumes "xs = x\<bullet>xs" and "#x = Fin y" 
  shows "stake (i*y)\<cdot>xs = stake (i*y)\<cdot>(sinftimes x)"
proof (induction i)
  case 0 thus ?case by simp
next
  case (Suc i) 
  have drop_xs:"sdrop (i*y)\<cdot>xs = xs" by (metis assms mult.commute sdrop_sinf2) 

  have "stake (Suc i * y)\<cdot>xs  =  stake (i*y)\<cdot>xs \<bullet> stake y\<cdot>(sdrop (i*y)\<cdot>xs)" by (metis add.commute mult_Suc stake_add) 
  hence eq1:"stake (Suc i * y)\<cdot>xs =  stake (i*y)\<cdot>xs \<bullet> x"  by (metis approxl1 assms drop_xs minimal monofun_cfun_arg sconc_snd_empty)
  
  have "stake (Suc i * y)\<cdot>(sinftimes x) = stake (i*y)\<cdot>(sinftimes x) \<bullet> stake y\<cdot>(sdrop (i*y)\<cdot>(sinftimes x))"  
    by (metis add.commute mult_Suc stake_add)
  hence eq2:"stake (Suc i * y)\<cdot>(sinftimes x) =  stake (i*y)\<cdot>(sinftimes x) \<bullet> x" by (simp add: assms(2)) 

  thus ?case using Suc.IH eq1 by auto 
qed

(* if two streams xs and ys are identical for any prefix that is a multiple of y long, then the two
   streams are identical for any prefix *)
lemma gstake2stake: assumes "\<forall>i. stake (i*y)\<cdot>xs = stake (i*y)\<cdot>ys" and "y\<noteq>0"
  shows "\<forall>i. stake i\<cdot>xs = stake i\<cdot>ys"
proof 
  fix i
  obtain k where "\<exists>l. k = y*l" and "k\<ge>i" by (metis One_nat_def Suc_le_eq assms(2) gr0I mult.commute mult_le_mono2 nat_mult_1_right)
  thus "stake i\<cdot>xs = stake i\<cdot>ys" by (metis assms(1) min_def mult.commute stream.take_take) 
qed

(* when repeating a stream s a different number of times, one of the repetitions will be a prefix of
   the other *)
lemma stake_sntimes2sntimes: assumes "j\<le>k" and "#s = Fin y"
  shows "stake (j*y)\<cdot>(k\<star>s) = j\<star>s"
by (smt assms(1) assms(2) min_def mult_le_mono1 sinf2sntimes stakeostake)

(* For a stream s, a natural y and an arbitrary natural j, apply blockwise stake sntimes. *)
lemma lubStake2sn: assumes "#s = Fin y"
  shows "(\<Squnion> i. stake (y*j)\<cdot>(i\<star>s)) = j\<star>s" (is "(\<Squnion>i. ?c i) = _")
proof -
  have "max_in_chain j (\<lambda>i. ?c i)" by (simp add: assms max_in_chainI mult.commute stake_sntimes2sntimes) 
  thus ?thesis by (simp add: assms maxinch_is_thelub mult.commute sntimes_chain stake_sntimes2sntimes)  
qed

(* building block of the lemma sntimesLub_Fin *)
lemma sntimesChain: assumes "#s = Fin y" and "y \<noteq> 0"
  shows "\<forall>j. stake (y*j)\<cdot>(\<Squnion> i. i\<star>s) = stake (y*j)\<cdot> (s\<infinity>)"
by (metis assms(1) contlub_cfun_arg lubStake2sn mult.commute sinf2sntimes sntimes_chain)

lemma sntimesLub_Fin: assumes "#s = Fin y" and "y \<noteq> 0"
  shows "(\<Squnion> i. i\<star>s) = s\<infinity>"
proof - 
  have  "\<forall>j. stake (j*y)\<cdot>(\<Squnion> i. i\<star>s) = stake (j*y)\<cdot> (s\<infinity>)" by (metis assms(1) assms(2) mult.commute sntimesChain) 
  hence "\<forall>j. stake j\<cdot>(\<Squnion> i. i\<star>s) = stake j\<cdot> (s\<infinity>)" using assms by (metis gstake2stake)
  thus ?thesis by (simp add:  stream.take_lemma)
qed

(* for any stream s the LUB of sntimes is sinftimes *)
lemma sntimesLub[simp]:"(\<Squnion> i. i\<star>s) = s\<infinity>"
apply(cases "#s = \<infinity>")
apply (metis inf2max sconc_fst_inf sinf_inf sntimes.simps(2) sntimes_chain)
by (metis Fin_0 lncases lub_eq_bottom_iff slen_empty_eq sntimesLub_Fin sntimes_chain sntimes_eps strict_icycle)


    (* wichtig *)
(* shows that any recursive definition with the following form is equal to sinftimes *)
lemma rek2sinftimes: assumes "xs = x \<bullet> xs" and "x\<noteq>\<epsilon>"
  shows "xs = sinftimes x"
proof (cases "#x = \<infinity>")
  case True thus ?thesis by (metis assms(1) sconc_fst_inf sinftimes_unfold)
next
  case False 
  obtain y where y_def: "Fin y = #x \<and> y\<noteq>0"  by (metis False Fin_02bot assms(2) infI lnzero_def slen_empty_eq)
  hence "\<forall>i. stake (i*y)\<cdot>xs = stake (i*y)\<cdot>(x\<infinity>)" using assms(1) stake_eq_sinf by fastforce  
  hence "\<forall>i. stake i\<cdot>xs = stake i\<cdot>(x\<infinity>)" using gstake2stake y_def by blast 
  thus ?thesis by (simp add: stream.take_lemma)
qed

(* specializes the result from rek2sinftimes to singleton streams *)
lemma s2sinftimes: assumes "xs = \<up>x \<bullet> xs"
  shows "xs = \<up>x\<infinity>"
using assms rek2sinftimes by fastforce

(* shows that the infinite repetition of a stream x is the least fixed point of iterating (\<Lambda> s. x \<bullet> s),
   which maps streams to streams *)
lemma fix2sinf[simp]: "fix\<cdot>(\<Lambda> s. x \<bullet> s) = x\<infinity>"
by (metis eta_cfun fix_eq fix_strict rek2sinftimes sconc_snd_empty strict_icycle)









(* ----------------------------------------------------------------------- *)
section {* Lemmas about smap *}
(* ----------------------------------------------------------------------- *)


lemma rek2smap: assumes "\<And>a as. f\<cdot>(\<up>a \<bullet> as) = \<up>(g a) \<bullet> f\<cdot>as"
  and "f\<cdot>\<bottom> = \<bottom>"
  shows "f\<cdot>s = smap g\<cdot>s"
apply(rule ind [of _s])
by(simp_all add: assms)

(* smap distributes over infinite repetition *)
lemma smap2sinf[simp]: "smap f\<cdot>(x\<infinity>)= (smap f\<cdot>x)\<infinity>"
by (metis (no_types) rek2sinftimes sinftimes_unfold slen_empty_eq slen_smap smap_split strict_icycle)

(* smap for streams is equivalent to map for lists *)
lemma smap2map: "smap g\<cdot>(<ls>) = <(map g ls)>"
apply(induction ls)
by auto

(* the notion of length is the same for streams as for lists *)
lemma list2streamFin: "#(<ls>) = Fin (length ls)"
apply(induction ls)
by auto









(* ----------------------------------------------------------------------- *)
section {* Lemmas about siterate *}
(* ----------------------------------------------------------------------- *)


(* to define the nth element of siterate we define a helper function \<open>niterate\<close> *)
  (* \<open>iterate\<close> cannot be used, because the function is only about CPO's *)
  
(* Kopieren in Prelude. *)
  primrec niterate :: "nat \<Rightarrow> ('a::type \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" where
      "niterate 0 = (\<lambda> F x. x)"
    | "niterate (Suc n) = (\<lambda> F x. F (niterate n F x))"
 
  (* Kopieren in Prelude. *)
  lemma niterate_Suc2: "niterate (Suc n) F x = niterate n F (F x)"
  apply(induction n)
  by(simp_all)

  (* Kopieren in Prelude. *)
  lemma niter2iter: "iterate g\<cdot>h\<cdot>x = niterate g (Rep_cfun h) x"
  apply (induction g)
  by(simp_all)
  
  (* Prelude *)
  lemma iterate_eps [simp]: assumes "g \<epsilon> = \<epsilon>"
    shows "(iterate i\<cdot>(\<Lambda> h. (\<lambda>s. s \<bullet> h (g s)))\<cdot>\<bottom>) \<epsilon> = \<epsilon>" 
  using assms by (induction i, auto)
  
  (* prelude *)
  lemma fix_eps [simp]: assumes "g \<epsilon> = \<epsilon>"
    shows "(\<mu> h. (\<lambda>s. s \<bullet> h (g s))) \<epsilon> = \<epsilon>"
  proof -
    have aI: "max_in_chain 0 (\<lambda>i. (iterate i\<cdot>(\<Lambda> h. (\<lambda>s. s \<bullet> h (g s)))\<cdot>\<bottom>) \<epsilon> )" by (simp add: max_in_chainI assms)
    hence "(\<Squnion>i. (iterate i\<cdot>(\<Lambda> h. (\<lambda>s. s \<bullet> h (g s)))\<cdot>\<bottom>) \<epsilon>) = \<epsilon>"  using assms by auto 
    hence " (\<Squnion> i. iterate i\<cdot>(\<Lambda> h. (\<lambda>s. s \<bullet> h (g s)))\<cdot>\<bottom>) \<epsilon> = \<epsilon>" by (simp add: lub_fun) 
    thus ?thesis using lub_fun fix_def2 by (metis (no_types, lifting) lub_eq)
  qed
  
(* beginning the iteration of the function h with the element (h x) is equivalent to beginning the
   iteration with x and dropping the head of the iteration *)
lemma siterate_sdrop: "siterate h (h x) = sdrop 1\<cdot>(siterate h x)"
by (metis One_nat_def sdrop_0 sdrop_scons siterate_scons)

(* iterating the function h infinitely often after having already iterated i times is equivalent to
   beginning the iteration with x and then dropping i elements from the resulting stream *)
lemma siterate_drop2iter: "siterate h (niterate i h x) = sdrop i\<cdot>(siterate h x)"
apply (induction i)
apply (simp add: One_nat_def)
by (simp add: sdrop_back_rt siterate_sdrop One_nat_def)  

(* the head of iterating the function g on x doesn't have any applications of g *)
lemma shd_siter[simp]: "shd (siterate g x) = x"
by (simp add: siterate_def)

(* dropping i elements from the infinite iteration of the function g on x and then extracting the head
   is equivalent to computing the i'th iteration via niterate *)
lemma shd_siters: "shd (sdrop i\<cdot>(siterate g x)) = niterate i g x"
by (metis shd_siter siterate_drop2iter)            

(* the i'th element of the infinite stream of iterating the function g on x can alternatively be found
   with (niterate i g x) *)
lemma snth_siter: "snth i (siterate g x) = niterate i g x"
by (simp add: shd_siters snth_def)

(* dropping j elements from the stream x and then extracting the i'th element is equivalent to extracting
   the i+j'th element directly *)
lemma snth_sdrop: "snth i (sdrop j\<cdot>x) = snth (i+j) x"
by (simp add: sdrop_plus snth_def)

(* extracting the i+1'st element from the stream of iterating the function g on x is equivalent to extracting
   the i'th element and then applying g one more time *)
lemma snth_snth_siter: "snth (Suc i) (siterate g x) = g (snth i (siterate g x))"
by (simp add: snth_siter)

(* dropping the first element from the chain of iterates is equivalent to shifting the chain by applying g *)
lemma sdrop_siter:  "sdrop 1\<cdot>(siterate g x) = smap g\<cdot>(siterate g x)"
apply(rule sinf_snt2eq)
apply (simp add: fair_sdrop) 
apply simp
by (simp add: smap_snth_lemma snth_sdrop snth_snth_siter One_nat_def)

(* if the functions g and h commute then g also commutes with any number of iterations of h *)
lemma iterate_insert: assumes "\<forall>z. h (g z) = g (h z)"
  shows "niterate i h (g x) = g (niterate i h x)"
using assms by (induction i, auto)

(* lifts iterate_insert from particular iterations to streams of iterations *)
lemma siterate_smap:  assumes "\<forall>z. g (h z) = h (g z)"
  shows "smap g\<cdot>(siterate h x) = siterate h (g x)"
apply (rule sinf_snt2eq, auto)
by (simp add: assms smap_snth_lemma snth_siter iterate_insert) 

(* shows the equivalence of an alternative recursive definition of iteration *)
lemma rek2niter: assumes "xs = \<up>x \<bullet> (smap g\<cdot>xs)"
  shows "snth i xs = niterate i g x"
proof (induction i)
  case 0 thus ?case by (metis assms niterate.simps(1) shd1 snth_shd)
next
  case (Suc i) 
  have "#xs = \<infinity>" by (metis Inf'_def assms below_refl fix_least_below inf_less_eq lnle_def slen_scons slen_smap)
  thus ?case by (metis Fin_neq_inf Suc assms inf_ub lnle_def lnless_def niterate.simps(2) smap_snth_lemma snth_scons)
qed


(* wichtig *)
(* recursively mapping the function g over the rest of xs is equivalent to the stream of iterations of g on x *)
lemma rek2siter: assumes "xs = \<up>x \<bullet> (smap g\<cdot>xs)"
  shows "xs = siterate g x" 
apply (rule sinf_snt2eq, auto)
apply (metis Inf'_def assms fix_least inf_less_eq lnle_conv slen_scons slen_smap) 
by (metis assms rek2niter snth_siter)

(* shows that siterate produces the least fixed point of the alternative recursive definition *)
lemma fixrek2siter: "fix\<cdot>(\<Lambda> s . (\<up>x \<bullet> smap g\<cdot>s)) =  siterate g x"
by (metis (no_types) cfcomp1 cfcomp2 fix_eq rek2siter)

(* dropping elements from a stream of iterations is equivalent to adding iterations to every element *)
lemma sdrop2smap: "sdrop i\<cdot>(siterate g x) = smap (niterate i g)\<cdot>(siterate g x)"
by (simp add: iterate_insert siterate_drop2iter siterate_smap)

(* doing smap in two passes, applying h in the first pass and g in the second is equivalent to applying
   g \<circ> h in a single pass *)
lemma smaps2smap: "smap g\<cdot>(smap h\<cdot>xs) =  smap (\<lambda> x. g (h x))\<cdot>xs"
by (simp add: smap_snth_lemma snths_eq)

(* iterating the function g on x is equivalent to the stream produced by concatenating \<up>x and the 
   iteration of g on x shifted by another application of g *)
lemma siterate_unfold: "siterate g x = \<up>x \<bullet> smap g\<cdot>(siterate g x)"
by (metis siterate_scons siterate_smap)

(* iterating the identity function produces an infinite constant stream of the element x *)
lemma siter2sinf: "siterate id x = sinftimes (\<up>x)"
by (metis id_apply s2sinftimes siterate_scons)

(* if g acts as the identity for the element x then iterating g on x produces an infinite constant
   stream of x *)
lemma siter2sinf2: assumes "g x = x"
  shows "siterate g x = sinftimes (\<up>x)"
by (smt assms s2sinftimes siterate_scons)









(* ----------------------------------------------------------------------- *)
section {* siterateBlock *}
(* ----------------------------------------------------------------------- *)



(* Alternative definition similar to siterate *)
  (* it is more general than siterate and sinftimes *)
definition siterateBlock:: "('a stream \<Rightarrow> 'a stream) \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
"siterateBlock f \<equiv> fix \<cdot> (\<Lambda> h. (\<lambda>s. s \<bullet> (h (f s))))"

(* block-iterating the function f on the stream x is equivalent to the stream produced by concatenating x
   and the iteration of f on x shifted by another application of f *)
lemma siterateBlock_unfold: "siterateBlock f x = x \<bullet> siterateBlock f (f x)"
by(subst siterateBlock_def [THEN fix_eq2], auto)

(* if g doesn't change the length of the input, then iterating g doesn't either *)
lemma niterate_len[simp]: assumes "\<forall>z. #z = #(g z)" 
  shows "#((niterate i g) x) = #x"
using assms by(induction i, auto)

(* dropping i blocks from siterateBlock g x is equivalent to beginning siterateBlock after i iterations
   of g have already been applied *)
lemma siterateBlock_sdrop2: assumes "#x = Fin y" and "\<forall>z. #z = #(g z)" 
  shows "sdrop (y*i)\<cdot>(siterateBlock g x) = siterateBlock g ((niterate i g) x)"
apply (induction i, auto)
by (metis assms(1) assms(2) niterate_len sdrop_plus sdropl6 siterateBlock_unfold)

(* the y*i'th element of siterateBlock is the same as the head of the i'th iteration *)
lemma siterateBlock_snth: assumes "#x = Fin y" and "\<forall>z. #z = #(g z)" and "#x > Fin 0" 
  shows "snth (y*i) (siterateBlock g x) = shd ((niterate i g) x)"
proof -
  have eq1: "sdrop (y*i)\<cdot>(siterateBlock g x) = siterateBlock g ((niterate i g) x)" using assms(1) assms(2) siterateBlock_sdrop2 by blast 

  have "#((niterate i g) x) > 0" by (metis Fin_02bot assms(2) assms(3) lnzero_def niterate_len)  
  hence "shd (siterateBlock g ((niterate i g) x)) = shd (((niterate i g) x))" by (metis Fin_0 minimal monofun_cfun_arg sconc_snd_empty siterateBlock_unfold snth_less snth_shd)
  thus ?thesis by (simp add: eq1 snth_def) 
qed

(* dropping a single block from siterateBlock is equivalent to beginning the iteration with (g x) *)
lemma siterateBlock_sdrop: assumes "#x = Fin y"
  shows "sdrop y\<cdot>(siterateBlock g x) = siterateBlock g (g x)"
by (metis assms sdropl6 siterateBlock_unfold)

(* block-iterating the function g on the empty stream produces the empty stream again *)
lemma siterateBlock_eps[simp]: assumes "g \<epsilon> = \<epsilon>"
  shows "siterateBlock g \<epsilon> = \<epsilon>" 
by(simp add: siterateBlock_def assms)

(* block-iterating the identity on the element x is equivalent to infinitely repeating x *)
lemma siterateBlock2sinf: "siterateBlock id x = sinftimes x"
by (metis id_apply rek2sinftimes siterateBlock_eps siterateBlock_unfold strict_icycle)

(* siterateBlock doesn't affect infinite streams *)
lemma siterBlock_inf [simp]: assumes "#s = \<infinity>"
  shows "siterateBlock f s = s"
by (metis assms sconc_fst_inf siterateBlock_unfold)

(* the first element of siterateBlock doesn't have any applications of g *)
lemma siterateBlock_shd [simp]: "shd (siterateBlock g (\<up>x)) = x"
by (metis shd1 siterateBlock_unfold)

(* helper lemma for siterateBlock2siter *)
lemma siterateBlock2niter: "snth i (siterateBlock (\<lambda>s. (smap g\<cdot>s)) (\<up>x)) = niterate i g x" (is "snth i (?B) = ?N i")
proof -
  have f1: "#(\<up>x) = Fin 1" by simp
  have "\<forall>z. #z = #((\<lambda>s. (smap g\<cdot>s)) z)" by simp 
  hence f2: " snth (i) (siterateBlock (\<lambda>s. (smap g\<cdot>s)) (\<up>x)) = shd (niterate i (\<lambda>s. (smap g\<cdot>s)) (\<up>x))"
  by (metis Fin_0 Fin_Suc One_nat_def f1 lnat.con_rews lnless_def lnzero_def minimal nat_mult_1 siterateBlock_snth) 
  
  have "shd (niterate i (\<lambda>s. (smap g\<cdot>s)) (\<up>x)) = niterate i g x"
  proof (induction i)
    case 0 thus ?case by simp
  next
    case (Suc i) thus ?case
    by (smt Fin_0 f1 inject_scons neq0_conv niterate.simps(2) niterate_len slen_smap smap_scons strict_slen surj_scons zero_less_one) 
  qed
  thus ?thesis by (simp add: f2) 
qed

(* siterateBlock creates an infinitely long stream *)
lemma siterateBlock_len [simp]: "#(siterateBlock (\<lambda>s. (smap g\<cdot>s)) (\<up>x)) = \<infinity>"
apply (rule infI)
apply (rule allI)
apply (rule_tac x="x" in spec)
apply (induct_tac k, simp+)
apply (metis bot_is_0 lnat.con_rews siterateBlock_unfold slen_scons strict_slen)
by (metis Fin_Suc lnat.sel_rews(2) sconc_snd_empty siterateBlock_unfold slen_scons smap_scons strict_smap)

(* iterating the identity function commutes with any function f *)
lemma siterateBlock_smap: "siterateBlock id (smap f\<cdot>x) =  smap f\<cdot>(siterateBlock id x)"
by (simp add: siterateBlock2sinf smap2sinf)

(* converting x to a singleton stream and applying siterateBlock using smap g is equivalent to
   iterating using g directly on x *)
lemma siterateBlock2siter [simp]: "siterateBlock (\<lambda>s. (smap g\<cdot>s)) (\<up>x) = siterate g x" 
apply (rule sinf_snt2eq, auto)
by (simp add: siterateBlock2niter snth_siter) 







(* szip *)
(* zipping the infinite constant streams \<up>x\<infinity> and \<up>y\<infinity> is equivalent to infinitely repeating the tuple
   \<up>(x, y) *)
lemma szip2sinftimes[simp]: "szip\<cdot>\<up>x\<infinity>\<cdot>\<up>y\<infinity> = \<up>(x, y)\<infinity> "
by (metis s2sinftimes sinftimes_unfold szip_scons)

lemma szip_len [simp]: "#(szip\<cdot>as\<cdot>bs) = min (#as) (#bs)"
apply(induction as arbitrary: bs)
apply(rule admI)
apply auto[1]
apply (metis inf_chainl4 inf_less_eq lub_eqI lub_finch2 min_def slen_sprojsnd sprojsnd_szipl1)
apply simp
apply(case_tac "bs=\<epsilon>")
apply auto[1]
proof -
  fix u :: "'a discr u"
  fix as:: "'a stream"
  fix bs:: "'b stream"
  assume as1: "u \<noteq> \<bottom>" and 
    as2: "(\<And>bs::'b stream. #(szip\<cdot>as\<cdot>bs) = min (#as) (#bs))" and as3: "bs \<noteq> \<epsilon>" 
  obtain a where a_def: "updis a = u" by (metis as1 lshd_updis stream.sel_rews(4) stream.sel_rews(5) surj_scons)
  obtain b bs2 where b_def: "bs = \<up>b \<bullet> bs2" by (metis as3 surj_scons) 
  hence "#(szip\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>b \<bullet> bs2)) = min (#(\<up>a \<bullet> as)) (#(\<up>b \<bullet> bs2))" by (simp add: as2 min_def) 
  thus "#(szip\<cdot>(u && as)\<cdot>bs) = min (#(u && as)) (#bs)" by (metis a_def b_def lscons_conv) 
qed

lemma stake_mono[simp]: assumes "i\<le>j"
  shows "stake i\<cdot>s \<sqsubseteq> stake j\<cdot>s"
by (metis assms min_def stream.take_below stream.take_take)

lemma sconc_sdom: "sdom\<cdot>(s1\<bullet>s2) \<subseteq> sdom\<cdot>s1 \<union> sdom\<cdot>s2"
by (metis SetPcpo.less_set_def below_refl lncases sconc_fst_inf sdom_sconc2un sup.coboundedI1)

lemma sntimes_sdom1[simp]: "sdom\<cdot>(sntimes n s) \<subseteq> sdom\<cdot>s"
proof (induction n)
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case using sconc_sdom sntimes.simps(2) sup.orderE by auto
qed


(* adm Lemmas *)
(* for functions g and h producing sets the following predicate is admissible *)
lemma adm_subsetEq [simp]: "adm (\<lambda>s. g\<cdot>s \<subseteq> h\<cdot>s)"
by (metis (full_types) SetPcpo.less_set_def adm_below cont_Rep_cfun2)

(* for a function g producing sets and a set cs the following predicate is admissible *)
lemma adm_subsetEq_rc [simp]: "adm (\<lambda>s. g\<cdot>s \<subseteq> cs)"
by (metis (no_types, lifting) adm_def chain_monofun contlub_cfun_arg lub_below set_cpo_simps(1))

(* for a function h producing sets and a set cs the following predicate is admissible *)
lemma adm_subsetEq_lc [simp]: "adm (\<lambda>s. cs \<subseteq> h\<cdot>s)"
by (simp add: adm_subst adm_superset)

(* for a set cs and a function g producing sets, the following predicate is admissible *)
lemma adm_subsetNEq_rc [simp]: "adm (\<lambda>s. \<not> g\<cdot>s \<subseteq> cs)"
  apply(rule admI)
  apply(rule+)
  by (metis SetPcpo.less_set_def is_ub_thelub monofun_cfun_arg subset_eq)

(* for a function g over streams, the admissiblity of the following predicate over streams holds *)
lemma sdom_adm2[simp]: "adm (\<lambda>a. sdom\<cdot>(g\<cdot>a) \<subseteq> sdom\<cdot>a)"
apply(rule admI)
by (smt SetPcpo.less_set_def ch2ch_Rep_cfunR contlub_cfun_arg is_ub_thelub lub_below subset_iff)

lemma adm_finstream [simp]: "adm (\<lambda>s. #s<\<infinity> \<longrightarrow> P s)"
apply(rule admI)
apply auto
using inf_chainl4 lub_eqI lub_finch2 by fastforce


lemma adm_fin_below: "adm (\<lambda>x . \<not> Fin n \<sqsubseteq> # x)"
  apply(rule admI)
  apply auto
  using inf_chainl3rf l42 by fastforce

lemma adm_fin_below2: "adm (\<lambda>x . \<not> Fin n \<le> # x)"
by(simp only: lnle_def adm_fin_below)




(* sdom Lemmas *)

(* appending another stream xs can't shrink the domain of a stream x *)
lemma sdom_sconc[simp]: "sdom\<cdot>x \<subseteq> sdom\<cdot>(x \<bullet> xs)"
by (metis minimal monofun_cfun_arg sconc_snd_empty set_cpo_simps(1))

(* repeating a stream doesn't add elements to the domain *)
lemma sinftimes_sdom[simp]: "sdom\<cdot>(sinftimes s) \<subseteq> sdom\<cdot>s"
by (smt chain_monofun contlub_cfun_arg lub_below set_cpo_simps(1) sntimesLub sntimes_chain sntimes_sdom1)

(* repeating a stream doesn't remove elements from the domain either *)
lemma sinf_sdom [simp]: "sdom\<cdot>(s\<infinity>) = sdom\<cdot>s"
by (metis antisym_conv sdom_sconc sinftimes_sdom sinftimes_unfold)

(* sfilter doesn't add elements to the domain *)
lemma sbfilter_sbdom[simp]: "sdom\<cdot>(sfilter A\<cdot>s) \<subseteq> sdom\<cdot>s"
apply(rule ind [of _s], auto)
by (metis (mono_tags, lifting) UnE contra_subsetD sdom2un sfilter_in sfilter_nin singletonD)

(* smap can only produce elements in the range of the mapped function f *)
lemma smap_sdom_range [simp]: "sdom\<cdot>(smap f\<cdot>s) \<subseteq> range f"
by (smt mem_Collect_eq range_eqI sdom_def2 slen_smap smap_snth_lemma subsetI)

(* every element produced by (smap f) is in the image of the function f *)
lemma smap_sdom: "sdom\<cdot>(smap f\<cdot>s) =  f ` sdom\<cdot>s"
apply(rule)
apply (smt image_eqI mem_Collect_eq sdom_def2 slen_smap smap_snth_lemma subsetI)
by (smt image_subset_iff mem_Collect_eq sdom_def2 slen_smap smap_snth_lemma)


(* Lemmas für SB *)
(* if the stream a is a prefix of the stream b then a's domain is a subset of b's *)
lemma f1 [simp]: "a \<sqsubseteq> b \<Longrightarrow> sdom\<cdot>a \<subseteq> sdom\<cdot>b"
by (metis SetPcpo.less_set_def monofun_cfun_arg)

(* the lub of a chain of streams contains any elements contained in any stream in the chain *)
lemma l4: "chain S \<Longrightarrow> sdom\<cdot>(S i) \<subseteq> sdom\<cdot>(\<Squnion> j. S j)"
using f1 is_ub_thelub by auto

lemma l402: "chain S \<Longrightarrow> S i \<noteq> \<up>8 \<Longrightarrow> \<forall>i. S i \<sqsubseteq> s \<Longrightarrow> (\<Squnion> j. S j) \<sqsubseteq> s"
by (simp add: lub_below)

lemma l403: "chain S \<Longrightarrow> \<forall>i. S i \<sqsubseteq> s \<Longrightarrow> \<forall>i. sdom\<cdot>(S i) \<subseteq> sdom\<cdot>s"
by (simp add: f1)

lemma l404: "chain S \<Longrightarrow>  \<forall>i. S i \<sqsubseteq> s \<Longrightarrow> sdom\<cdot>(\<Squnion> j. S j) \<subseteq> sdom\<cdot>s"
using f1 lub_below by blast

(* streams appearing later in the chain S contain the elements of preceding streams *)
lemma l405: "chain S \<Longrightarrow> i \<le> j \<Longrightarrow> sdom\<cdot>(S i) \<subseteq> sdom\<cdot>(S j)"
by (simp add: f1 po_class.chain_mono)

lemma l43: "chain S \<Longrightarrow> finite_chain S \<Longrightarrow> sdom\<cdot>(\<Squnion> j. S j) \<subseteq> (\<Union>i. sdom\<cdot>(S i))"
using l42 by fastforce


(*wichtig*)
(* the lub doesn't have any elements that don't appear somewhere in the chain *)
lemma sdom_lub: "chain S \<Longrightarrow> sdom\<cdot>(\<Squnion> j. S j) = (\<Union>i. sdom\<cdot>(S i))"
apply (simp add: contlub_cfun_arg)
by (simp add: lub_eq_Union)

text {*Sei i in N ein index der Kette S von Strömen und B eine Menge von Nachrichten. *}
lemma l44: assumes "chain S" and "\<forall>i. sdom\<cdot>(S i) \<subseteq> B"
  shows "sdom\<cdot>(\<Squnion> j. S j) \<subseteq> B"
by (metis (mono_tags, lifting) UN_E assms sdom_lub subsetCE subsetI)


lemma l6: "chain S \<Longrightarrow> \<forall>i. sdom\<cdot>(S i) \<subseteq> B \<Longrightarrow> sdom\<cdot>(\<Squnion> j. S (j + (SOME k. A))) \<subseteq> B"
by (simp add: l44 lub_range_shift)

(* dropping elements can't increase the domain *)
lemma sdrop_sdom[simp]: "sdom\<cdot>(sdrop n\<cdot>s)\<subseteq>sdom\<cdot>s"
by (metis Un_upper2 approxl2 f1 sdom_sconc2un sdrop_0 sdropostake split_streaml1 stream.take_below)














(* Lemmas für TStream *)

(* appending the singleton stream \<up>a increases the length of the stream y by one *)
lemma slen_lnsuc: 
  shows "#(y \<bullet> \<up>a) = lnsuc\<cdot>(#y)"
  apply(induction y)
    apply (smt admI fold_inf inf_chainl4 lub_eqI lub_finch2 sconc_fst_inf)
   apply (metis sconc_fst_empty sconc_snd_empty slen_scons)
  by (metis (no_types, lifting) assoc_sconc slen_scons stream.con_rews(2) stream.sel_rews(5) surj_scons)



(* returns the last element of a stream *)
(* the stream must not be empty or infinitely long *)
definition sfoot :: "'a stream \<Rightarrow> 'a" where
"sfoot s = snth (THE a. lnsuc\<cdot>(Fin a) = #s) s"


(* appending the singleton stream \<up>a to a finite stream s causes sfoot to extract a again *)
lemma sfoot1[simp]: assumes "xs = s\<bullet>(\<up>a)" and "#xs < \<infinity>"
   shows "sfoot xs = a"
proof -
  have "xs \<noteq> \<epsilon>" using assms(1) strictI by force
  obtain n where n_def: "Fin n = #xs" by (metis assms(2) lncases lnless_def) 
  hence "n>0" using assms(2) gr0I using Fin_02bot \<open>xs \<noteq> \<epsilon>\<close> lnzero_def slen_empty_eq by fastforce 
  hence "(THE n'. lnsuc\<cdot>(Fin n') = #xs) = n-1" by (metis (mono_tags, lifting) Fin_Suc Suc_diff_1 n_def inject_Fin inject_lnsuc the_equality)
  have "snth (n-1) xs = a" by (metis Fin_0 Fin_Suc Fin_neq_inf Suc_diff_1 assms(1) n_def bot_is_0 inf_ub inject_lnsuc lnat.con_rews lnle_conv lnless_def lscons_conv neq0_conv sconc_fst_inf sdropl6 shd1 slen_lnsuc snth_def sup'_def)
  thus ?thesis by (metis \<open>(THE n'. lnsuc\<cdot>(Fin n') = #xs) = n - 1\<close> sfoot_def)
qed

(* sfoot extracts the element a from any finite stream ending with \<up>a *)
lemma sfoot12 [simp]: assumes "#s<\<infinity>"
  shows "sfoot (s\<bullet>\<up>a) = a"
by (metis assms fold_inf inject_lnsuc lnless_def monofun_cfun_arg sfoot1 slen_lnsuc)

(* sfoot extracts a from the singleton stream \<up>a *)
lemma sfoot_one [simp]: "sfoot (\<up>a) = a"
by (metis Inf'_neq_0 inf_ub lnle_def lnless_def sconc_fst_empty sfoot12 strict_slen)

(* concatenating finite streams produces another finite stream *)
lemma sconc_slen [simp]: assumes "#s<\<infinity>" and "#xs<\<infinity>"
  shows "#(s\<bullet>xs) < \<infinity>"
by (metis Fin_neq_inf assms(1) assms(2) infI inf_ub lnle_def lnless_def slen_sconc_all_finite)

(* if the foot of a non-empty stream xs is a, then xs consists of another stream s (possibly empty)
   concatenated with \<up>a *)
lemma sfoot2 [simp]: assumes "sfoot xs = a" and "xs\<noteq>\<epsilon>"
  shows "\<exists>s. xs = s \<bullet> \<up>a"
proof (cases "#xs = \<infinity>")
  case True thus ?thesis by (metis sconc_fst_inf) 
next
  case False 
  obtain n where "#xs = Fin n" using False lncases by auto
  hence "(THE n'. lnsuc\<cdot>(Fin n') = #xs) = n-1"
    by (smt Fin_02bot Fin_Suc Suc_diff_1 assms(2) bot_is_0 inject_Fin inject_lnsuc neq0_conv slen_empty_eq the_equality)
  have "stake (n-1)\<cdot>xs \<bullet> \<up>(snth (n-1) xs) = xs"
    by (smt Fin_0 Fin_Suc Inf'_def Suc_diff_1 \<open>#xs = Fin n\<close> assms(2) fin2stake fix_least_below lnle_def neq0_conv notinfI3 sconc_snd_empty sdrop_back_rt sdropostake slen_empty_eq snth_def split_streaml1 surj_scons ub_slen_stake)
  thus ?thesis by (metis \<open>(THE n'. lnsuc\<cdot>(Fin n') = #xs) = n - 1\<close> assms(1) sfoot_def) 
qed

(* when sfoot is applied to the concatenation of two finite streams s and xs, and xs is not empty,
   then sfoot will produce the foot of xs *)
lemma sfoot_conc [simp]: assumes "#s<\<infinity>" and "#xs<\<infinity>" and "xs\<noteq>\<epsilon>"
  shows "sfoot (s\<bullet>xs) = sfoot xs"
by (metis (no_types, hide_lams) assms(1) assms(2) assms(3) assoc_sconc sconc_slen sfoot1 sfoot2)

(* if the finite stream s contains more than one element then the foot of s will be the foot of the
   rest of s *)
lemma sfoot_sdrop: assumes "Fin 1<#s" and "#s<\<infinity>"
  shows "sfoot (srt\<cdot>s) = sfoot s"
proof -
  obtain s' where "s = s' \<bullet> \<up>(sfoot s)" by (metis assms below_antisym bot_is_0 lnless_def minimal sfoot2 strict_slen)
  hence "s' \<noteq> \<epsilon>"
    by (metis Fin_02bot Fin_Suc Inf'_neq_0 One_nat_def assms lnless_def lnzero_def minimal slen_lnsuc strict_slen)
  hence "srt\<cdot>s = srt\<cdot>s' \<bullet> \<up>(sfoot s)"
    by (smt \<open>s = s' \<bullet> \<up>(sfoot s)\<close> assoc_sconc inject_scons sconc_snd_empty strictI surj_scons)
  thus ?thesis
    by (metis \<open>s = s' \<bullet> \<up>(sfoot s)\<close> \<open>s' \<noteq> \<epsilon>\<close> assms(2) inf_ub lnle_conv lnless_def sconc_snd_empty sfoot1 slen_sconc_snd_inf strictI surj_scons) 
qed

lemma [simp]: assumes "#xs < \<infinity>"
  shows "sfoot (\<up>a \<bullet> \<up>b \<bullet> xs) = sfoot (\<up>b \<bullet> xs)"
using assms lnless_def by auto 

(* the foot of any stream s is the nth element of s for some natural number n *)
lemma sfoot_exists [simp]:"\<exists>n. snth n s = sfoot s"
by (metis sfoot_def)

(* if the stream s contains n+1 elements then the foot of s will be found at index n *)
lemma  sfoot_exists2: 
  shows "Fin (Suc n) = #s \<Longrightarrow> snth n s = sfoot s"
  apply(induction n arbitrary: s)
   apply (metis (mono_tags, lifting) Fin_02bot Fin_Suc Zero_lnless_infty inject_lnsuc lnzero_def sconc_fst_empty sconc_snd_empty sfoot12 slen_empty_eq slen_scons snth_shd surj_scons)
  by (smt Fin_Suc Fin_neq_inf fold_inf inf_ub inject_lnsuc lnat.con_rews lnle_conv lnless_def lnzero_def sconc_snd_empty sfoot_conc slen_scons snth_rt strict_slen surj_scons)




(* sfilter *)
(* if filtering the stream s2 with the set A produces infinitely many elements then prepending any
   finite stream s1 to s2 will still produce infinitely many elements *)
lemma sfilter_conc2[simp]: assumes "#(sfilter A\<cdot>s2) = \<infinity>" and "#s1 < \<infinity>"
  shows "#(sfilter A\<cdot>(s1\<bullet>s2)) = \<infinity>"
proof -
  have "(sfilter A\<cdot>(s1\<bullet>s2)) = ((sfilter A\<cdot>s1) \<bullet> (sfilter A\<cdot>s2))"
    using add_sfilter assms(2) lnless_def ninf2Fin by fastforce 
  thus ?thesis by (simp add: assms(1) slen_sconc_snd_inf) 
qed

(* if the stream z is a prefix of another non-empty stream (y\<bullet>\<up>a) but isn't equal to it, then z is
   also a prefix of y *)
lemma below_conc: assumes "z \<sqsubseteq> (y\<bullet>\<up>a)" and "z\<noteq>(y\<bullet>\<up>a)"
  shows "z\<sqsubseteq>y"
proof(cases "#y = \<infinity>")
  case True thus ?thesis using assms(1) sconc_fst_inf by auto  
next
  case False 
  obtain n_y where "Fin n_y= #y" using False ninf2Fin by fastforce
  have "#z \<le> #(y\<bullet>\<up>a)" using assms(1) mono_slen by blast
  have "#z \<noteq> #(y\<bullet>\<up>a)" using assms(1) assms(2) eq_slen_eq_and_less by blast
  hence "#z < #(y\<bullet>\<up>a)" using \<open>#z \<le> #(y \<bullet> \<up>a)\<close> lnle_def lnless_def by blast 
  obtain n_z where nz_def: "Fin n_z = #z" using approxl2 assms(1) assms(2) by blast 
  have "#y < #(y \<bullet> \<up>a)"
    by (metis \<open>Fin n_y = #y\<close> eq_slen_eq_and_less inject_sconc lnless_def minimal monofun_cfun_arg sconc_snd_empty stream.con_rews(2) sup'_def up_defined)
  have "#y < \<infinity>" by (simp add: False lnless_def) 
  hence "Fin n_z \<le> #y" by (metis Fin_Suc \<open>#z < #(y \<bullet> \<up>a)\<close> less2lnleD lnsuc_lnle_emb nz_def slen_lnsuc) 
  have "\<And>s. stake n_y\<cdot>(y \<bullet> s) = y" by (simp add: \<open>Fin n_y = #y\<close> approxl1)
  hence "stake n_z\<cdot>y = stake n_z\<cdot>(y\<bullet>\<up>a)" by (metis \<open>Fin n_y = #y\<close> \<open>Fin n_z \<le> #y\<close> less2nat min_def stakeostake)
  thus ?thesis by (metis \<open>Fin n_z = #z\<close> approxl1 assms(1) stream.take_below) 
qed

(* for any set A and singleton stream \<up>a the following predicate over streams is admissible *)
lemma sfilter_conc_adm: "adm (\<lambda>b. #b<\<infinity> \<longrightarrow> #(A \<ominus> b) < #(A \<ominus> b \<bullet> \<up>a))" (is "adm ?F")
by (metis (mono_tags, lifting) admI inf_chainl4 lnless_def lub_eqI lub_finch2)

(* the element a is kept when filtering with A, so (x \<bullet> \<up>a) produces a larger result than just x,
   provided that x is finite *)
lemma sfilter_conc: assumes "a\<in>A" 
  shows "#x<\<infinity> \<Longrightarrow> #(A \<ominus> x) < #(A \<ominus> (x \<bullet> \<up>a))" (is "_ \<Longrightarrow> ?F x")
  proof(induction x)
    show "adm (\<lambda>b. #b < \<infinity> \<longrightarrow> #(A \<ominus> b) < #(A \<ominus> b \<bullet> \<up>a))" using sfilter_conc_adm by blast
   show "?F \<epsilon>" using assms(1) lnless_def by auto
  next
  fix u :: "'a discr u"
  fix s :: "'a stream"
  assume "u\<noteq>\<bottom>" and "#s<\<infinity> \<Longrightarrow> ?F s" and "#(u && s) < \<infinity>"
  obtain ua where "(updis ua) = u" by (metis \<open>u \<noteq> \<bottom>\<close> discr.exhaust upE)
  hence "u && s = \<up>ua \<bullet>s" using lscons_conv by blast
  thus "?F (u&&s)"
  by (smt \<open>#(u && s) < \<infinity>\<close> \<open>#s < \<infinity> \<Longrightarrow> #(A \<ominus> s) < #(A \<ominus> s \<bullet> \<up>a)\<close> assoc_sconc fold_inf lnat.sel_rews(2) lnless_def monofun_cfun_arg sfilter_in sfilter_nin slen_scons)
qed

(* for any finite stream s and set A, if filtering s with A doesn't produce the empty stream, then
   filtering and infinite repetition are associative *)
lemma sfilter_sinf [simp]: assumes "#s<\<infinity>" and "(A \<ominus> s) \<noteq> \<epsilon>"
  shows "A \<ominus> (s\<infinity>) = (A \<ominus> s)\<infinity>"
by (metis add_sfilter assms(1) assms(2) infI lnless_def rek2sinftimes sinftimes_unfold)

(* if filtering the stream s with the set A produces infinitely many elements, then filtering the 
   rest of s with A also produces infinitely many elements *)
lemma sfilter_srt_sinf [simp]: assumes "#(A \<ominus> s) = \<infinity>" 
  shows  "#(A \<ominus> (srt\<cdot>s)) = \<infinity>"
by (smt assms inf_scase inject_scons sfilter_in sfilter_nin stream.sel_rews(2) surj_scons) 








text {* Streams can be split for filtering *}
lemma add_sfilter2: assumes "#x < \<infinity>" 
  shows "sfilter A\<cdot>(x \<bullet> y) = sfilter A\<cdot>x \<bullet> sfilter A\<cdot>y"
by (metis (no_types) add_sfilter assms lncases lnless_def)

(* if none of the elements in the domain of the stream s are in the set A, then filtering s with A
   produces the empty stream *)
lemma sfilter_sdom_eps: "sdom\<cdot>s \<inter> A = {} \<Longrightarrow> (A \<ominus> s) = \<epsilon>"
by (meson disjoint_iff_not_equal ex_snth_in_sfilter_nempty snth2sdom)



(* stakewhile *)
(* stakewhile can't increase the length of a stream *)
lemma stakewhile_less [simp]: "#(stakewhile f\<cdot>s)\<le>#s"
  apply(rule ind [of _ s], auto)
   apply (metis (mono_tags, lifting) admI inf_chainl4 inf_ub l42)
  by (metis bot_is_0 lnle_def lnsuc_lnle_emb minimal slen_empty_eq slen_scons stakewhile_f stakewhile_t)

(* stakewhile doesn't take elements past an element that fails the predicate f *)
lemma stakewhile_slen[simp]: "\<not>f (snth n s) \<Longrightarrow> #(stakewhile f\<cdot>s)\<le>Fin n"
  apply(induction n arbitrary: s)
   apply (metis Fin_02bot lnat_po_eq_conv lnzero_def sdrop_0 slen_empty_eq snth_def stakewhile_f strict_stakewhile surj_scons)
  by (smt inject_scons slen_rt_ile_eq snth_rt stakewhile_f stakewhile_t stream.take_strict strict_stakewhile surj_scons ub_slen_stake)

(* the prefix of the constant stream of x's whose elements aren't equal to x is empty *)
lemma [simp]: "stakewhile (\<lambda>a. a \<noteq> x)\<cdot>\<up>x\<infinity> = \<epsilon>"
by (metis sinftimes_unfold stakewhile_f)

(* stakewhile produces a prefix of the input *)
lemma stakewhile_below[simp]: "stakewhile f\<cdot>s \<sqsubseteq> s"
  apply(induction s)
    apply(simp+)
  by (smt minimal monofun_cfun_arg stakewhile_f stakewhile_t stream.con_rews(2) stream.sel_rews(5) surj_scons)

(* stwbl produces a prefix of the input *)
lemma stwbl_below [simp]: "stwbl f\<cdot>s \<sqsubseteq> s"
by (metis (no_types) minimal monofun_cfun_arg sconc_snd_empty stwbl_srtdw)

(* stakewhile doesn't include the element a that failed the predicate f in the result *)
lemma stakewhile_dom[simp]:assumes "\<not>f a"
  shows "a\<notin>sdom\<cdot>(stakewhile f\<cdot>s)"
by (smt assms below_antisym lnle_conv lnless_def mem_Collect_eq sdom_def2 snth_less stakewhile_below stakewhile_slen)

(* if stakewhile leaves a stream s unchanged, then every element must pass the predicate f *) 
lemma stakewhile_id_snth: assumes "stakewhile f\<cdot>s = s" and "Fin n < #s"
  shows "f (snth n s)"
by (metis assms snth2sdom stakewhile_dom)

(* if stakewhile produces a result of length n or greater, then the nth element in s must pass f *)
lemma stakewhile_snth[simp]: assumes  "Fin n < #(stakewhile f\<cdot>s)"
  shows "f (snth n s)"
by (metis assms snth2sdom snth_less stakewhile_below stakewhile_dom)

(* if stakewhile changes the stream s, then there must be an element in s that fails the predicate f *)
lemma stakewhile_notin [simp]: 
  shows "stakewhile f\<cdot>s \<noteq> s \<Longrightarrow> #(stakewhile f\<cdot>s) = Fin n \<Longrightarrow> \<not> f (snth n s)"
  apply(induction n arbitrary:s)
   apply (metis Fin_02bot lnat.con_rews slen_scons snth_shd stakewhile_t surj_scons)
  by (smt Fin_02bot Fin_Suc approxl2 inject_scons lnat.con_rews lnat_po_eq_conv lnsuc_lnle_emb lnzero_def slen_empty_eq slen_rt_ile_eq snth_rt snth_shd stakewhile_below stakewhile_slen stakewhile_t stream.take_strict surj_scons ub_slen_stake)

(* if stakewhile changes the stream s, which is a prefix of the stream s', then stakewhile of s and s'
   produce the same result *)
lemma stakewhile_finite_below: 
  shows "stakewhile f\<cdot>s \<noteq> s \<Longrightarrow> s\<sqsubseteq>s' \<Longrightarrow> stakewhile f\<cdot>s = stakewhile f\<cdot>s'"
  apply(induction s)
    apply simp+
  by (smt approxl1 approxl2 lnless_def monofun_cfun_arg rev_below_trans snth_less stakewhile_below stakewhile_notin stakewhile_snth)

(* if there is an element in the stream s that fails the predicate f, then stakewhile will change s *)
lemma stakewhile_noteq[simp]: assumes "\<not>f (snth n s)" and "Fin n < #s"
  shows "stakewhile f\<cdot>s \<noteq> s"
proof (rule ccontr)
  assume "\<not> stakewhile f\<cdot>s \<noteq> s"
  hence "sdom\<cdot>(stakewhile f\<cdot>s) = sdom\<cdot>s" by simp
  hence "(snth n s)\<in>sdom\<cdot>(stakewhile f\<cdot>s)" by (simp add: assms(2) snth2sdom)
  thus False by (simp add: assms(1)) 
qed

(* if there's an element a in the domain of s which fails the predicate f, then stwbl will produce a
   finite result *)
lemma stwbl_fin [simp]: assumes "a\<in>sdom\<cdot>s" and "\<not> f a"
  shows "#(stwbl f\<cdot>s) < \<infinity>"
by (metis assms(1) assms(2) inf_ub lnle_conv lnless_def notinfI3 sconc_slen sdom2snth stakewhile_slen stwbl_stakewhile ub_slen_stake)

(* stwbl keeps at least all the elements that stakewhile keeps *)
lemma stakewhile_stwbl [simp]: "stakewhile f\<cdot>(stwbl f\<cdot>s) = stakewhile f\<cdot>s"
proof -
  have "\<And>s sa. (s::'a stream) \<sqsubseteq> s \<bullet> sa"
    by simp
  then have "stakewhile f\<cdot>(stwbl f\<cdot>s) = stwbl f\<cdot>s \<longrightarrow> stakewhile f\<cdot>(stwbl f\<cdot>s) = stakewhile f\<cdot>s"
    by (metis (no_types) below_antisym monofun_cfun_arg stwbl_below stwbl_stakewhile)
  then show ?thesis
    using stakewhile_finite_below stwbl_below by blast
qed





(* sscanl - lemmas *)


(* dropping the first element of the result of sscanl is equivalent to beginning the scan with 
   (f a (shd s)) as the initial element and proceeding with the rest of the input *)
lemma sscanl_srt: "srt\<cdot>(sscanl f a\<cdot>s) = sscanl f (f a (shd s)) \<cdot>(srt\<cdot>s) "
by (metis (no_types, lifting) sconc_fst_empty sconc_scons' sscanl_empty sscanl_scons stream.sel_rews(2) stream.sel_rews(5) sup'_def surj_scons up_defined)

(* the n + 1'st element produced by sscanl is the result of mering the n + 1'st item of s with the n'th
   element produced by sscanl *)
lemma sscanl_snth:  "Fin (Suc n) < #s \<Longrightarrow> snth (Suc n) (sscanl f a\<cdot>s) = f (snth n (sscanl f a\<cdot>s)) (snth (Suc n) s)"
apply(induction n arbitrary:  a s)
apply (smt Fin_02bot Fin_leq_Suc_leq less2lnleD less_lnsuc lnat_po_eq_conv lnless_def lnzero_def shd1 slen_empty_eq slen_rt_ile_eq snth_scons snth_shd sscanl_scons surj_scons)
by (smt Fin_Suc lnat_po_eq_conv lnle_def lnless_def lnsuc_lnle_emb lnzero_def minimal slen_scons snth_scons sscanl_scons strict_slen surj_scons)

(* the result of sscanl has the same length as the input stream x *)
lemma fair_sscanl[simp]: "#(sscanl f a\<cdot>x) = #x"
apply (rule spec [where x = a])
by (rule ind [of _ x], auto)




lemma sdom_sfilter1: assumes "x\<in>sdom\<cdot>(A\<ominus>s)" 
  shows "x\<in>A"
by (smt assms mem_Collect_eq sdom_def2 sfilterl7)

lemma sdom_subset: assumes "u\<noteq>\<bottom>"
  shows "sdom\<cdot>s\<subseteq>sdom\<cdot>(u && s)"
by (metis Un_upper2 assms sdom2un stream.con_rews(2) stream.sel_rews(5) surj_scons)

lemma sdom_sfilter_subset: assumes "u\<noteq>\<bottom>"
  shows "sdom\<cdot>(A\<ominus>s)\<subseteq>sdom\<cdot>(A \<ominus> (u && s))"
by (smt Un_upper2 assms eq_iff sdom2un sfilter_in sfilter_nin stream.con_rews(2) stream.sel_rews(5) surj_scons)

lemma sdom_sfilter2: assumes  "x\<in>A"
  shows "x\<in>sdom\<cdot>s \<Longrightarrow> x\<in>(sdom\<cdot>(A \<ominus> s))"
  apply(induction s)
    apply(rule admI)
    apply rule
    apply (smt SUP_def UN_E ch2ch_Rep_cfunR contlub_cfun_arg contra_subsetD l4 set_cpo_simps(2))
   apply simp
  by (smt UnE assms empty_iff insert_iff sconc_sdom sdom2un sdom_sconc sdom_sfilter_subset sfilter_in stream.con_rews(2) stream.sel_rews(5) subsetCE surj_scons)



lemma sdom_sfilter[simp]: "sdom\<cdot>(A\<ominus>s) = sdom\<cdot>s \<inter> A"
  apply rule
   apply (meson IntI sbfilter_sbdom sdom_sfilter1 subset_iff)
  apply rule
  by (meson IntD1 IntD2 sdom_sfilter2)


lemma stwbl_id_help:
  shows "(\<forall>a\<in>sdom\<cdot>s. f a) \<longrightarrow> stwbl f\<cdot>s = s"
  apply (rule ind [of _s])
    apply(rule adm_imp)
     apply(rule admI, rule+)
     using l4 apply blast
    apply(rule admI)
    apply (metis cont2contlubE cont_Rep_cfun2 lub_eq)
   using strict_stwbl apply blast
  apply rule+
  by simp

lemma stwbl_id [simp]: "(\<And> a. a\<in>sdom\<cdot>s \<Longrightarrow> f a) \<Longrightarrow> stwbl f\<cdot>s = s"
by (simp add: stwbl_id_help)

lemma stwbl_notEps: "s\<noteq>\<epsilon> \<Longrightarrow> (stwbl f\<cdot>s)\<noteq>\<epsilon>"
by (smt lnat.con_rews lnzero_def sconc_snd_empty slen_scons strict_slen stwbl_f stwbl_t surj_scons)


lemma stwbl2stakewhile: assumes "a\<in>sdom\<cdot>s" and "\<not>f a"
  shows "\<exists>x. (stwbl f\<cdot>s) = stakewhile f\<cdot>s \<bullet> \<up>x" 
proof -
  have "#(stwbl f\<cdot>s) < \<infinity>" using assms(1) assms(2) snth2sdom stwbl_fin by blast
  hence "stwbl f\<cdot>s \<noteq> \<epsilon>" by (metis assms(1) assms(2) stakewhile_dom strict_stakewhile stwbl_notEps) 
  thus ?thesis
    by (smt Fin_02bot approxl2 assms(1) assms(2) bottomI lnle_def lnzero_def mem_Collect_eq sconc_snd_empty sdom_def2 sdrop_0 slen_empty_eq slen_rt_ile_eq split_streaml1 stakewhile_below stakewhile_noteq stakewhile_sdropwhilel1 stwbl_notEps stwbl_stakewhile surj_scons tdw ub_slen_stake) 
qed

lemma stwbl_sfoot: assumes "a\<in>sdom\<cdot>s" and "\<not>f a"
  shows "\<not> f (sfoot (stwbl f\<cdot>s))" 
proof(rule ccontr)
  assume "\<not> \<not> f (sfoot (stwbl f\<cdot>s))"
  hence "f (sfoot (stwbl f\<cdot>s))" by blast
  obtain x where x_def:"(stwbl f\<cdot>s) = stakewhile f\<cdot>s \<bullet> \<up>x"
    using assms(1) assms(2) stwbl2stakewhile by blast
  hence "sfoot (stwbl f\<cdot>s) = x"
    using assms(1) assms(2) sfoot1 stwbl_fin by blast
  have "stakewhile f\<cdot>s \<bullet> \<up>x \<sqsubseteq> s" by (metis stwbl_below x_def)
  have "f x"
    using \<open>f (sfoot (stwbl f\<cdot>s))\<close> \<open>sfoot (stwbl f\<cdot>s) = x\<close> by blast
  thus False
    by (smt Fin_02bot \<open>sfoot (stwbl f\<cdot>s) = x\<close> approxl2 assms(1) assms(2) assoc_sconc bottomI lnle_def lnzero_def sconc_fst_empty sconc_snd_empty sdrop_0 sdropwhile_t sfoot1 slen_empty_eq slen_rt_ile_eq split_streaml1 stakewhile_below stakewhile_dom stakewhile_sdropwhilel1 stakewhile_stwbl stream.take_strict strict_stakewhile stwbl_fin stwbl_notEps stwbl_stakewhile surj_scons tdw ub_slen_stake)
qed

lemma stwbl2stbl[simp]: "stwbl f\<cdot>(stwbl f\<cdot>s) = stwbl f\<cdot>s"
  apply(rule ind [of _s])
    apply simp_all
  by (metis sconc_snd_empty stwbl_f stwbl_t)


lemma stakewhileDropwhile[simp]: "stakewhile f\<cdot>s \<bullet> (sdropwhile f\<cdot>s) = s "
  apply(rule ind [of _s])
    apply (rule admI)
    apply (metis (no_types, lifting) approxl2 inf_chainl4 lub_eqI lub_finch2 sconc_fst_inf split_streaml1 stakewhile_below stakewhile_sdropwhilel1)
   apply simp
  by (metis assoc_sconc sconc_fst_empty sdropwhile_f sdropwhile_t stakewhile_t tdw)

lemma stwbl_eps: "stwbl f\<cdot>s = \<epsilon> \<longleftrightarrow> s=\<epsilon>"
using strict_stwbl stwbl_notEps by blast


lemma srtdw_stwbl [simp]: "srtdw f\<cdot> (stwbl f\<cdot>s) = \<epsilon>" (is "?F s")
proof(rule ind [of _s ])
  show "adm ?F" by simp
  show "?F \<epsilon>" by simp

  fix a
  fix s
  assume IH: "?F s"
  thus "?F (\<up>a \<bullet> s)" 
  proof (cases "f a")
    case True thus ?thesis by (simp add: IH)
  next
    case False thus ?thesis by simp
  qed
qed


lemma sconc_neq_h: assumes "s1 \<noteq> s2"
  shows "#a < \<infinity> \<longrightarrow> a \<bullet> s1 \<noteq> a \<bullet> s2"
  apply(rule ind [of _a ])
    apply(rule admI)
    apply (rule impI)
    apply (metis inf_chainl4 l42 neq_iff)
   apply (simp add: assms)
  by (metis inf_ub inject_scons less_le sconc_scons slen_sconc_snd_inf)
 
lemma sconc_neq: assumes "s1 \<noteq> s2" and "#a < \<infinity>"
  shows "a \<bullet> s1 \<noteq> a \<bullet> s2"
using assms(1) assms(2) sconc_neq_h by blast


lemma adm_nsdom [simp]:  "adm (\<lambda>x. b \<notin> sdom\<cdot>x)"
proof (rule admI)
  fix Y
  assume as1: "chain Y" and as2: "\<forall>i. b\<notin>sdom\<cdot>(Y i)"
  thus "b\<notin>sdom\<cdot>(\<Squnion>i. Y i)"
  proof (cases "finite_chain Y")
    case True thus ?thesis using as1 as2 l42 by fastforce 
  next
    case False
    hence "#(\<Squnion>i. Y i) = \<infinity>" using as1 inf_chainl4 by blast
    hence "\<And>n. snth n (\<Squnion>i. Y i) \<noteq> b"
    proof -
      fix n
      obtain j where "Fin n < # (Y j)"  by (metis False Streams.inf_chainl2 as1 inf_chainl3rf less_le) 
      hence "snth n (Y j) \<noteq>b" using as2 snth2sdom by blast
      thus "snth n (\<Squnion>i. Y i) \<noteq> b" using \<open>Fin n < #(Y j)\<close> as1 is_ub_thelub snth_less by blast
    qed
    thus ?thesis using sdom2snth by blast 
  qed
qed

lemma strdw_filter_h: "b\<in>sdom\<cdot>s \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>s)) = #({b} \<ominus> s)"
proof(rule ind [of _s])
  have "adm (\<lambda>a. lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>a)) = #({b} \<ominus> a))" by simp
  thus "adm (\<lambda>a. b \<in> sdom\<cdot>a \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>a)) = #({b} \<ominus> a))" by(simp add: adm_nsdom)
  show "b \<in> sdom\<cdot>\<epsilon> \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>\<epsilon>)) = #({b} \<ominus> \<epsilon>)" by simp
  fix a 
  fix s
  assume IH: " b \<in> sdom\<cdot>s \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>s)) = #({b} \<ominus> s)"
  show " b \<in> sdom\<cdot>(\<up>a \<bullet> s) \<longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(\<up>a \<bullet> s))) = #({b} \<ominus> \<up>a \<bullet> s)"
  proof (cases "a=b")
    case True thus ?thesis by (simp add: sfilter_in singletonI slen_scons stwbl_f stwbl_srtdw) 
  next
    case False
    hence f1:"#({b} \<ominus> \<up>a \<bullet> s) = #({b} \<ominus> s)" using sfilter_nin singletonD by auto
    hence f2:"#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(\<up>a \<bullet> s)) = #({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(s))" using False by auto
    hence "b \<in> sdom\<cdot>(\<up>a \<bullet> s) \<Longrightarrow> b\<in>sdom\<cdot>s" using False by auto
    thus ?thesis using IH f2 local.f1 by auto 
  qed
qed

lemma strdw_filter: "b\<in>sdom\<cdot>s \<Longrightarrow> lnsuc\<cdot>(#({b} \<ominus> srtdw (\<lambda>a. a \<noteq> b)\<cdot>s)) = #({b} \<ominus> s)"
by(simp add: strdw_filter_h)


lemma stwbl_filterlen[simp]: "b\<in>sdom\<cdot>ts \<longrightarrow> #({b} \<ominus> stwbl (\<lambda>a. a \<noteq> b)\<cdot>ts) = Fin 1"
  apply(rule ind [of _ ts])
    apply(rule adm_imp)
     apply simp
    apply simp
   apply simp
  apply auto
  by (metis (mono_tags, lifting) Fin_02bot Fin_Suc One_nat_def lnzero_def sconc_snd_empty sfilter_in sfilter_nin singletonD singletonI slen_scons strict_sfilter strict_slen stwbl_f stwbl_t)


lemma srtdw_conc: "b\<in>sdom\<cdot>ts  \<Longrightarrow> (srtdw (\<lambda>a. a \<noteq> b)\<cdot>(ts \<bullet> as)) = srtdw (\<lambda>a. a \<noteq> b)\<cdot>(ts) \<bullet> as"
  apply(induction ts arbitrary: as)
    apply (rule adm_imp)
     apply auto
   apply(rule admI)
   apply rule+
   apply (metis (no_types, lifting) approxl3 assoc_sconc is_ub_thelub)
proof -
  fix u ts as
  assume as1: "u \<noteq> \<bottom>" and as2: "(\<And>as. b \<in> sdom\<cdot>ts \<Longrightarrow> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(ts \<bullet> as) = srtdw (\<lambda>a. a \<noteq> b)\<cdot>ts \<bullet> as)"
       and as3: "b \<in> sdom\<cdot>(u && ts)"
  obtain a where a_def: "updis a = u" by (metis Exh_Up as1 discr.exhaust) 
  have "a\<noteq>b \<Longrightarrow> b\<in>sdom\<cdot>ts" by (metis UnE a_def as3 lscons_conv sdom2un singletonD) 
  hence "a\<noteq>b \<Longrightarrow> srtdw (\<lambda>a. a \<noteq> b)\<cdot>(\<up>a\<bullet> (ts \<bullet> as)) = srtdw (\<lambda>a. a \<noteq> b)\<cdot>(\<up>a\<bullet> ts) \<bullet> as " using as2 a_def by auto
  thus "srtdw (\<lambda>a. a \<noteq> b)\<cdot>((u && ts) \<bullet> as) = srtdw (\<lambda>a. a \<noteq> b)\<cdot>(u && ts) \<bullet> as "
    by (smt a_def inject_scons lscons_conv sconc_scons stwbl_f stwbl_srtdw) 
qed


lemma stwbl_conc[simp]: "b\<in>sdom\<cdot>ts \<Longrightarrow>
    (stwbl (\<lambda>a. a \<noteq> b)\<cdot>(stwbl (\<lambda>a. a \<noteq> b)\<cdot>ts \<bullet> xs)) =
    (stwbl (\<lambda>a. a \<noteq> b)\<cdot>(ts))"
  apply(induction ts)
    apply(rule adm_imp)
     apply simp
    apply(rule admI)
    apply (metis (no_types, lifting) ch2ch_Rep_cfunR contlub_cfun_arg inf_chainl4 lub_eqI lub_finch2 sconc_fst_inf stwbl2stbl)
   apply simp
  by (smt UnE assoc_sconc sdom2un singletonD stream.con_rews(2) stream.sel_rews(5) stwbl_f stwbl_t surj_scons)











(* takes a function and 2 streams, merges the 2 streams according to the function *)
definition merge:: "('a  \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a stream \<rightarrow> 'b stream \<rightarrow> 'c stream" where
"merge f \<equiv> \<Lambda> s1 s2 . smap (\<lambda> s3. f (fst s3) (snd s3))\<cdot>(szip\<cdot>s1\<cdot>s2)"


lemma merge_unfold: "merge f\<cdot>(\<up>x \<bullet> xs)\<cdot>(\<up>y\<bullet> ys) = \<up>(f x y) \<bullet> merge f\<cdot>xs\<cdot>ys"
  by(simp add: merge_def)

lemma merge_snth[simp]: "Fin n <#xs \<Longrightarrow>Fin n < #ys \<Longrightarrow> snth n (merge f\<cdot>xs\<cdot>ys) = f (snth n xs) (snth n ys)"
  apply(induction n arbitrary:xs ys)
   apply (metis Fin_02bot merge_unfold lnless_def lnzero_def shd1 slen_empty_eq snth_shd surj_scons)
  by (smt Fin_Suc Fin_leq_Suc_leq Suc_eq_plus1_left merge_unfold inject_lnsuc less2eq less2lnleD lnle_conv lnless_def lnsuc_lnle_emb sconc_snd_empty sdropostake shd1 slen_scons snth_rt snth_scons split_streaml1 stream.take_strict surj_scons ub_slen_stake)

lemma merge_eps1[simp]: "merge f\<cdot>\<epsilon>\<cdot>ys = \<epsilon>"
  by(simp add: merge_def)

lemma merge_eps2[simp]: "merge f\<cdot>xs\<cdot>\<epsilon> = \<epsilon>"
  by(simp add: merge_def)

lemma [simp]: "srt\<cdot>(merge f\<cdot>(\<up>a \<bullet> as)\<cdot>(\<up>b \<bullet> bs)) = merge f\<cdot>as\<cdot>bs"
  by (simp add: merge_unfold)

lemma merge_len [simp]: "#(merge f\<cdot>as\<cdot>bs) = min (#as) (#bs)"
by(simp add: merge_def)

lemma merge_commutative: assumes "\<And> a b. f a b = f b a"
  shows "merge f\<cdot>as\<cdot>bs = merge f\<cdot>bs\<cdot>as"
  apply(rule snths_eq)
   apply (simp add: min.commute)
  by (simp add: assms)
  

end