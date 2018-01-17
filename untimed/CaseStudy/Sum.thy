theory Sum

(* Taken from /core/CaseStudies/StreamCase_Study.thy *)
imports "../Streams" "../../inc/Event"
begin

fun plus_event:: "nat \<Rightarrow> nat event \<Rightarrow> (nat event \<times> nat)" where
"plus_event n Tick = (Tick, n)" |
"plus_event n (Msg m) = (Msg (m+n), n+m)"

definition sum :: "nat event stream \<rightarrow> nat event stream" where
"sum \<equiv> sscanlA plus_event 0"


lemma sum_eps [simp]:"sum\<cdot>\<epsilon> = \<epsilon>"
  by (simp add: sum_def)


lemma [simp]: "#(sum\<cdot>xs) = #xs"
  by(simp add: sum_def)



lemma sum_shd [simp]: "shd (sum\<cdot>as) = shd as"
  apply(simp add: sum_def)
  by (metis (no_types, lifting) Pair_eqD1 Sum.sum_def add.right_neutral plus_event.elims prod.collapse shd1 sscanla_step sum_eps surj_scons)


(* O_n = O_n-1 + I_ n *)
lemma sum_snth: "Fin n < #as \<Longrightarrow> snth (Suc n) (sum\<cdot>(\<up>a \<bullet> as)) = snth n (sum\<cdot>as) + a"
  apply(induction n arbitrary: as a)
   apply(simp add: sum_def sscanl_srt snth_rt)
   apply (metis add.commute add.left_neutral lnsuc_neq_0_rev shd1 slen_empty_eq sscanl_scons surj_scons)
by (smt ab_semigroup_add_class.add_ac(1) add.commute convert_inductive_asm snth_scons sscanl_scons sscanl_snth sum_def)


lemma sum_snth_inf[simp]: "snth n (sum\<cdot>(\<up>x\<infinity>)) = (Suc n) * x"
  apply(induction n)
   apply (metis add.commute mult_Suc mult_is_0 shd1 sinftimes_unfold snth_shd sscanl_scons sum_def)
  by (simp add: sscanl_snth sum_def)

lemma "(sum\<cdot>\<up>1\<infinity>) = (siterate Suc 1)"
  apply(rule sinf_snt2eq)
    apply simp
   apply simp
  using snth_siterate_Suc by auto

lemma siter_snth2[simp]: "snth n (siterate (op + x) a) = a+ (n * x)"
  apply(induction n arbitrary: x)
   apply (simp)
  by (simp add: snth_snth_siter)


lemma sum_2_siter: "(sum\<cdot>\<up>x\<infinity>) = (siterate (\<lambda> a. x+a) x)"
  apply(rule sinf_snt2eq)
    by auto

lemma "sum\<cdot>(\<up>1\<infinity>) = siterate Suc 1"
  using One_nat_def Suc2plus sum_2_siter by presburger

lemma "sum\<cdot>(\<up>0\<infinity>) = \<up>0\<infinity>"
  by (simp add: siter2sinf2 sum_2_siter)

lemma "sum\<cdot>(<[5,1,0,3]>) = <[5,6,6,9]>"
by(simp add: sum_def)





  (* add takes 2 nat-streams and adds them component-wise *)

lemma add_zero [simp]: "add\<cdot>(sum\<cdot>s)\<cdot>\<up>0\<infinity> = sum\<cdot>s"
  apply(rule snths_eq)
   apply simp
  by (auto simp add: add_snth)

end