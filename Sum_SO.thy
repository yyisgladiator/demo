theory Sum_SO
imports Main TStream StreamCase_Study
begin

declare [[show_types]]

definition sum :: "nat stream \<Rightarrow> nat stream" where
"sum = fix\<cdot>(\<Lambda> f. (\<lambda> s. if s = \<epsilon> then \<epsilon> else \<up>(shd s) \<bullet> (smap (plus (shd s))\<cdot>(f (srt\<cdot>s)))))"

primrec stream_to_list :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a list" where
"stream_to_list 0 s = []" |
"stream_to_list (Suc n) s = (if s = \<epsilon> then [] else stream_to_list n s @ [snth n s])"

fun sum_list :: "nat list \<Rightarrow> nat" where
"sum_list [] = 0" |          
"sum_list l = sum_list (butlast l) + last l"





lemma sum_list_tail : "sum_list (l @ [tail]) = sum_list l + tail" by (metis snoc_eq_iff_butlast sum_list.elims)

lemma unwrap_sum : "sum = (\<Lambda> f. (\<lambda> s. if s = \<epsilon> then \<epsilon> else \<up>(shd s) \<bullet> (smap (plus (shd s))\<cdot>(f (srt\<cdot>s)))))\<cdot>sum" using fix_eq by (metis (no_types, lifting) sum_def)

lemma recursive_sum : "sum = (\<lambda> s. if s = \<epsilon> then \<epsilon> else \<up>(shd s) \<bullet> (smap (plus (shd s))\<cdot>(sum (srt\<cdot>s))))" using unwrap_sum by simp

lemma smap_hd_rst : "s \<noteq> \<epsilon> \<Longrightarrow> smap f\<cdot>s = \<up>(f (shd s)) \<bullet> smap f\<cdot>(srt\<cdot>s)" by (metis smap_scons surj_scons)

lemma srt_decrements_length : "s \<noteq> \<epsilon> \<Longrightarrow> #s = lnsuc\<cdot>(#(srt\<cdot>s))" by (metis slen_scons surj_scons)

lemma empty_is_shortest : "Fin n < #s \<Longrightarrow> s \<noteq> \<epsilon>" by (metis Fin_0 less_le lnle_Fin_0 strict_slen)

lemma convert_inductive_asm : "Fin (Suc n) < #s \<Longrightarrow> Fin n < #s" by (metis Fin_leq_Suc_leq less_le not_le)

lemma only_empty_has_length_0 : "#s \<noteq> 0 \<Longrightarrow> s \<noteq> \<epsilon>" by simp

lemma srt_drop : "srt\<cdot>(sdrop n\<cdot>s) = sdrop (Suc n)\<cdot>s" by (simp add: sdrop_back_rt)

lemma drop_not_all : "Fin n < #s \<Longrightarrow> sdrop n\<cdot>s \<noteq> \<epsilon>"
proof (induct n)
  show "Fin 0 < #s \<Longrightarrow> sdrop 0\<cdot>s \<noteq> \<epsilon>" by auto
  
  have "\<And> n. Fin n < #s \<Longrightarrow> #(sdrop n\<cdot>s) = lnsuc\<cdot>(#(srt\<cdot>(sdrop n\<cdot>s)))" by (metis not_le sdrop_stakel1 srt_decrements_length ub_slen_stake)
  hence "\<And> n. Fin n < #s \<Longrightarrow> sdrop n\<cdot>s \<noteq> \<epsilon>" using only_empty_has_length_0 by fastforce
  thus "\<And> n. (Fin n < #s \<Longrightarrow> sdrop n\<cdot>s \<noteq> \<epsilon>) \<Longrightarrow> Fin (Suc n) < #s \<Longrightarrow> sdrop (Suc n)\<cdot>s \<noteq> \<epsilon>" by simp
qed

lemma map_plus_0 : "smap (plus (0::nat))\<cdot>s = s"
proof -
  have "\<And> n. Fin n < #s \<Longrightarrow> snth n (smap (plus 0)\<cdot>s) = snth n s" by (simp add: smap_snth_lemma)
  thus ?thesis by (simp add: snths_eq)
qed

lemma merge_sum : "Fin n < #(s :: nat stream) \<Longrightarrow> sum_list(stream_to_list n s) + shd (sdrop n\<cdot>s) = sum_list(stream_to_list (Suc n) s)"  
by (simp add: sum_list_tail empty_is_shortest snth_def)

lemma merge_map_plus : "smap (plus x)\<cdot>(smap (plus y)\<cdot>(s :: nat stream)) = smap (plus (x + y))\<cdot>s"
proof (cases "s = \<epsilon>")
  case True
  thus ?thesis by simp
  next
  case False
  hence "\<And> n. Fin n < #s \<Longrightarrow> snth n (smap (op + x)\<cdot>(smap (op + y)\<cdot>s)) = snth n (smap (op + (x + y))\<cdot>s)" by (simp add: smap_snth_lemma)
  thus ?thesis by (simp add: snths_eq)
qed

(* Demonstrates that dropping an element from the output is equivalent to dropping an element from the input and adding that element to the
   sum that gets mapped over the output. This theorem is crucial for the inductive step since it converts between the case 'n' and 'n + 1'. *)
theorem shift_sum : "Fin n < #s \<Longrightarrow> srt\<cdot>(smap (plus (sum_list (stream_to_list n s)))\<cdot>(sum (sdrop n\<cdot>s))) =
                                        smap (plus (sum_list (stream_to_list (Suc n) s)))\<cdot>(sum (sdrop (Suc n)\<cdot>s))"
proof -
  assume asm : "Fin n < #s"
  have "smap (plus (sum_list (stream_to_list n s)))\<cdot>(sum (sdrop n\<cdot>s)) = 
        smap (plus (sum_list (stream_to_list n s)))\<cdot>(if sdrop n\<cdot>s = \<epsilon> then \<epsilon> else \<up>(shd (sdrop n\<cdot>s)) \<bullet> smap (plus (shd (sdrop n\<cdot>s)))\<cdot>(sum (srt\<cdot>(sdrop n\<cdot>s))))"
  by (simp add: recursive_sum)
  
  hence "smap (plus (sum_list (stream_to_list n s)))\<cdot>(sum (sdrop n\<cdot>s)) = 
         smap (plus (sum_list (stream_to_list n s)))\<cdot>(\<up>(shd (sdrop n\<cdot>s)) \<bullet> smap (plus (shd (sdrop n\<cdot>s)))\<cdot>(sum (srt\<cdot>(sdrop n\<cdot>s))))"
  using drop_not_all asm by auto
         
  hence "smap (plus (sum_list (stream_to_list n s)))\<cdot>(sum (sdrop n\<cdot>s)) = 
         \<up>((sum_list (stream_to_list n s)) + shd (sdrop n\<cdot>s)) \<bullet> smap (plus (sum_list (stream_to_list n s)))\<cdot>(smap (plus (shd (sdrop n\<cdot>s)))\<cdot>(sum (srt\<cdot>(sdrop n\<cdot>s))))"
  using smap_hd_rst by auto
  
  hence "smap (plus (sum_list (stream_to_list n s)))\<cdot>(sum (sdrop n\<cdot>s)) = 
         \<up>(sum_list (stream_to_list (Suc n) s)) \<bullet> smap (plus (sum_list (stream_to_list (Suc n) s)))\<cdot>(sum (sdrop (Suc n)\<cdot>s))"
  using merge_sum merge_map_plus srt_drop asm by metis
  
  thus ?thesis by simp
qed
        
(* Proof by induction that sum accumulates a running sum that gets mapped over sum applied to the remainder of the output. *)
theorem sum_sdrop_n : "Fin n < #s \<Longrightarrow> sdrop n\<cdot>(sum s) = smap (plus (sum_list (stream_to_list n s)))\<cdot>(sum (sdrop n\<cdot>s))"
proof (induct n)
  show "sdrop 0\<cdot>(sum s) = smap (plus (sum_list (stream_to_list 0 s)))\<cdot>(sum (sdrop 0\<cdot>s))" by (simp add: map_plus_0)
  
  show "\<And> n. (Fin n < #s \<Longrightarrow> sdrop n\<cdot>(sum s) = smap (plus (sum_list (stream_to_list n s)))\<cdot>(sum (sdrop n\<cdot>s))) \<Longrightarrow>
              Fin (Suc n) < #s \<Longrightarrow> sdrop (Suc n)\<cdot>(sum s) = smap (plus (sum_list (stream_to_list (Suc n) s)))\<cdot>(sum (sdrop (Suc n)\<cdot>s))"
  proof -
    fix n
    assume inductive_asm : "Fin n < #s \<Longrightarrow> sdrop n\<cdot>(sum s) = smap (plus (sum_list (stream_to_list n s)))\<cdot>(sum (sdrop n\<cdot>s))"
    show "Fin (Suc n) < #s \<Longrightarrow> sdrop (Suc n)\<cdot>(sum s) = smap (plus (sum_list (stream_to_list (Suc n) s)))\<cdot>(sum (sdrop (Suc n)\<cdot>s))"
    proof -
      assume asm : "Fin (Suc n) < #s"
      hence "smap (plus (sum_list (stream_to_list (Suc n) s)))\<cdot>(sum (sdrop (Suc n)\<cdot>s)) = srt\<cdot>(smap (plus (sum_list (stream_to_list n s)))\<cdot>(sum (sdrop n\<cdot>s)))"
      using convert_inductive_asm shift_sum by fastforce
      
      hence "smap (plus (sum_list (stream_to_list (Suc n) s)))\<cdot>(sum (sdrop (Suc n)\<cdot>s)) = srt\<cdot>(sdrop n\<cdot>(sum s))"
      using asm inductive_asm convert_inductive_asm by force
      
      thus ?thesis by (simp add: srt_drop)
    qed
  qed
qed

(* Finally verifies that the element at index n of the output is equivalent to summing the first n + 1 items of the input *)
theorem sum_property : "Fin n < #s \<Longrightarrow> snth n (sum s) = (sum_list (stream_to_list (Suc n) s))"
proof -
  assume asm : "Fin n < #s"
  have "snth n (sum s) = shd (sdrop n\<cdot>(sum s))" by (simp add: snth_def)
  hence "snth n (sum s) = shd (smap (plus (sum_list (stream_to_list n s)))\<cdot>(sum (sdrop n\<cdot>s)))" using asm sum_sdrop_n by fastforce
  hence "snth n (sum s) = shd (smap (plus (sum_list (stream_to_list n s)))\<cdot>(\<up>(shd (sdrop n\<cdot>s)) \<bullet> (smap (plus (shd (sdrop n\<cdot>s)))\<cdot>(sum (srt\<cdot>(sdrop n\<cdot>s))))))"
  by (metis asm recursive_sum drop_not_all)
  hence "snth n (sum s) =  (sum_list (stream_to_list n s)) + shd (sdrop n\<cdot>s)" using asm smap_hd_rst by auto
  thus ?thesis using merge_sum asm by simp
qed








(* Neue Sachen von Sebastian Stüber *)
lemma sum3_sumlist: "Fin n < #s \<Longrightarrow> snth n (sum3\<cdot>s) = (sum_list (stream_to_list (Suc n) s))"
  apply(induction n arbitrary: s)
   apply auto[1]
  apply simp
  apply rule+
   apply simp
  apply rule
proof -
  fix na :: nat and sa :: "nat stream"
  assume a1: "Fin (Suc na) < #sa"
  assume a2: "sa \<noteq> \<epsilon>"
  assume a3: "\<And>s. Fin na < #s \<Longrightarrow> snth na (sum3\<cdot>s) = sum_list (if s = \<epsilon> then [] else stream_to_list na s @ [snth na s])"
  have f4: "snth (Suc na) (sum3\<cdot>sa) = snth na (sscanl op + 0\<cdot>sa) + snth (Suc na) sa"
    using a1 by (simp add: sscanl_snth sum3_def)
  have "Fin na < #sa"
    using a1 convert_inductive_asm by blast
  then have "snth (Suc na) (sum3\<cdot>sa) = sum_list (stream_to_list (Suc na) sa) + shd (sdrop (Suc na)\<cdot>sa)"
    using f4 a3 by (simp add: snth_def sum3_def)
  then have "snth (Suc na) (sum3\<cdot>sa) = sum_list (stream_to_list (Suc (Suc na)) sa)"
    using a1 merge_sum by presburger
  then show "snth (Suc na) (sum3\<cdot>sa) = sum_list (stream_to_list na sa @ [snth na sa, snth (Suc na) sa])"
    using a2 by simp
qed

  
definition sum2 :: "nat stream \<Rightarrow> nat stream" where
"sum2 = fix\<cdot>(\<Lambda> f. (\<lambda> s. (lshd\<cdot>s) && (smap (plus (shd s))\<cdot>(f (srt\<cdot>s)))))"

lemma sum2_unfold: "sum2 s = (lshd\<cdot>s) && (smap (plus (shd s))\<cdot>(sum2 (srt\<cdot>s)))"
apply(simp add: sum2_def)
apply(subst fix_eq)
apply simp
done

lemma sum2sum_help: "(\<Lambda> f. (\<lambda> s. if s = \<epsilon> then \<epsilon> else \<up>(shd s) \<bullet> (smap (plus (shd s))\<cdot>(f (srt\<cdot>s))))) 
  = (\<Lambda> f. (\<lambda> s. (lshd\<cdot>s) && (smap (plus (shd s))\<cdot>(f (srt\<cdot>s)))))" 
apply (rule cfun_eqI)
apply simp
by (metis (no_types, hide_lams) lscons_conv stream.exhaust stream.sel_rews(4) surj_scons)

lemma sum2sum2: "sum = sum2"
by(simp add: sum_def sum2_def sum2sum_help)

lemma "#s = \<infinity> \<Longrightarrow> # (sum s) = #s"
oops

lemma sum_len [simp]: "# (sum s) = #s"
apply(rule ind [of _s])
apply(rule admI)
apply auto
sorry

lemma sum32sum: "sum3\<cdot>s = sum s"
apply(rule snths_eq)
apply auto
by (simp add: sum3_sumlist sum_property)

lemma "sum4\<cdot>s = sum s"
by (simp add: sum32sum sum42sum3)

lemma sum32sum2: "sum3\<cdot>s = sum2 s"
by (simp add: sum2sum2 sum32sum)

end
