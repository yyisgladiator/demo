theory sscanlA
  imports Streams
begin

(* Stateful scanline *)
(* The user has more control. Instead of the last output ('b)  a state ('s) is used as next input *)
definition sscanlA :: "'s \<Rightarrow> ('s \<Rightarrow>'a \<Rightarrow> ('b \<times>'s)) \<Rightarrow> 'a stream \<rightarrow> 'b stream" where
"sscanlA s0 f \<equiv> \<Lambda> s. sprojfst\<cdot>(sscanl (\<lambda>(_,b). f b) (undefined, s0)\<cdot>s)"


lemma sscanla_cont: "cont (\<lambda>s. sprojfst\<cdot>(sscanl (\<lambda>(_,b). f b) (undefined, s0)\<cdot>s))"
  by simp

lemma sscanla_len [simp]: "#(sscanlA s0 f\<cdot>s) = #s"
  by(simp add: sscanlA_def slen_sprojfst)

lemma sscanla_bot [simp]: "sscanlA s0 f\<cdot>\<bottom> = \<bottom>"
  by (simp add: sscanlA_def)

lemma sscanla_step [simp]: "sscanlA s0 f\<cdot>(\<up>a \<bullet> as) = \<up>(fst (f s0 a)) \<bullet> sscanlA (snd (f s0 a)) f\<cdot>as"
  apply(simp add: sscanlA_def sprojfst_def)
proof -
  have "(case f s0 a of (a, x) \<Rightarrow> f x) = (case (undefined::'a, snd (f s0 a)) of (a, x) \<Rightarrow> f x)"
by (metis (no_types) old.prod.case prod.collapse)
  then have "\<up>(shd as) \<bullet> srt\<cdot>as = as \<longrightarrow> sscanl (\<lambda>(a, y). f y) (f s0 a)\<cdot>as = sscanl (\<lambda>(a, y). f y) (undefined, snd (f s0 a))\<cdot> (\<up>(shd as) \<bullet> srt\<cdot>as)"
    by (metis (no_types) sscanl_scons)
  then show "\<up>(fst (f s0 a)) \<bullet> smap fst\<cdot> (sscanl (\<lambda>(a, y). f y) (f s0 a)\<cdot> as) = \<up>(fst (f s0 a)) \<bullet> smap fst\<cdot> (sscanl (\<lambda>(a, y). f y) (undefined, snd (f s0 a))\<cdot> as)"
    using surj_scons by force
qed

end
