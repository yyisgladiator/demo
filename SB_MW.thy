theory SB_MW
imports SB

begin
  
definition sbHd :: "'m SB \<rightarrow> (channel \<rightharpoonup> 'm discr\<^sub>\<bottom>)" where
"sbHd \<equiv> \<Lambda> sb. (\<lambda>c. (c \<in> sbDom\<cdot>sb) \<leadsto> (lshd\<cdot>(sb . c)))" 


(* sbRt is defined in SB.thy *)

definition sbLscons :: "(channel \<rightharpoonup> 'm discr\<^sub>\<bottom>) \<Rightarrow> 'm SB \<rightarrow> 'm SB" where
"sbLscons sb1 \<equiv> \<Lambda> sb. (\<lambda>c. (c \<in> (sbDom\<cdot>sb \<inter> (dom sb1))) \<leadsto> (lscons\<cdot>(sb1 \<rightharpoonup> c)\<cdot>(sb . c)))\<Omega>"

(* Some type problems

definition convDiscrUp :: "(channel \<rightharpoonup> 'm) \<Rightarrow> (channel \<rightharpoonup> 'm discr\<^sub>\<bottom>)" where
"convDiscrUp sb \<equiv> (\<lambda>c. (c \<in> dom sb) \<leadsto> (Discr (sb \<rightharpoonup> c)))"

definition convSB :: "(channel \<rightharpoonup> 'm discr\<^sub>\<bottom>) \<Rightarrow> 'm SB" where
"convSB sb \<equiv> (\<lambda>c. (c \<in> dom sb) \<leadsto> (sup'(sb \<rightharpoonup> c)))\<Omega>"

*)

end