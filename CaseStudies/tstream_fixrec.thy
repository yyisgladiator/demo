theory tstream_fixrec
(* This theory enables the use of tStreams with fixrec. Especially pattern-matching with the first 
Element of the stream is supported. Hence it is possible to create seperate cases for "first Element is Tick"
and "first element is Message" *)
  
(* Created by Sebastian Stüber.
   sebastian.stueber@rwth-aachen.de *)
  
  
imports "../TStream"  (* "~~/src/HOL/HOLCF/Library/Option_Cpo" *)

begin

lemma tstickcount_adm [simp]: "adm (\<lambda>a. #\<surd> a \<le> #\<surd> f\<cdot>a)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a tstream"
  assume a1: "chain Y"
  assume a2: "\<forall>i. #\<surd> Y i \<le> #\<surd> f\<cdot>(Y i)"
  obtain nn :: "(nat \<Rightarrow> 'a tstream) \<Rightarrow> nat \<Rightarrow> nat" where
      "\<forall>f. \<not> chain f \<or> finite_chain f \<or> (\<forall>n. Fin n \<le> #\<surd> f (nn f n))"
    by (meson exist_tslen)
  then have f3: "\<And>n. Fin n \<le> #\<surd> f\<cdot>(Y (nn Y n)) \<or> finite_chain Y"
    using a2 a1 trans_lnle by blast
  have "\<And>l c ca f n. (l::lnat) \<le> c\<cdot>(ca\<cdot>(Lub f::'a tstream)::'b tstream) \<or> \<not> l \<le> c\<cdot>(ca\<cdot>(f n)) \<or> \<not> chain f"
    by (meson is_ub_thelub lnle_def monofun_cfun_arg trans_lnle)
  then show "#\<surd> \<Squnion>n. Y n \<le> #\<surd> f\<cdot>(\<Squnion>n. Y n)"
    using f3 a2 a1 by (metis Suc_n_not_le_n l42 less2nat linorder_not_less lncases order_less_irrefl)
qed

lemma "t\<noteq>\<bottom>\<Longrightarrow>#\<surd> (tsMLscons\<cdot>t\<cdot>ts) = #\<surd>ts"
  apply(cases "ts=\<bottom>")
   apply simp
  oops
    
lemma assumes "\<And>ts. f\<cdot>(delayFun\<cdot>ts) = delayFun\<cdot>(f\<cdot>ts)"
  shows "#\<surd>ts \<le> #\<surd>(f\<cdot>ts)"
  apply (induction ts) 
apply simp_all
  apply (metis assms delayFun.rep_eq lnsuc_lnle_emb tstickcount_tscons)
  oops
    
    
    
(* demo that the old fixrec is not working *)

  (* this function is removing all ticks *)
fixrec demo::"'a event stream \<rightarrow> 'a event stream" where
"t \<noteq> \<bottom> \<Longrightarrow> t=updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = ts" |
(unchecked) "t \<noteq> \<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = t&&ts"


lemma "t \<noteq> \<bottom> \<Longrightarrow> t\<noteq>updis \<surd> \<Longrightarrow> demo\<cdot>(lscons\<cdot>t\<cdot>ts) = t&&ts"
apply fixrec_simp
oops (* good luck proving this :/ *)
  
  
 
  (* Case Studies *)

fixrec teees:: "'a tstream \<rightarrow>'a tstream" where
"teees\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = tsInfTick" |  (* t is a 'event discr u', ts a tstream *)
"t\<noteq>DiscrTick \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> teees\<cdot>(tsLscons\<cdot>(up\<cdot>t)\<cdot>ts) = ts"

lemma [simp]: "teees\<cdot>\<bottom> = \<bottom>"
  by(fixrec_simp)

    (* First Element is a Tick *)
lemma "teees\<cdot>(delayFun\<cdot>ts) = tsInfTick"
  by fixrec_simp
    
    (* First Element is not a Tick *)
lemma "t\<noteq>DiscrTick \<Longrightarrow> ts\<noteq>\<bottom> \<Longrightarrow> teees\<cdot>(tsLscons\<cdot>(up\<cdot>t)\<cdot>ts) = ts"
  by simp

lemma "teees\<cdot>\<bottom>= \<bottom>"
  by simp
    

 
    
    
(* removes first tick (if there is a first tick *)
fixrec tee :: "'a tstream \<rightarrow> 'a tstream" where
"tee\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = ts"  (* this pattern is only called if the input stream starts with a tick *)



fixrec tsAbsNew :: "'a tstream \<rightarrow> 'a stream" where
"tsAbsNew\<cdot>(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>ts) = tsAbsNew\<cdot>ts" |   (* ignore ticks *)  
"ts\<noteq>\<bottom> \<Longrightarrow> tsAbsNew\<cdot>(tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>t))\<cdot>ts) = up\<cdot>t && tsAbsNew\<cdot>ts"  (* prepend first message and go on *)  



lemma [simp]: "tsAbsNew\<cdot>\<bottom>=\<bottom>"
  by fixrec_simp

lemma [simp]: "tsAbsNew\<cdot>(delayFun\<cdot>ts) = tsAbsNew\<cdot>ts"
  by fixrec_simp
  
lemma tsabs_new_msg [simp]: "xs\<noteq>\<bottom> \<Longrightarrow> tsAbsNew\<cdot>(tsMLscons\<cdot>(up\<cdot>x)\<cdot>xs) = up\<cdot>x && (tsAbsNew\<cdot>xs)"
  by fixrec_simp+

lemma tsmlscons2tslscons: "xs\<noteq>\<bottom> \<Longrightarrow> (tsMLscons\<cdot>(up\<cdot>x)\<cdot>xs) = tsLscons\<cdot>(up\<cdot>(uMsg\<cdot>x))\<cdot>xs"
  by(simp add: tsMLscons_def)
    
lemma "tsAbsNew\<cdot>ts= tsAbs\<cdot>ts"
  apply (induction)
  apply simp_all
  apply (simp add: tsabs_delayfun)
  using updis_exists tsabs_mlscons by fastforce
    
    

    


    
    
lemma tslscons_discrtick [simp]: "(tsLscons\<cdot>(up\<cdot>DiscrTick)\<cdot>i) \<noteq>\<bottom>"
  apply(simp add: tslscons_insert)
  by (metis DiscrTick_def tslscons_insert tslscons_nbot2)
  

lemma [simp]: "ts\<noteq>\<bottom>\<Longrightarrow>match_tstream\<cdot>ts\<cdot>k = k\<cdot>(tsLshd\<cdot>ts)\<cdot>(tsRt\<cdot>ts)"
oops
lemma [simp]: "ts\<noteq>\<bottom> \<Longrightarrow> tsLshd\<cdot>ts\<noteq>\<bottom>" 
  oops
       
end  