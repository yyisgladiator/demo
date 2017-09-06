(*  Title:        ABP_TSPS.thy
    Author:       Jens Christoph Bürger
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  ABP modeled with TSPS
*)

theory ABP_TSPS
  imports "../../TSPS" Receiver Composition Medium "../../TSPF"
    
begin

  default_sort message 
  
(* ----------------------------------------------------------------------- *)
section \<open>Datatype Definition\<close>
(* ----------------------------------------------------------------------- *)
  
datatype 'a::type MABP = BoolPair "('a * bool)" | Bool bool | Data 'a

instantiation MABP ::  (countable) countable
begin
instance 
   by (countable_datatype)
end

instantiation MABP ::  (countable) message
begin
fun ctype_MABP :: "channel \<Rightarrow> 'a MABP set" where
  "ctype_MABP abpIn = range Data" |
  "ctype_MABP abpOut = range Data" |
  "ctype_MABP ds = range BoolPair" |
  "ctype_MABP dr = range BoolPair" |
  "ctype_MABP as = range Bool" |
  "ctype_MABP ar = range Bool" |
  "ctype_MABP other = {}"

  instance ..
end

declare [[show_types]]  
  
(* ----------------------------------------------------------------------- *)
section \<open>Definitions\<close>
(* ----------------------------------------------------------------------- *)  
 
subsection \<open>datatype destructors\<close>
abbreviation invBoolPair :: "'a MABP \<Rightarrow> ('a \<times> bool)" where
"invBoolPair \<equiv> (inv BoolPair)"

abbreviation invBool :: "'a MABP \<Rightarrow> bool" where
"invBool \<equiv> (inv Bool)"

abbreviation invData :: "'a MABP \<Rightarrow> 'a" where
"invData \<equiv> (inv Data)"
  

subsection \<open>receiver\<close> 
definition recvTSPF :: "'a MABP TSPF" where
"recvTSPF \<equiv> 
let recRes = (\<lambda> x. tsRec\<cdot>((tsMap invBoolPair)\<cdot>(x . dr)))
in Abs_CTSPF (\<lambda> x. (tsbDom\<cdot>x = {dr}) \<leadsto> [ar    \<mapsto> tsMap Bool\<cdot>(fst (recRes x)),
                                        abpOut \<mapsto> tsMap Data\<cdot>(snd (recRes x))]\<Omega>)"
  


(* ----------------------------------------------------------------------- *)
section \<open>lemmata\<close>
(* ----------------------------------------------------------------------- *) 
  
subsection \<open>general\<close>
  
lemma tsmap_id[simp]: assumes "inj f" shows "tsMap (inv f)\<cdot>(tsMap f\<cdot>ts) = ts"
apply(induction ts)
by(simp_all add: assms tsmap_delayfun  tsmap_mlscons)
 
subsection \<open>datatype\<close>  
  
  (* inverse BoolPair applied to BoolPair is identity *)
lemma data_bool_pair_inv [simp]: "(invBoolPair) (BoolPair x) = x"
  by (meson MABP.inject(1) f_inv_into_f rangeI)
  
  (* inverse Bool applied to Bool is identity *)
lemma data_bool_inv [simp]: "(inv Bool) (Bool x) = x"
  by (meson MABP.inject(2) f_inv_into_f rangeI)
    
  (* inverse Data applied to Data is identity *)
lemma data_data_inv [simp]: "(inv Data) (Data x) = x"
  by (meson MABP.inject(3) f_inv_into_f rangeI)
  


lemma "(\<lambda> x. if x= Bool True then True else False) (Bool False) = False"
  by simp
    
lemma "(\<lambda> x. THE b. x = (Bool b)) (Bool x) = x"
  by (simp add: the_equality)
  
lemma "(inv Bool) (Bool x) = x"
  by (meson MABP.inject(2) f_inv_into_f rangeI) 
    
lemma "(inv Data) (Data x) = x"
  by (meson MABP.inject(3) f_inv_into_f rangeI)
    
  
  
    
end