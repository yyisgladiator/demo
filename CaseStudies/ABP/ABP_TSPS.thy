(*  Title:        ABP_TSPS.thy
    Author:       Jens Christoph Bürger
    e-mail:       jens.buerger@rwth-aachen.de

    Description:  ABP modeled with TSPS
*)

theory ABP_TSPS
  imports "../../TSPS" Receiver Composition Medium
    
begin

  default_sort message 
  
(* TODO: datatype instantiation *)
  
datatype 'a::type MABP = myPair "('a * bool)" | Bool bool | Data 'a

instantiation MABP ::  (countable) countable
begin
instance 
   by (countable_datatype)
end

instantiation MABP ::  (countable) message
begin
  fun ctype_MABP :: "channel \<Rightarrow> 'a MABP set" where
  "ctype_MABP as = range myPair" | 
  "ctype_MABP ds = range Bool" | 
  "ctype_MABP ar = range Data" |
  "ctype_MABP other = {}"

  instance ..
end
  
(* general lemmata *)
lemma tsmap_id[simp]: assumes "inj f" shows "tsMap (inv f)\<cdot>(tsMap f\<cdot>ts) = ts"
apply(induction ts)
by(simp_all add: assms tsmap_delayfun  tsmap_mlscons)

lemma "(\<lambda> x. if x= Bool True then True else False) (Bool False) = False"
  by simp
    
lemma "(\<lambda> x. THE b. x = (Bool b)) (Bool x) = x"
  by (simp add: the_equality)
  
lemma "(inv Bool) (Bool x) = x"
  by (meson MABP.inject(2) f_inv_into_f rangeI) 
    
lemma "(inv Data) (Data x) = x"
  by (meson MABP.inject(3) f_inv_into_f rangeI)
  
  
    
end