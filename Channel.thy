theory Channel
imports "~~/src/HOL/HOLCF/HOLCF"

begin

text {*This is the total set of channels. While representing an existing network of components or creating a new one, 
 one should add here all channels that occur in the whole network.*}

datatype channel = c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10
             (* for ABP Specification*) | as | ds | ar | dr | abpIn | abpOut

default_sort type

(* 
  Example Instantiation  

datatype M = MNat nat | MBool bool

instantiation M :: message
begin
  fun ctype_M :: "channel \<Rightarrow> M set" where
  "ctype_M c1 = range MNat"  |
  "ctype_M c2 = range MBool"

instance 
apply(intro_classes)
by(countable_datatype)

end
*)
(*
(* Instantiate channel as po, used to instantiate as CPO. *)
instantiation channel :: po
begin
    
  (* Define "below" relation as the equal function *)
  definition below_channel_def: "(op \<sqsubseteq>) \<equiv> (\<lambda> (b1::channel) b2. (b1 = b2))"

  (* Show that the "below" relation satisfies the po assumptions *)
  instance
  apply intro_classes
     apply(simp add:below_channel_def)
    apply (smt below_channel_def below_trans)
   by (simp add: below_channel_def )
end

(* Instantiate channel as cpo, used to define continuous functions. *)
instantiation channel :: cpo
begin
  (* In a channel chain all elements are equal *)
  lemma channel_chain: fixes S :: "nat \<Rightarrow> channel" assumes "chain S" shows "S i = S j"
  by (metis (full_types) assms below_channel_def nat_le_linear po_class.chain_mono)

  instance
  apply intro_classes
  by (metis channel_chain image_cong is_lub_const)
end

instance channel ::discrete_cpo
  apply(intro_classes)
  by (simp add: below_channel_def)


(* the Lub of the chain equals all elements in the chain *)
lemma channel_Lub: fixes S:: "nat \<Rightarrow> channel" assumes "chain S" 
  shows "(\<Squnion>i. S i) = S j"
by (metis assms channel_chain lub_chain_maxelem po_eq_conv)

(* All functions are constant on channels *)
lemma channel_cont[simp]: shows "cont (\<lambda>c::channel . g c)"
by (metis (mono_tags, lifting) channel_Lub contI is_lub_maximal po_eq_conv rangeI ub_rangeI) 



(*
text {*Channels are typed, that means only streams composed of specific alphabet symbols may flow in them (see below "welltyped"). 
These should be initialized by the user as soon as a new channel is needed. For example:*}

datatype M = Nat nat ("\<N> _" )  | Bool bool ("\<bool> _")

abbreviation abrev_invNat :: "M \<Rightarrow> nat" ("\<inverse>\<N>") where
"\<inverse>\<N> m \<equiv> inv Nat m"

abbreviation abrev_invBool :: "M \<Rightarrow> bool" ("\<inverse>\<bool>") where
"\<inverse>\<bool> m \<equiv> inv Bool m"

instance M :: countable
by countable_datatype



fun ctype :: "channel \<Rightarrow> M set" where
"ctype c1 = range Nat" |
"ctype c2 = range Nat" |
"ctype c3 = range Nat" |
"ctype c4 = range Nat" 



lemma [simp]:"\<inverse>\<N> (\<N> x) = x"
by (meson M.inject(1) f_inv_into_f rangeI)

lemma [simp]:"\<inverse>\<bool> (\<bool> x) = x"
by (meson M.inject(2) f_inv_into_f rangeI)

*)

*)
  
  
instantiation channel :: finite
begin
  instance
  apply(intro_classes)
  proof - 
    have f1: "(UNIV :: channel set) = {c1 , c2 , c3 , c4 , c5 , c6 , c7 , c8 , c9 , c10 , as , ds , ar , dr , abpIn , abpOut}"
    proof - 
      have "\<And>a. (a \<in> (UNIV :: channel set)) = (a \<in> {c1 , c2 , c3 , c4 , c5 , c6 , c7 , c8 , c9 , c10 , as , ds , ar , dr , abpIn , abpOut})"
      proof - 
        fix a
        show "(a \<in> (UNIV :: channel set)) = (a \<in> {c1 , c2 , c3 , c4 , c5 , c6 , c7 , c8 , c9 , c10 , as , ds , ar , dr , abpIn , abpOut})"
          by(simp add: channel.nchotomy)
      qed
      then show ?thesis
        by auto
    qed
    show "finite (UNIV :: channel set)"
      by (simp add: f1)  
  qed
end   
  
  
end
