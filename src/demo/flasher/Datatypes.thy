theory Datatypes

imports inc.Prelude

begin

default_sort type


datatype channel = c1 | c2 | c3 | cin1 | cin2 | cout



section \<open>Message Definition\<close>

text\<open>The same is true for the "Message" Datatype. Every kind of message has to be described here:\<close>
datatype M_pure = \<N> nat | \<B> bool

text \<open>Instantiate @{type M_pure} as countable. This is necessary for using @{type M_pure} streams. }\<close>
instance M_pure::countable
  apply(countable_datatype)
  done

lemma inj_B[simp]:"inj \<B>"
  by (simp add: inj_def)

lemma inj_Bopt[simp]:"inj (map_option \<B>)"
  by (simp add: option.inj_map)

text \<open>Then one describes the types of each channel. Only Messages included are allowed to be
  transmitted\<close>
fun cMsg :: "channel \<Rightarrow> M_pure set" where
"cMsg c1 = range \<N>" |
"cMsg c2 = range \<B>" |
"cMsg c3 = {}" |
"cMsg _ = range \<B>"

text\<open>Timing properties of each channel\<close>
fun cTime :: "channel \<Rightarrow> timeType" where
"cTime cin1 = TTsyn" |
"cTime cin2 = TTsyn" |
"cTime cout = TTsyn" |
"cTime _ = undefined"

lemma cmsgempty_ex:"\<exists>c. cMsg c = {}"
  using cMsg.simps by blast

end
