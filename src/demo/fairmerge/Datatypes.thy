theory Datatypes

imports inc.Prelude

begin

default_sort type

datatype channel = cin1 | cin2 | cout | cbot



section \<open>Message Definition\<close>

text\<open>The same is true for the "Message" Datatype. Every kind of message has to be described here:\<close>
datatype M_pure = \<N> nat | \<B> bool


instance M_pure::countable
  apply(countable_datatype)
  done

text \<open>Then one describes the types of each channel. Only Messages included are allowed to be
  transmitted\<close>
fun cMsg :: "channel \<Rightarrow> M_pure set" where 
"cMsg cin1 = range \<N>" |
"cMsg cin2 = range \<N>" |
"cMsg cout = range \<N>" |
"cMsg _ = {}"

lemma cmsgempty_ex:"\<exists>c. cMsg c = {}"
  using cMsg.simps by blast

fun cTime :: "channel \<Rightarrow> timeType" where 
"cTime cin1 = TTsyn" |
"cTime cin2 = TTsyn" |
"cTime cout = TTsyn" |
"cTime _ = undefined"

end
