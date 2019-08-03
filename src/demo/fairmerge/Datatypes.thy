theory Datatypes

imports HOLCF

begin

default_sort type

datatype channel = cin1 | cin2 | cout | cbot



section \<open>Message Definition\<close>

text\<open>The same is true for the "Message" Datatype. Every kind of message has to be described here:\<close>
datatype M = \<N> nat | \<B> bool | eps

text \<open>* Introduce symbol @{text ~} for empty time-slots called eps. \<close>
syntax "@eps" :: M ("~")
translations "~" == "CONST eps"

instance M::countable
  apply(countable_datatype)
  done

text \<open>Then one describes the types of each channel. Only Messages included are allowed to be
  transmitted\<close>
fun ctype :: "channel \<Rightarrow> M set" where 
"ctype cin1 = range \<N>" |
"ctype cin2 = range \<N>" |
"ctype cout = range \<N>" |
"ctype _ = {}"

lemma ctypeempty_ex:"\<exists>c. ctype c = {}"
  using ctype.simps by blast

end
