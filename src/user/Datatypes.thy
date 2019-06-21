theory Datatypes

imports HOLCF

begin

default_sort type

section \<open>Datatype\<close>
text \<open>The channel-datatype is fixed before the proof begins.
  This datatype contains every channel, that is used. There is no way to "dynamically" add
 channels, except modifying this datatype\<close>

datatype channel = DummyChannel nat

hide_const DummyChannel


section \<open>Message Definition\<close>

text\<open>The same is true for the "Message" Datatype. Every kind of message has to be described here:\<close>
datatype M = DummyMessage nat
hide_const DummyMessage

instance M :: countable
  apply(intro_classes)
  by(countable_datatype)




text \<open>Then one describes the types of each channel. Only Messages included are allowed to be
  transmitted\<close>
definition ctype :: "channel \<Rightarrow> M set" where 
"ctype = undefined"

hide_fact ctype_def




end
