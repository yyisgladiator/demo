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
datatype M_pure = DummyMessage nat
hide_const DummyMessage

instance M_pure :: countable
  apply(intro_classes)
  by(countable_datatype)




text \<open>Then one describes the types of each channel. Only Messages included are allowed to be
  transmitted\<close>

definition cMsg :: "channel \<Rightarrow> M_pure set" where 
"cMsg = (\<lambda>c. if c= undefined then {} else undefined)"

lemma cmsgempty_ex:"\<exists>c. cMsg c = {}"
  by (simp add: cMsg_def)


(* Begin Framework: *)
  (* TODO: woanders hin kopieren, eg Prelude *)
datatype timeType = TUntimed | TTimed | TTsyn
(* End Framework *)

definition cTime :: "channel \<Rightarrow> timeType" where
"cTime = undefined"


hide_fact cMsg_def
hide_fact cTime_def

end
