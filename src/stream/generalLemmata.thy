theory generalLemmata
imports stream.Streams
begin

lemma stream_snth_shd: assumes"\<And>n.  P(snth n s)"
  shows"P(shd s)"
  by (metis assms snth_shd)

lemma stream_snth:  assumes"\<And>n.  P(snth n (\<up>m \<bullet> s))"
  shows"P(m)"
  by (metis assms shd1 snth_shd)

lemma stream_snth_snth: assumes"\<And>n.  P(snth n (\<up>m \<bullet> s))"
      shows"P(snth n(s))"
  by (metis assms snth_scons)

lemma stream_snth_srt:  assumes"\<And>n. P(snth n (s))"
      shows"P(snth n(srt\<cdot>s))"
  by (metis assms snth_rt)

end