session "inc" (mustWork) in inc = "HOLCF" +
  options [quick_and_dirty = false]
  theories
    Channel
    LNat
    SetPcpo
    Reversed
    Prelude
    OptionCpo
    UnivClasses
    CPOFix


session "HOLMF" (mustWork) in HOLMF = "inc" +
  options [quick_and_dirty = false]
  theories
    LongChain
    Division
    LFP

session "stream" (mustWork) in stream = "inc" +
  options [quick_and_dirty = true]
  theories
    Streams
    tsynStream

session "bundle" (mustWork) in bundle = "stream" + 
  options [quick_and_dirty = true]
  theories
    SB
    UBundle_Induction
    tsynBundle

session "fun" (mustWork) in fun = "bundle" + 
  options [quick_and_dirty = true]
  theories
    SPF

session "spec" (mustWork) in spec = "fun" + 
  options [quick_and_dirty = true]
  sessions
    HOLMF
  theories
    SPS

session "automat" (mustWork) in automat = "spec" + 
  options [quick_and_dirty = true]
  theories
    SpfStep
    dAutomaton
    SpsStep
    ndAutomaton

session "automatCaseStudy" (mustWork) in "automat/CaseStudy" = "automat" + 
  options [quick_and_dirty = true]
  theories
    medFairStep
    medUnfairStep

session "abp" (canFail) in abp = "automat" + 
  options [quick_and_dirty = true]
  theories
    Receiver
