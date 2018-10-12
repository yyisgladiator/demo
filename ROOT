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
  options [quick_and_dirty = false]
  theories
    Streams
    tsynStream

session "bundle" (mustWork) in bundle = "stream" + 
  options [quick_and_dirty = false]
  theories
    SB
    UBundle_Induction
    tsynBundle
    SBElem

session "fun" (mustWork) in fun = "bundle" + 
  options [quick_and_dirty = false]
  theories
    SPF

session "spec" (mustWork) in spec = "fun" + 
  options [quick_and_dirty = false]
  sessions
    HOLMF
  theories
    SPS
    USpec_UFunComp

session "automat" (mustWork) in automat = "spec" + 
  options [quick_and_dirty = true]
  theories
    SpfStep
    dAutomaton
    SpsStep
    ndAutomaton
    ndaTotal

session "abpGenerat" (mustWork) in "abp/generated/abp" = "automat" + 
  options [quick_and_dirty = true]
  theories
    ReceiverAutomaton
    SenderAutomaton
    MediumDatatype
    MediumAutomaton
    FairMediumAutomaton
    Fair99MediumAutomaton
    IdMediumAutomaton
    ABPComponent
    NoMediumABPComponent


session "abpMedium" (mustWork) in "abp/Medium" = "abpGenerat" + 
  options [quick_and_dirty = true]
  theories
    medGeneralAut
    medUnfairStep
    medsBelow
    Medium
    MediumSPF
    MediumSPS

