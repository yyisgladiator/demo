session "Streams" (mustWork) = "HOLCF" +
  options [quick_and_dirty = false]
  theories
    Streams

session "TStreamSorry" (mustWork) = "Streams" + 
  options [quick_and_dirty = true]
  theories
    TStream   
    fixrec_tstream
    "CaseStudies/TimedABP"
    TStream_DS
 
 
session "TSPSSorry" (mustWork) = "TStreamSorry" + 
  options [quick_and_dirty = true]
  theories
    TSPS   
    


session "TStream" (canFail) = "Streams" + 
  options [quick_and_dirty = false]
  theories
    TStream   
    fixrec_tstream
 
session "TSPS" (canFail) = "TStream" + 
  options [quick_and_dirty = false]
  theories
    TSPS   
    

