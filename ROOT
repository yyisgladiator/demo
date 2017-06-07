session "Streams" (mustWork) = "HOLCF" +
  options [quick_and_dirty = false]
  theories
    Streams

session "TStreamSorry" (mustWork) = "Streams" + 
  options [quick_and_dirty = true]
  theories
    TStream   
    "CaseStudies/TimedABP"
 
 
session "TSPSSorry" (mustWork) = "TStreamSorry" + 
  options [quick_and_dirty = true]
  theories
    TSPS   
    


session "TStream" (canFail) = "Streams" + 
  options [quick_and_dirty = false]
  theories
    TStream   
 
session "TSPS" (canFail) = "TStream" + 
  options [quick_and_dirty = false]
  theories
    TSPS   
    

