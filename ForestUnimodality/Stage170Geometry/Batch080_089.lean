import ForestUnimodality.Stage170Geometry.Data

namespace ForestUnimodality.Stage170Geometry
open FiniteRectangleCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem strip080_checked : (strip 80).check rectangle = true := by decide +kernel
theorem source080_checked : (strip 80).sourceCheck (window 80) 170 = true := by decide +kernel
#print axioms strip080_checked
#print axioms source080_checked

theorem strip081_checked : (strip 81).check rectangle = true := by decide +kernel
theorem source081_checked : (strip 81).sourceCheck (window 81) 170 = true := by decide +kernel
#print axioms strip081_checked
#print axioms source081_checked

theorem strip082_checked : (strip 82).check rectangle = true := by decide +kernel
theorem source082_checked : (strip 82).sourceCheck (window 82) 170 = true := by decide +kernel
#print axioms strip082_checked
#print axioms source082_checked

theorem strip083_checked : (strip 83).check rectangle = true := by decide +kernel
theorem source083_checked : (strip 83).sourceCheck (window 83) 170 = true := by decide +kernel
#print axioms strip083_checked
#print axioms source083_checked

theorem strip084_checked : (strip 84).check rectangle = true := by decide +kernel
theorem source084_checked : (strip 84).sourceCheck (window 84) 170 = true := by decide +kernel
#print axioms strip084_checked
#print axioms source084_checked

theorem strip085_checked : (strip 85).check rectangle = true := by decide +kernel
theorem source085_checked : (strip 85).sourceCheck (window 85) 170 = true := by decide +kernel
#print axioms strip085_checked
#print axioms source085_checked

theorem strip086_checked : (strip 86).check rectangle = true := by decide +kernel
theorem source086_checked : (strip 86).sourceCheck (window 86) 170 = true := by decide +kernel
#print axioms strip086_checked
#print axioms source086_checked

theorem strip087_checked : (strip 87).check rectangle = true := by decide +kernel
theorem source087_checked : (strip 87).sourceCheck (window 87) 170 = true := by decide +kernel
#print axioms strip087_checked
#print axioms source087_checked

theorem strip088_checked : (strip 88).check rectangle = true := by decide +kernel
theorem source088_checked : (strip 88).sourceCheck (window 88) 170 = true := by decide +kernel
#print axioms strip088_checked
#print axioms source088_checked

theorem strip089_checked : (strip 89).check rectangle = true := by decide +kernel
theorem source089_checked : (strip 89).sourceCheck (window 89) 170 = true := by decide +kernel
#print axioms strip089_checked
#print axioms source089_checked

end ForestUnimodality.Stage170Geometry
