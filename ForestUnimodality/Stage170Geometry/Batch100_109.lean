import ForestUnimodality.Stage170Geometry.Data

namespace ForestUnimodality.Stage170Geometry
open FiniteRectangleCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem strip100_checked : (strip 100).check rectangle = true := by decide +kernel
theorem source100_checked : (strip 100).sourceCheck (window 100) 170 = true := by decide +kernel
#print axioms strip100_checked
#print axioms source100_checked

theorem strip101_checked : (strip 101).check rectangle = true := by decide +kernel
theorem source101_checked : (strip 101).sourceCheck (window 101) 170 = true := by decide +kernel
#print axioms strip101_checked
#print axioms source101_checked

theorem strip102_checked : (strip 102).check rectangle = true := by decide +kernel
theorem source102_checked : (strip 102).sourceCheck (window 102) 170 = true := by decide +kernel
#print axioms strip102_checked
#print axioms source102_checked

theorem strip103_checked : (strip 103).check rectangle = true := by decide +kernel
theorem source103_checked : (strip 103).sourceCheck (window 103) 170 = true := by decide +kernel
#print axioms strip103_checked
#print axioms source103_checked

theorem strip104_checked : (strip 104).check rectangle = true := by decide +kernel
theorem source104_checked : (strip 104).sourceCheck (window 104) 170 = true := by decide +kernel
#print axioms strip104_checked
#print axioms source104_checked

theorem strip105_checked : (strip 105).check rectangle = true := by decide +kernel
theorem source105_checked : (strip 105).sourceCheck (window 105) 170 = true := by decide +kernel
#print axioms strip105_checked
#print axioms source105_checked

theorem strip106_checked : (strip 106).check rectangle = true := by decide +kernel
theorem source106_checked : (strip 106).sourceCheck (window 106) 170 = true := by decide +kernel
#print axioms strip106_checked
#print axioms source106_checked

theorem strip107_checked : (strip 107).check rectangle = true := by decide +kernel
theorem source107_checked : (strip 107).sourceCheck (window 107) 170 = true := by decide +kernel
#print axioms strip107_checked
#print axioms source107_checked

theorem strip108_checked : (strip 108).check rectangle = true := by decide +kernel
theorem source108_checked : (strip 108).sourceCheck (window 108) 170 = true := by decide +kernel
#print axioms strip108_checked
#print axioms source108_checked

theorem strip109_checked : (strip 109).check rectangle = true := by decide +kernel
theorem source109_checked : (strip 109).sourceCheck (window 109) 170 = true := by decide +kernel
#print axioms strip109_checked
#print axioms source109_checked

end ForestUnimodality.Stage170Geometry
