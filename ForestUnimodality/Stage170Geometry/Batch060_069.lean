import ForestUnimodality.Stage170Geometry.Data

namespace ForestUnimodality.Stage170Geometry
open FiniteRectangleCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem strip060_checked : (strip 60).check rectangle = true := by decide +kernel
theorem source060_checked : (strip 60).sourceCheck (window 60) 170 = true := by decide +kernel
#print axioms strip060_checked
#print axioms source060_checked

theorem strip061_checked : (strip 61).check rectangle = true := by decide +kernel
theorem source061_checked : (strip 61).sourceCheck (window 61) 170 = true := by decide +kernel
#print axioms strip061_checked
#print axioms source061_checked

theorem strip062_checked : (strip 62).check rectangle = true := by decide +kernel
theorem source062_checked : (strip 62).sourceCheck (window 62) 170 = true := by decide +kernel
#print axioms strip062_checked
#print axioms source062_checked

theorem strip063_checked : (strip 63).check rectangle = true := by decide +kernel
theorem source063_checked : (strip 63).sourceCheck (window 63) 170 = true := by decide +kernel
#print axioms strip063_checked
#print axioms source063_checked

theorem strip064_checked : (strip 64).check rectangle = true := by decide +kernel
theorem source064_checked : (strip 64).sourceCheck (window 64) 170 = true := by decide +kernel
#print axioms strip064_checked
#print axioms source064_checked

theorem strip065_checked : (strip 65).check rectangle = true := by decide +kernel
theorem source065_checked : (strip 65).sourceCheck (window 65) 170 = true := by decide +kernel
#print axioms strip065_checked
#print axioms source065_checked

theorem strip066_checked : (strip 66).check rectangle = true := by decide +kernel
theorem source066_checked : (strip 66).sourceCheck (window 66) 170 = true := by decide +kernel
#print axioms strip066_checked
#print axioms source066_checked

theorem strip067_checked : (strip 67).check rectangle = true := by decide +kernel
theorem source067_checked : (strip 67).sourceCheck (window 67) 170 = true := by decide +kernel
#print axioms strip067_checked
#print axioms source067_checked

theorem strip068_checked : (strip 68).check rectangle = true := by decide +kernel
theorem source068_checked : (strip 68).sourceCheck (window 68) 170 = true := by decide +kernel
#print axioms strip068_checked
#print axioms source068_checked

theorem strip069_checked : (strip 69).check rectangle = true := by decide +kernel
theorem source069_checked : (strip 69).sourceCheck (window 69) 170 = true := by decide +kernel
#print axioms strip069_checked
#print axioms source069_checked

end ForestUnimodality.Stage170Geometry
