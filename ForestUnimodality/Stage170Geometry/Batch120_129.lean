import ForestUnimodality.Stage170Geometry.Data

namespace ForestUnimodality.Stage170Geometry
open FiniteRectangleCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem strip120_checked : (strip 120).check rectangle = true := by decide +kernel
theorem source120_checked : (strip 120).sourceCheck (window 120) 170 = true := by decide +kernel
#print axioms strip120_checked
#print axioms source120_checked

theorem strip121_checked : (strip 121).check rectangle = true := by decide +kernel
theorem source121_checked : (strip 121).sourceCheck (window 121) 170 = true := by decide +kernel
#print axioms strip121_checked
#print axioms source121_checked

theorem strip122_checked : (strip 122).check rectangle = true := by decide +kernel
theorem source122_checked : (strip 122).sourceCheck (window 122) 170 = true := by decide +kernel
#print axioms strip122_checked
#print axioms source122_checked

theorem strip123_checked : (strip 123).check rectangle = true := by decide +kernel
theorem source123_checked : (strip 123).sourceCheck (window 123) 170 = true := by decide +kernel
#print axioms strip123_checked
#print axioms source123_checked

theorem strip124_checked : (strip 124).check rectangle = true := by decide +kernel
theorem source124_checked : (strip 124).sourceCheck (window 124) 170 = true := by decide +kernel
#print axioms strip124_checked
#print axioms source124_checked

theorem strip125_checked : (strip 125).check rectangle = true := by decide +kernel
theorem source125_checked : (strip 125).sourceCheck (window 125) 170 = true := by decide +kernel
#print axioms strip125_checked
#print axioms source125_checked

theorem strip126_checked : (strip 126).check rectangle = true := by decide +kernel
theorem source126_checked : (strip 126).sourceCheck (window 126) 170 = true := by decide +kernel
#print axioms strip126_checked
#print axioms source126_checked

theorem strip127_checked : (strip 127).check rectangle = true := by decide +kernel
theorem source127_checked : (strip 127).sourceCheck (window 127) 170 = true := by decide +kernel
#print axioms strip127_checked
#print axioms source127_checked

theorem strip128_checked : (strip 128).check rectangle = true := by decide +kernel
theorem source128_checked : (strip 128).sourceCheck (window 128) 170 = true := by decide +kernel
#print axioms strip128_checked
#print axioms source128_checked

theorem strip129_checked : (strip 129).check rectangle = true := by decide +kernel
theorem source129_checked : (strip 129).sourceCheck (window 129) 170 = true := by decide +kernel
#print axioms strip129_checked
#print axioms source129_checked

end ForestUnimodality.Stage170Geometry
