import ForestUnimodality.Stage170Geometry.Data

namespace ForestUnimodality.Stage170Geometry
open FiniteRectangleCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem strip000_checked : (strip 0).check rectangle = true := by decide +kernel
theorem source000_checked : (strip 0).sourceCheck (window 0) 170 = true := by decide +kernel
#print axioms strip000_checked
#print axioms source000_checked

theorem strip001_checked : (strip 1).check rectangle = true := by decide +kernel
theorem source001_checked : (strip 1).sourceCheck (window 1) 170 = true := by decide +kernel
#print axioms strip001_checked
#print axioms source001_checked

theorem strip002_checked : (strip 2).check rectangle = true := by decide +kernel
theorem source002_checked : (strip 2).sourceCheck (window 2) 170 = true := by decide +kernel
#print axioms strip002_checked
#print axioms source002_checked

theorem strip003_checked : (strip 3).check rectangle = true := by decide +kernel
theorem source003_checked : (strip 3).sourceCheck (window 3) 170 = true := by decide +kernel
#print axioms strip003_checked
#print axioms source003_checked

theorem strip004_checked : (strip 4).check rectangle = true := by decide +kernel
theorem source004_checked : (strip 4).sourceCheck (window 4) 170 = true := by decide +kernel
#print axioms strip004_checked
#print axioms source004_checked

theorem strip005_checked : (strip 5).check rectangle = true := by decide +kernel
theorem source005_checked : (strip 5).sourceCheck (window 5) 170 = true := by decide +kernel
#print axioms strip005_checked
#print axioms source005_checked

theorem strip006_checked : (strip 6).check rectangle = true := by decide +kernel
theorem source006_checked : (strip 6).sourceCheck (window 6) 170 = true := by decide +kernel
#print axioms strip006_checked
#print axioms source006_checked

theorem strip007_checked : (strip 7).check rectangle = true := by decide +kernel
theorem source007_checked : (strip 7).sourceCheck (window 7) 170 = true := by decide +kernel
#print axioms strip007_checked
#print axioms source007_checked

theorem strip008_checked : (strip 8).check rectangle = true := by decide +kernel
theorem source008_checked : (strip 8).sourceCheck (window 8) 170 = true := by decide +kernel
#print axioms strip008_checked
#print axioms source008_checked

theorem strip009_checked : (strip 9).check rectangle = true := by decide +kernel
theorem source009_checked : (strip 9).sourceCheck (window 9) 170 = true := by decide +kernel
#print axioms strip009_checked
#print axioms source009_checked

end ForestUnimodality.Stage170Geometry
