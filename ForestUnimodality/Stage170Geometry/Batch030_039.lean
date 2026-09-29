import ForestUnimodality.Stage170Geometry.Data

namespace ForestUnimodality.Stage170Geometry
open FiniteRectangleCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem strip030_checked : (strip 30).check rectangle = true := by decide +kernel
theorem source030_checked : (strip 30).sourceCheck (window 30) 170 = true := by decide +kernel
#print axioms strip030_checked
#print axioms source030_checked

theorem strip031_checked : (strip 31).check rectangle = true := by decide +kernel
theorem source031_checked : (strip 31).sourceCheck (window 31) 170 = true := by decide +kernel
#print axioms strip031_checked
#print axioms source031_checked

theorem strip032_checked : (strip 32).check rectangle = true := by decide +kernel
theorem source032_checked : (strip 32).sourceCheck (window 32) 170 = true := by decide +kernel
#print axioms strip032_checked
#print axioms source032_checked

theorem strip033_checked : (strip 33).check rectangle = true := by decide +kernel
theorem source033_checked : (strip 33).sourceCheck (window 33) 170 = true := by decide +kernel
#print axioms strip033_checked
#print axioms source033_checked

theorem strip034_checked : (strip 34).check rectangle = true := by decide +kernel
theorem source034_checked : (strip 34).sourceCheck (window 34) 170 = true := by decide +kernel
#print axioms strip034_checked
#print axioms source034_checked

theorem strip035_checked : (strip 35).check rectangle = true := by decide +kernel
theorem source035_checked : (strip 35).sourceCheck (window 35) 170 = true := by decide +kernel
#print axioms strip035_checked
#print axioms source035_checked

theorem strip036_checked : (strip 36).check rectangle = true := by decide +kernel
theorem source036_checked : (strip 36).sourceCheck (window 36) 170 = true := by decide +kernel
#print axioms strip036_checked
#print axioms source036_checked

theorem strip037_checked : (strip 37).check rectangle = true := by decide +kernel
theorem source037_checked : (strip 37).sourceCheck (window 37) 170 = true := by decide +kernel
#print axioms strip037_checked
#print axioms source037_checked

theorem strip038_checked : (strip 38).check rectangle = true := by decide +kernel
theorem source038_checked : (strip 38).sourceCheck (window 38) 170 = true := by decide +kernel
#print axioms strip038_checked
#print axioms source038_checked

theorem strip039_checked : (strip 39).check rectangle = true := by decide +kernel
theorem source039_checked : (strip 39).sourceCheck (window 39) 170 = true := by decide +kernel
#print axioms strip039_checked
#print axioms source039_checked

end ForestUnimodality.Stage170Geometry
