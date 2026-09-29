import ForestUnimodality.Stage170Geometry.Data

namespace ForestUnimodality.Stage170Geometry
open FiniteRectangleCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem strip020_checked : (strip 20).check rectangle = true := by decide +kernel
theorem source020_checked : (strip 20).sourceCheck (window 20) 170 = true := by decide +kernel
#print axioms strip020_checked
#print axioms source020_checked

theorem strip021_checked : (strip 21).check rectangle = true := by decide +kernel
theorem source021_checked : (strip 21).sourceCheck (window 21) 170 = true := by decide +kernel
#print axioms strip021_checked
#print axioms source021_checked

theorem strip022_checked : (strip 22).check rectangle = true := by decide +kernel
theorem source022_checked : (strip 22).sourceCheck (window 22) 170 = true := by decide +kernel
#print axioms strip022_checked
#print axioms source022_checked

theorem strip023_checked : (strip 23).check rectangle = true := by decide +kernel
theorem source023_checked : (strip 23).sourceCheck (window 23) 170 = true := by decide +kernel
#print axioms strip023_checked
#print axioms source023_checked

theorem strip024_checked : (strip 24).check rectangle = true := by decide +kernel
theorem source024_checked : (strip 24).sourceCheck (window 24) 170 = true := by decide +kernel
#print axioms strip024_checked
#print axioms source024_checked

theorem strip025_checked : (strip 25).check rectangle = true := by decide +kernel
theorem source025_checked : (strip 25).sourceCheck (window 25) 170 = true := by decide +kernel
#print axioms strip025_checked
#print axioms source025_checked

theorem strip026_checked : (strip 26).check rectangle = true := by decide +kernel
theorem source026_checked : (strip 26).sourceCheck (window 26) 170 = true := by decide +kernel
#print axioms strip026_checked
#print axioms source026_checked

theorem strip027_checked : (strip 27).check rectangle = true := by decide +kernel
theorem source027_checked : (strip 27).sourceCheck (window 27) 170 = true := by decide +kernel
#print axioms strip027_checked
#print axioms source027_checked

theorem strip028_checked : (strip 28).check rectangle = true := by decide +kernel
theorem source028_checked : (strip 28).sourceCheck (window 28) 170 = true := by decide +kernel
#print axioms strip028_checked
#print axioms source028_checked

theorem strip029_checked : (strip 29).check rectangle = true := by decide +kernel
theorem source029_checked : (strip 29).sourceCheck (window 29) 170 = true := by decide +kernel
#print axioms strip029_checked
#print axioms source029_checked

end ForestUnimodality.Stage170Geometry
