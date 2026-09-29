import ForestUnimodality.Stage170Geometry.Data

namespace ForestUnimodality.Stage170Geometry
open FiniteRectangleCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem strip110_checked : (strip 110).check rectangle = true := by decide +kernel
theorem source110_checked : (strip 110).sourceCheck (window 110) 170 = true := by decide +kernel
#print axioms strip110_checked
#print axioms source110_checked

theorem strip111_checked : (strip 111).check rectangle = true := by decide +kernel
theorem source111_checked : (strip 111).sourceCheck (window 111) 170 = true := by decide +kernel
#print axioms strip111_checked
#print axioms source111_checked

theorem strip112_checked : (strip 112).check rectangle = true := by decide +kernel
theorem source112_checked : (strip 112).sourceCheck (window 112) 170 = true := by decide +kernel
#print axioms strip112_checked
#print axioms source112_checked

theorem strip113_checked : (strip 113).check rectangle = true := by decide +kernel
theorem source113_checked : (strip 113).sourceCheck (window 113) 170 = true := by decide +kernel
#print axioms strip113_checked
#print axioms source113_checked

theorem strip114_checked : (strip 114).check rectangle = true := by decide +kernel
theorem source114_checked : (strip 114).sourceCheck (window 114) 170 = true := by decide +kernel
#print axioms strip114_checked
#print axioms source114_checked

theorem strip115_checked : (strip 115).check rectangle = true := by decide +kernel
theorem source115_checked : (strip 115).sourceCheck (window 115) 170 = true := by decide +kernel
#print axioms strip115_checked
#print axioms source115_checked

theorem strip116_checked : (strip 116).check rectangle = true := by decide +kernel
theorem source116_checked : (strip 116).sourceCheck (window 116) 170 = true := by decide +kernel
#print axioms strip116_checked
#print axioms source116_checked

theorem strip117_checked : (strip 117).check rectangle = true := by decide +kernel
theorem source117_checked : (strip 117).sourceCheck (window 117) 170 = true := by decide +kernel
#print axioms strip117_checked
#print axioms source117_checked

theorem strip118_checked : (strip 118).check rectangle = true := by decide +kernel
theorem source118_checked : (strip 118).sourceCheck (window 118) 170 = true := by decide +kernel
#print axioms strip118_checked
#print axioms source118_checked

theorem strip119_checked : (strip 119).check rectangle = true := by decide +kernel
theorem source119_checked : (strip 119).sourceCheck (window 119) 170 = true := by decide +kernel
#print axioms strip119_checked
#print axioms source119_checked

end ForestUnimodality.Stage170Geometry
