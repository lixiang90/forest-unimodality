import ForestUnimodality.Stage170Geometry.Data

namespace ForestUnimodality.Stage170Geometry
open FiniteRectangleCover
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem strip010_checked : (strip 10).check rectangle = true := by decide +kernel
theorem source010_checked : (strip 10).sourceCheck (window 10) 170 = true := by decide +kernel
#print axioms strip010_checked
#print axioms source010_checked

theorem strip011_checked : (strip 11).check rectangle = true := by decide +kernel
theorem source011_checked : (strip 11).sourceCheck (window 11) 170 = true := by decide +kernel
#print axioms strip011_checked
#print axioms source011_checked

theorem strip012_checked : (strip 12).check rectangle = true := by decide +kernel
theorem source012_checked : (strip 12).sourceCheck (window 12) 170 = true := by decide +kernel
#print axioms strip012_checked
#print axioms source012_checked

theorem strip013_checked : (strip 13).check rectangle = true := by decide +kernel
theorem source013_checked : (strip 13).sourceCheck (window 13) 170 = true := by decide +kernel
#print axioms strip013_checked
#print axioms source013_checked

theorem strip014_checked : (strip 14).check rectangle = true := by decide +kernel
theorem source014_checked : (strip 14).sourceCheck (window 14) 170 = true := by decide +kernel
#print axioms strip014_checked
#print axioms source014_checked

theorem strip015_checked : (strip 15).check rectangle = true := by decide +kernel
theorem source015_checked : (strip 15).sourceCheck (window 15) 170 = true := by decide +kernel
#print axioms strip015_checked
#print axioms source015_checked

theorem strip016_checked : (strip 16).check rectangle = true := by decide +kernel
theorem source016_checked : (strip 16).sourceCheck (window 16) 170 = true := by decide +kernel
#print axioms strip016_checked
#print axioms source016_checked

theorem strip017_checked : (strip 17).check rectangle = true := by decide +kernel
theorem source017_checked : (strip 17).sourceCheck (window 17) 170 = true := by decide +kernel
#print axioms strip017_checked
#print axioms source017_checked

theorem strip018_checked : (strip 18).check rectangle = true := by decide +kernel
theorem source018_checked : (strip 18).sourceCheck (window 18) 170 = true := by decide +kernel
#print axioms strip018_checked
#print axioms source018_checked

theorem strip019_checked : (strip 19).check rectangle = true := by decide +kernel
theorem source019_checked : (strip 19).sourceCheck (window 19) 170 = true := by decide +kernel
#print axioms strip019_checked
#print axioms source019_checked

end ForestUnimodality.Stage170Geometry
