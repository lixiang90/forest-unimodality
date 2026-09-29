import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 17
  A := (23189368165237827792424241/250000000000000000000000000)
  B := (3808697008213954293687209/200000000000000000000000000)
  C := (-25854356151018907661320867/1000000000000000000000000000)
  dδ := (19056740845421513141921821/1000000000000000000000000000)
  dM := (6996796943158218576221813/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(67770953172327963454080191/100000000000000000000000000), (19922162791134727655162351/5000000000000000000000000)]
  retention := ![(1/2), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37/140)
  hi := (19/70)
  vmin := (3811/19600)
  damping := (381100000000000000000000000000000000000000/4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell002
