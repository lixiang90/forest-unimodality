import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell381
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (107)
  A := (-8763605403051471737185807 / 5000000000000000000000000)
  B := (9250784333228645461844053 / 100000000000000000000000000)
  C := (-4839289060553379241691463 / 2000000000000000000000000000)
  dδ := (13851948251844660789378061 / 250000000000000000000000000)
  dM := (86912614523152191721433457 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(10776914632636662716436149 / 1000000000000000000000000), (2360434653456898246304263 / 25000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23 / 48)
  hi := (47 / 97)
  vmin := (575 / 2304)
  damping := (575 / 2304)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell381
