import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell297
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (51)
  A := (-33981524508174033574192663 / 1000000000000000000000000000)
  B := (1501932087872069263023711 / 100000000000000000000000000)
  C := (37817189145663204774550081 / 1000000000000000000000000000)
  dδ := (5620644197412483222819901 / 500000000000000000000000000)
  dM := (17688221130690961725934543 / 250000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(4106642779092394945905653 / 1000000000000000000000000), (3977212346586625368871637 / 250000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (123 / 203)
  hi := (63 / 103)
  vmin := (2520 / 10609)
  damping := (2520 / 10609)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell297
