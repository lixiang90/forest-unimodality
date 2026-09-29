import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell522
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (100)
  A := (-10117009610577018757737733 / 5000000000000000000000000)
  B := (10846599576361477812458389 / 100000000000000000000000000)
  C := (42606242519207145058590669 / 10000000000000000000000000000)
  dδ := (5882337440214076285105449 / 100000000000000000000000000)
  dM := (2146026983520975262020869 / 2000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(37645595345310951529427257 / 5000000000000000000000000), (90392926258672190442666761 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (113 / 213)
  hi := (8069 / 15194)
  vmin := (57491625 / 230857636)
  damping := (57491625 / 230857636)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell522
