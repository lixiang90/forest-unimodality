import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell263
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (83)
  A := (-4564858605739617680541187 / 20000000000000000000000000)
  B := (10025768826941630629256963 / 500000000000000000000000000)
  C := (1379215154919660180077301 / 20000000000000000000000000)
  dδ := (285773142560963137881469 / 20000000000000000000000000)
  dM := (11663212763695276211672533 / 125000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(19124023060515288108263121 / 1000000000000000000000000), (406585483137662162533843 / 25000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 93)
  hi := (107 / 187)
  vmin := (8560 / 34969)
  damping := (8560 / 34969)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell263
