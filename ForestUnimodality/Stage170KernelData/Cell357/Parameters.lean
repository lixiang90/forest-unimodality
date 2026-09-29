import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell357
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (27)
  A := (6504058263755680358464417 / 50000000000000000000000000)
  B := (2713237105244128283265681 / 200000000000000000000000000)
  C := (-6058463944502471935915633 / 250000000000000000000000000)
  dδ := (20904284333576845589589 / 1562500000000000000000000)
  dM := (36908517274174502877538001 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(9303768962305364320641843 / 5000000000000000000000000), (34015766732455570142690249 / 5000000000000000000000000)]
  retention := ![(3 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13 / 42)
  hi := (20 / 63)
  vmin := (377 / 1764)
  damping := (3770000000000000000000000000000000000000000 / 43524955408804071509263948678105342569819369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell357
