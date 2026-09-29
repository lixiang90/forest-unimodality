import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (31)
  A := (1519531937394149145958977 / 10000000000000000000000000)
  B := (49854083269601492597877801 / 5000000000000000000000000000)
  C := (-18606776974139260794061101 / 1000000000000000000000000000)
  dδ := (10164672497723370794830977 / 1000000000000000000000000000)
  dM := (41905503046373009524549341 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(6372182307757319641439153 / 500000000000000000000000)]
  retention := ![(3 / 5)]
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
end ForestUnimodality.Stage170KernelData.Cell034
