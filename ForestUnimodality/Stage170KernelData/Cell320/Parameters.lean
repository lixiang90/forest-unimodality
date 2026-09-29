import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell320
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (38)
  A := (77153108400437219192014027 / 1000000000000000000000000000)
  B := (118517008435271783972631 / 10000000000000000000000000)
  C := (25641165537406571117706733 / 1000000000000000000000000000)
  dδ := (19959681449494438149061537 / 2000000000000000000000000000)
  dM := (6845788256124974971623693 / 125000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(8010756991310215013868401 / 2000000000000000000000000), (98636568679387011115977657 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (236 / 371)
  hi := (9 / 14)
  vmin := (45 / 196)
  damping := (45 / 196)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell320
