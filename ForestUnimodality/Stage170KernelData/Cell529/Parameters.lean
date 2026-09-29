import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell529
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (91)
  A := (-14999709875317161389318699 / 10000000000000000000000000)
  B := (18900530137158558230403571 / 200000000000000000000000000)
  C := (24599277836525176854642893 / 100000000000000000000000000)
  dδ := (6134568477169509599644659 / 125000000000000000000000000)
  dM := (22671499721658560505543889 / 25000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(48311123376198237266976321 / 10000000000000000000000000), (17368746856151112467614439 / 500000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (6 / 11)
  hi := (97 / 177)
  vmin := (7760 / 31329)
  damping := (7760 / 31329)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell529
