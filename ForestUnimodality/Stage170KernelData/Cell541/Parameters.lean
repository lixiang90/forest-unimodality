import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell541
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (48)
  A := (-1974713581560414614699539 / 4000000000000000000000000)
  B := (49087359659529497535324083 / 1000000000000000000000000000)
  C := (1057892932827143445129181 / 10000000000000000000000000)
  dδ := (14436486000888728437052677 / 500000000000000000000000000)
  dM := (2277370292839561380111163 / 5000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(7015685143752516950144127 / 500000000000000000000000), (5340299051820364795162277 / 1000000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7 / 12)
  hi := (53 / 90)
  vmin := (1961 / 8100)
  damping := (1961 / 8100)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell541
