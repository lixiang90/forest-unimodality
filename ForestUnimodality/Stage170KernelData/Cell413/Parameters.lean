import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell413
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (44)
  A := (-4933716938553597580519039 / 25000000000000000000000000)
  B := (34100473343596421349488423 / 1000000000000000000000000000)
  C := (41568317348462814619924899 / 500000000000000000000000000)
  dδ := (24481775832534011239083327 / 1000000000000000000000000000)
  dM := (28620618900032808711725307 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(9078400421427969269050351 / 25000000000000000000000000), (27802163799596408821912519 / 5000000000000000000000000), (11615918579596435478151761 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 180)
  hi := (3 / 5)
  vmin := (6 / 25)
  damping := (6 / 25)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell413
