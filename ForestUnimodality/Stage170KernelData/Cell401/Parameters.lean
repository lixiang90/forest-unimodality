import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell401
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (85)
  A := (-5842905152312657063262691 / 5000000000000000000000000)
  B := (3679520576926638419923421 / 50000000000000000000000000)
  C := (19404271255871610724064169 / 100000000000000000000000000)
  dδ := (39023291377444709049360227 / 1000000000000000000000000000)
  dM := (64914668701313959619375593 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(43469783552881962052083509 / 5000000000000000000000000), (14053326723018084720706611 / 500000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49 / 89)
  hi := (99 / 179)
  vmin := (7920 / 32041)
  damping := (7920 / 32041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell401
