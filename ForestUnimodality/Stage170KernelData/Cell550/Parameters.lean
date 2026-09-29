import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell550
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (28)
  A := (12271110412018683023305243 / 100000000000000000000000000)
  B := (1114036442068018495366033 / 50000000000000000000000000)
  C := (53717221857754640645943311 / 1000000000000000000000000000)
  dδ := (22330270208147758731476173 / 1000000000000000000000000000)
  dM := (19210350195434327093615967 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(1637656457173968931329 / 160000000000000000000)]
  retention := ![(7 / 10)]
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
end ForestUnimodality.Stage170KernelData.Cell550
