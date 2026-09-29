import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell202
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (283)
  A := (-18595204341836605765792001 / 10000000000000000000000000)
  B := (49136656445472881582503533 / 1000000000000000000000000000)
  C := (20775463414139353109100217 / 10000000000000000000000000000)
  dδ := (7114152097050427912827697 / 250000000000000000000000000)
  dM := (23598968924837943322153633 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(31819081523970762503950027 / 500000000000000000000000), (21747594745582804875994043 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (28 / 53)
  hi := (113 / 213)
  vmin := (11300 / 45369)
  damping := (11300 / 45369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell202
