import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (72)
  A := (-2432201457268488603347123 / 25000000000000000000000000)
  B := (4684941752075603808858073 / 250000000000000000000000000)
  C := (-34760216756788336889272273 / 500000000000000000000000000)
  dδ := (15627684781409217906755771 / 1000000000000000000000000000)
  dM := (11836107568494410151598191 / 125000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(3638373510362434615217353 / 100000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (64 / 153)
  hi := (65 / 153)
  vmin := (5696 / 23409)
  damping := (5696 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell090
