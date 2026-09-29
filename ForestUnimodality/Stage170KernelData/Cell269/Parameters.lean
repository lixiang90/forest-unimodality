import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell269
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (60)
  A := (-32163744188178088444729497 / 100000000000000000000000000)
  B := (17320094033552720785840151 / 500000000000000000000000000)
  C := (99635525501199098674653953 / 1000000000000000000000000000)
  dδ := (4774018561043861380577269 / 200000000000000000000000000)
  dM := (25930854541778876462196357 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(15402825702412050734579907 / 5000000000000000000000000), (2200621669294640625480497 / 100000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27 / 47)
  hi := (653 / 1128)
  vmin := (310175 / 1272384)
  damping := (310175 / 1272384)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell269
