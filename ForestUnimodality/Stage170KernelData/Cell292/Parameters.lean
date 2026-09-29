import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell292
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (54)
  A := (-2463312193402094673722047 / 50000000000000000000000000)
  B := (3074801936338399793724463 / 200000000000000000000000000)
  C := (5125452368595259308725609 / 125000000000000000000000000)
  dδ := (11527252981577576149141429 / 1000000000000000000000000000)
  dM := (36216793909650206288470403 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(26172907353210557168665673 / 5000000000000000000000000), (16263631413559323846129701 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3 / 5)
  hi := (123 / 203)
  vmin := (9840 / 41209)
  damping := (9840 / 41209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell292
