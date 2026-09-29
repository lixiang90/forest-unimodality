import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (193)
  A := (-7146333405757267725988413 / 5000000000000000000000000)
  B := (26236138808889541279567581 / 500000000000000000000000000)
  C := (-5424229479150003774626243 / 5000000000000000000000000000)
  dδ := (18012597289011091084010019 / 500000000000000000000000000)
  dM := (32457894169058343000755507 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(66416778297815696419093 / 4000000000000000000000), (3498632167914249180284969 / 20000000000000000000000)]
  retention := ![(4 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47 / 97)
  hi := (24 / 49)
  vmin := (2350 / 9409)
  damping := (2350 / 9409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell140
