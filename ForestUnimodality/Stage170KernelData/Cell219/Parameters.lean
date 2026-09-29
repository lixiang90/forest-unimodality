import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell219
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (125)
  A := (-41402961911176585696026109 / 50000000000000000000000000)
  B := (39911507079444318024652461 / 1000000000000000000000000000)
  C := (16599134283482869234305213 / 100000000000000000000000000)
  dδ := (26875728320346153887854257 / 1000000000000000000000000000)
  dM := (4599937192485098838047597 / 20000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(3138768491625106804576717 / 200000000000000000000000), (40629517326771846796873433 / 1000000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (643 / 1188)
  hi := (6 / 11)
  vmin := (30 / 121)
  damping := (30 / 121)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell219
