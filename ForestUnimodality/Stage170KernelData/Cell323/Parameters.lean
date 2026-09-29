import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell323
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (34)
  A := (72710569298715231898455613 / 1000000000000000000000000000)
  B := (2557467643107341412345157 / 200000000000000000000000000)
  C := (12961367525700491498685807 / 500000000000000000000000000)
  dδ := (10753517691064548231216769 / 1000000000000000000000000000)
  dM := (16203032321567454004766773 / 250000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(4769906537892351083840481 / 2500000000000000000000000), (5135469422128267069638241 / 500000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9 / 14)
  hi := (41 / 63)
  vmin := (902 / 3969)
  damping := (902 / 3969)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell323
