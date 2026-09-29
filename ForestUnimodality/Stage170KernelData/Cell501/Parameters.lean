import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell501
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (102)
  A := (-9596157703704919167364551 / 5000000000000000000000000)
  B := (5139719707857839242626241 / 50000000000000000000000000)
  C := (28221711968671979453571197 / 10000000000000000000000000000)
  dδ := (29132160195886609710402837 / 500000000000000000000000000)
  dM := (625608036791817955554057 / 625000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(64230647998713337187837169 / 10000000000000000000000000), (93602271510192792902671499 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22331 / 43056)
  hi := (27 / 52)
  vmin := (675 / 2704)
  damping := (675 / 2704)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell501
