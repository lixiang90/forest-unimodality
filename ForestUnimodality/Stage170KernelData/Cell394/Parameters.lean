import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell394
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (113)
  A := (-19343003951864389711090553 / 10000000000000000000000000)
  B := (95295073634502958093150937 / 1000000000000000000000000000)
  C := (40351805404777816438377513 / 10000000000000000000000000000)
  dδ := (52882679884212122067843609 / 1000000000000000000000000000)
  dM := (21503262260092533431771189 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(16796292146882290552412087 / 1000000000000000000000000), (94220569958587546466333151 / 1000000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell394
