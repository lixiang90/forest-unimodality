import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell326
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (30)
  A := (53134450832629530623307801 / 1000000000000000000000000000)
  B := (58965000304513445761323 / 4000000000000000000000000)
  C := (27775804276476585841226807 / 1000000000000000000000000000)
  dδ := (6204974714759422041443493 / 500000000000000000000000000)
  dM := (8675287810912908278981881 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(12007430688615421121578919 / 50000000000000000000000000), (2562250139886201427685819 / 250000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (41 / 63)
  hi := (83 / 126)
  vmin := (3569 / 15876)
  damping := (35690000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell326
