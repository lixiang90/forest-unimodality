import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (28)
  A := (1946796050330577968034973 / 12500000000000000000000000)
  B := (99069790468709981873240977 / 10000000000000000000000000000)
  C := (-513128513590300669965083 / 31250000000000000000000000)
  dδ := (10414309421120067702948297 / 1000000000000000000000000000)
  dM := (40237579442296683154226683 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(25039286071176750425593127 / 500000000000000000000000)]
  retention := ![(1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2 / 7)
  hi := (37 / 126)
  vmin := (10 / 49)
  damping := (400000000000000000000000000000000000000000 / 4836106156533785723251549853122815841091041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell022
