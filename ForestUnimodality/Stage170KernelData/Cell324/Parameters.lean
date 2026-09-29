import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell324
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (36)
  A := (5314906281909952054931523 / 62500000000000000000000000)
  B := (11162415945131107242183077 / 1000000000000000000000000000)
  C := (1439508927195978999283299 / 62500000000000000000000000)
  dδ := (9473831678483573409677021 / 1000000000000000000000000000)
  dM := (50728842936612139147365547 / 1000000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(20401321143855493112084787 / 5000000000000000000000000), (44147105771842820587380629 / 5000000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell324
