import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (31)
  A := (8561103325542987974472453 / 50000000000000000000000000)
  B := (20568177071160712726660691 / 2500000000000000000000000000)
  C := (-14800552590041125139430633 / 1000000000000000000000000000)
  dδ := (88707367812130236833789709 / 10000000000000000000000000000)
  dM := (584793497034084703276903 / 20000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(6876931007147757668462873 / 200000000000000000000000)]
  retention := ![(3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37 / 126)
  hi := (19 / 63)
  vmin := (3293 / 15876)
  damping := (32930000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell027
