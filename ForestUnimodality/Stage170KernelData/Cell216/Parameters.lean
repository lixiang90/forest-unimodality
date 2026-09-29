import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell216
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (148)
  A := (-10427855557106264117095407 / 10000000000000000000000000)
  B := (38959855039615187699553189 / 1000000000000000000000000000)
  C := (16206161455475720511998361 / 100000000000000000000000000)
  dδ := (23868592847755984442947863 / 1000000000000000000000000000)
  dM := (1961790994112199446128969 / 10000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(5822352849246164474550369 / 250000000000000000000000), (44000401358420717201624939 / 1000000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29 / 54)
  hi := (643 / 1188)
  vmin := (350435 / 1411344)
  damping := (350435 / 1411344)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell216
