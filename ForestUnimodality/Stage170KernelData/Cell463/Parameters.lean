import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell463
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (97)
  A := (-22616254138361164172010831 / 10000000000000000000000000)
  B := (2405753330719024307704501 / 20000000000000000000000000)
  C := (-34770466458625246160274447 / 10000000000000000000000000000)
  dδ := (58774412642589909938628523 / 1000000000000000000000000000)
  dM := (2438089441374732390527269 / 2000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(38440551544154475394066139 / 10000000000000000000000000), (9083903206575170941050601 / 100000000000000000000000)]
  retention := ![(3 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1733 / 3648)
  hi := (869 / 1824)
  vmin := (3318695 / 13307904)
  damping := (3318695 / 13307904)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell463
