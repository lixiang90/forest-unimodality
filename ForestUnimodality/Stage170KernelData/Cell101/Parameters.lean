import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (88)
  A := (-1207854621402296138015231 / 2000000000000000000000000)
  B := (4332235108344013700676367 / 125000000000000000000000000)
  C := (-2869842876711740237150039 / 25000000000000000000000000)
  dδ := (21758733872828846245273127 / 1000000000000000000000000000)
  dM := (10473127059826045745678791 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(7595993942470545157163997 / 500000000000000000000000), (1448665841658077768627777 / 62500000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (67 / 153)
  hi := (4 / 9)
  vmin := (5762 / 23409)
  damping := (5762 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell101
