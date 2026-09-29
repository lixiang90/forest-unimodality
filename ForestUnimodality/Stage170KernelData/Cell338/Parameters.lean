import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell338
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (25)
  A := (11454227810551584068043951 / 250000000000000000000000000)
  B := (3408944299321964473137303 / 250000000000000000000000000)
  C := (507516052891791944606803 / 25000000000000000000000000)
  dδ := (543475525340451209865833 / 50000000000000000000000000)
  dM := (39226461541325998143986409 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(31309917322235500947158471 / 5000000000000000000000000), (9628751086247726576061723 / 5000000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (35 / 52)
  hi := (53 / 78)
  vmin := (1325 / 6084)
  damping := (13250000000000000000000000000000000000000000 / 150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell338
