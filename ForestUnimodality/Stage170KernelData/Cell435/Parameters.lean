import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell435
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (25)
  A := (2272454005232231932964737 / 20000000000000000000000000)
  B := (2021025453285682071252749 / 125000000000000000000000000)
  C := (-13256597606223654781110177 / 500000000000000000000000000)
  dδ := (15537491294940170005745017 / 1000000000000000000000000000)
  dM := (98380540197507714331691397 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(9722827529997705164888089 / 5000000000000000000000000), (2346044698339968803679767 / 400000000000000000000000)]
  retention := ![(1 / 2), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19 / 63)
  hi := (13 / 42)
  vmin := (836 / 3969)
  damping := (33440000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell435
