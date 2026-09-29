import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell342
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (24)
  A := (36227370504513199964691239 / 1000000000000000000000000000)
  B := (13836497577587463653214783 / 1000000000000000000000000000)
  C := (118475594596459377592923 / 6250000000000000000000000)
  dδ := (2143979702962117706022127 / 200000000000000000000000000)
  dM := (40297434150830998818380163 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(19088566424990229819513843 / 5000000000000000000000000), (9702889460409788169314993 / 2500000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 78)
  hi := (107 / 156)
  vmin := (5243 / 24336)
  damping := (13107500000000000000000000000000000000000000 / 150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell342
