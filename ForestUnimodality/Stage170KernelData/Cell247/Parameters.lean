import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell247
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (85)
  A := (-37163482741605423752773163 / 100000000000000000000000000)
  B := (13577864820937264600519967 / 500000000000000000000000000)
  C := (24593144025079040349002213 / 250000000000000000000000000)
  dδ := (19290291583093671645698919 / 1000000000000000000000000000)
  dM := (15193127698882733433646819 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(676740206047696357671839 / 62500000000000000000000), (13025009383295754972209579 / 500000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (116 / 207)
  hi := (13 / 23)
  vmin := (130 / 529)
  damping := (130 / 529)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell247
