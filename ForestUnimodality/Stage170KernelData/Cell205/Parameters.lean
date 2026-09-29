import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell205
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (206)
  A := (-17846952030355024876229209 / 10000000000000000000000000)
  B := (29169800238165184691485621 / 500000000000000000000000000)
  C := (3512677060189901205415619 / 1250000000000000000000000000)
  dδ := (34463308559853501888969873 / 1000000000000000000000000000)
  dM := (34350884258050668655995463 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(10506271209534329358348259 / 500000000000000000000000), (1831711192109842158970423 / 10000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (113 / 213)
  hi := (57 / 107)
  vmin := (2850 / 11449)
  damping := (2850 / 11449)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell205
