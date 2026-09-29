import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell281
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (49)
  A := (-81736463877473784078731 / 625000000000000000000000)
  B := (26996394539387132127661317 / 1000000000000000000000000000)
  C := (189670041642534398240727 / 2500000000000000000000000)
  dδ := (20689456007908856027821543 / 1000000000000000000000000000)
  dM := (2457792481037218519841249 / 12500000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(28502362979117115138194549 / 10000000000000000000000000), (17066882331663855154602061 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 90)
  hi := (107 / 180)
  vmin := (7811 / 32400)
  damping := (7811 / 32400)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell281
