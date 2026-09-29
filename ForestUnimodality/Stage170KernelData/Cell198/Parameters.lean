import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell198
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (136)
  A := (-1182069979261400852887931 / 625000000000000000000000)
  B := (40870933926585389928121117 / 500000000000000000000000000)
  C := (3305705275841561326111151 / 1000000000000000000000000000)
  dδ := (1440168941056751321719287 / 31250000000000000000000000)
  dM := (6451260176973411947232151 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(17940737959174040128118577 / 500000000000000000000000), (98184442413995697052087053 / 1000000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (28 / 53)
  hi := (113 / 213)
  vmin := (11300 / 45369)
  damping := (11300 / 45369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell198
