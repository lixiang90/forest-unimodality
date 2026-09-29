import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell302
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (48)
  A := (1175204881202270638107521 / 62500000000000000000000000)
  B := (13604468802988736036985173 / 1000000000000000000000000000)
  C := (17311007104436927639401489 / 500000000000000000000000000)
  dδ := (10846103285219824488572193 / 1000000000000000000000000000)
  dM := (62934878326634233528490137 / 1000000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(59059220792654620879602589 / 10000000000000000000000000), (12708199780368804709951291 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (63 / 103)
  hi := (129 / 209)
  vmin := (10320 / 43681)
  damping := (10320 / 43681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell302
