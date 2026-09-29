import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell545
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (37)
  A := (1465158763917331552661949 / 20000000000000000000000000)
  B := (26002577371170534220601311 / 1000000000000000000000000000)
  C := (79073072786100484510285469 / 1000000000000000000000000000)
  dδ := (5215421466501525549208651 / 200000000000000000000000000)
  dM := (712193885636791709748631 / 3125000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(14549398546254641573227673 / 1000000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (123 / 203)
  hi := (63 / 103)
  vmin := (2520 / 10609)
  damping := (2520 / 10609)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell545
