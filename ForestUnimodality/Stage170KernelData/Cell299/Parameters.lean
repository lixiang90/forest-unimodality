import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell299
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (39)
  A := (-36272154209988866035985211 / 5000000000000000000000000000)
  B := (1581849221723308955914189 / 62500000000000000000000000)
  C := (63347368385409677515873739 / 1000000000000000000000000000)
  dδ := (85208876928032625808207 / 4000000000000000000000000)
  dM := (1936177141398920918419907 / 10000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(15053737049501750178137627 / 1000000000000000000000000)]
  retention := ![(7 / 10)]
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
end ForestUnimodality.Stage170KernelData.Cell299
