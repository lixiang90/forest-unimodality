import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (63)
  A := (-402628479128115463581139 / 3125000000000000000000000)
  B := (12672817920761164645071517 / 500000000000000000000000000)
  C := (-90848092703433330763473919 / 1000000000000000000000000000)
  dδ := (2702762504607215000157483 / 125000000000000000000000000)
  dM := (16508708104364034534652927 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(10199176779573907225540097 / 1000000000000000000000000), (8162113898358873242955269 / 500000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (64 / 153)
  hi := (65 / 153)
  vmin := (5696 / 23409)
  damping := (5696 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell088
