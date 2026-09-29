import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell361
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (32)
  A := (16386335367415672982005503 / 100000000000000000000000000)
  B := (7802985519609772005478199 / 500000000000000000000000000)
  C := (-36688314809215243073037271 / 1000000000000000000000000000)
  dδ := (16333476874789459171166683 / 1000000000000000000000000000)
  dM := (96954300625926462882560319 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(97322896649136081403952403 / 100000000000000000000000000), (1030625004647918174782717 / 100000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29 / 85)
  hi := (89 / 255)
  vmin := (1624 / 7225)
  damping := (2598400000000000000000000000000000000000000 / 28523156719148246408565263419438648532149201)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell361
