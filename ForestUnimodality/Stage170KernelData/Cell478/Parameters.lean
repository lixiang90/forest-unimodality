import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell478
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-21184976172085003176448481 / 10000000000000000000000000)
  B := (43401095198678538242959 / 390625000000000000000000)
  C := (-13679723990566160533519091 / 25000000000000000000000000000)
  dδ := (28610545302291231356539569 / 500000000000000000000000000)
  dM := (21333297300021108380949 / 19531250000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(19185711958978546309850799 / 20000000000000000000000000), (48932776441598804240129539 / 500000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49 / 99)
  hi := (131 / 264)
  vmin := (2450 / 9801)
  damping := (2450 / 9801)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell478
