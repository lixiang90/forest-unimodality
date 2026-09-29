import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell303
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (50)
  A := (19587164686701196156803917 / 1000000000000000000000000000)
  B := (885707604361250940526451 / 62500000000000000000000000)
  C := (4508074766780443762281827 / 125000000000000000000000000)
  dδ := (2259604851087460355985037 / 200000000000000000000000000)
  dM := (4097322807723615981589059 / 62500000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(61520021659014085813055317 / 10000000000000000000000000), (6618854052275477073408183 / 500000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell303
