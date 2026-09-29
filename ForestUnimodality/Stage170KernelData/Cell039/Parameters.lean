import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (34)
  A := (14521072324140389287805419 / 100000000000000000000000000)
  B := (86332305647750760824177263 / 10000000000000000000000000000)
  C := (-1674297617152177217181297 / 100000000000000000000000000)
  dδ := (86325438307456488218338819 / 10000000000000000000000000000)
  dM := (32382714754943249893005819 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(10097440805176416844801679 / 250000000000000000000000)]
  retention := ![(3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (20 / 63)
  hi := (41 / 126)
  vmin := (860 / 3969)
  damping := (34400000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell039
