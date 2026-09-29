import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell234
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (111)
  A := (-30080574509559528994628863 / 50000000000000000000000000)
  B := (28792032731210701751445313 / 1000000000000000000000000000)
  C := (10814962293840565954461397 / 100000000000000000000000000)
  dδ := (1146519428409797361143041 / 62500000000000000000000000)
  dM := (14085784412181458517474009 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(8682302910027358322508917 / 500000000000000000000000), (1987183700337458391871337 / 62500000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49 / 89)
  hi := (99 / 179)
  vmin := (7920 / 32041)
  damping := (7920 / 32041)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell234
