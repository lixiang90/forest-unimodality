import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell517
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (100)
  A := (-20885090731926462714795889 / 10000000000000000000000000)
  B := (1103196283711299491292479 / 10000000000000000000000000)
  C := (10900944215078520616729607 / 2500000000000000000000000000)
  dδ := (14670250508896419058824101 / 250000000000000000000000000)
  dM := (10843790751041235565638177 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(53350460595893745008311271 / 10000000000000000000000000), (46261067121434201965257671 / 500000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (23607 / 44732)
  hi := (28 / 53)
  vmin := (700 / 2809)
  damping := (700 / 2809)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell517
