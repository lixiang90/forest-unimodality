import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (142)
  A := (-83338934960927118055451501 / 100000000000000000000000000)
  B := (20127455809991211949094847 / 500000000000000000000000000)
  C := (-19416039064070275688145273 / 100000000000000000000000000)
  dδ := (29924531830222148715003883 / 1000000000000000000000000000)
  dM := (180206377050313687772083 / 781250000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(6033337657992086100477991 / 500000000000000000000000), (26365762293388190329324061 / 500000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (17 / 37)
  hi := (1613 / 3478)
  vmin := (340 / 1369)
  damping := (340 / 1369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell116
