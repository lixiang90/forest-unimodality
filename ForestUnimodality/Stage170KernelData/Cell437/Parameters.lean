import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell437
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (27)
  A := (10395692135708224258294763 / 100000000000000000000000000)
  B := (4115712011221741954691833 / 250000000000000000000000000)
  C := (-5762422533671187480086573 / 200000000000000000000000000)
  dδ := (15335267598228294674833627 / 1000000000000000000000000000)
  dM := (320511591764976072919599 / 3125000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(23266121750253350164427957 / 5000000000000000000000000), (41923094767541142502409457 / 10000000000000000000000000)]
  retention := ![(9 / 20), (2 / 5)]
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
end ForestUnimodality.Stage170KernelData.Cell437
