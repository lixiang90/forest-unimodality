import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell510
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-22973224535372750898432059 / 10000000000000000000000000)
  B := (11810710907074083164669531 / 100000000000000000000000000)
  C := (7152048885110703739520499 / 2000000000000000000000000000)
  dδ := (57198110849567523894521059 / 1000000000000000000000000000)
  dM := (2321431736342911226339547 / 2000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(18971549907957117042656137 / 10000000000000000000000000), (96751910469259996716573369 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11 / 21)
  hi := (1549 / 2954)
  vmin := (2176345 / 8726116)
  damping := (2176345 / 8726116)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell510
