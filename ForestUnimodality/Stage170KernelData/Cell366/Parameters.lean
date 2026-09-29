import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell366
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (41)
  A := (403544341843198135535431 / 4000000000000000000000000)
  B := (17222877127081526876795081 / 1000000000000000000000000000)
  C := (-51046825063239369135725809 / 1000000000000000000000000000)
  dδ := (668937517244921758807763 / 40000000000000000000000000)
  dM := (5452837758786471952180547 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(18753825224344766731121581 / 5000000000000000000000000), (97600062691368123068969 / 8000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97 / 255)
  hi := (33 / 85)
  vmin := (15326 / 65025)
  damping := (15326 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell366
