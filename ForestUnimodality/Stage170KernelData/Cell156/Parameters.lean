import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (265)
  A := (-8659890925525885690916539 / 5000000000000000000000000)
  B := (48027837974153220201856129 / 1000000000000000000000000000)
  C := (3628447672948985954638479 / 20000000000000000000000000000)
  dδ := (28807321529902965573377571 / 1000000000000000000000000000)
  dM := (477888610820606648740827 / 2000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(40364531870391040513368353 / 1000000000000000000000000), (22287487404535755786127993 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1 / 2)
  hi := (51 / 101)
  vmin := (2550 / 10201)
  damping := (2550 / 10201)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell156
