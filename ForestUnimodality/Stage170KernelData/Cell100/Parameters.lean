import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (82)
  A := (-64190605082309708627974487 / 100000000000000000000000000)
  B := (41614402545679191058880519 / 1000000000000000000000000000)
  C := (-3342622369550189015408037 / 25000000000000000000000000)
  dδ := (13222357286067671841567339 / 500000000000000000000000000)
  dM := (29149271937683546513167543 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(95081473100478763882392741 / 10000000000000000000000000), (26134251474217339961114703 / 1000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (67 / 153)
  hi := (4 / 9)
  vmin := (5762 / 23409)
  damping := (5762 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell100
