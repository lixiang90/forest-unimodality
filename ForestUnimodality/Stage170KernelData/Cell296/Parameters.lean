import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell296
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (47)
  A := (-16266701209180409957610891 / 200000000000000000000000000)
  B := (9388847120957406061636519 / 500000000000000000000000000)
  C := (22287355461187419863877679 / 500000000000000000000000000)
  dδ := (337496811064072303743 / 25000000000000000000000)
  dM := (5201744429195173983170031 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(10021295191866927964952083 / 10000000000000000000000000), (8690319939543595495479167 / 500000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (123 / 203)
  hi := (63 / 103)
  vmin := (2520 / 10609)
  damping := (2520 / 10609)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell296
