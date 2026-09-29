import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (67)
  A := (-124716928169725138531021 / 10000000000000000000000000)
  B := (16964401464776537181711191 / 1000000000000000000000000000)
  C := (-63046164852472316719733669 / 1000000000000000000000000000)
  dδ := (378074427739676045476247 / 25000000000000000000000000)
  dM := (42467070769191903468597199 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(18150222950596489823738011 / 500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7 / 17)
  hi := (64 / 153)
  vmin := (70 / 289)
  damping := (70 / 289)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell086
