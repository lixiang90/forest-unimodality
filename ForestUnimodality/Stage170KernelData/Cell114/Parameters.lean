import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (124)
  A := (-14320289617627163691793157 / 10000000000000000000000000)
  B := (14690743741899164875874817 / 200000000000000000000000000)
  C := (-12915869021560322238428853 / 50000000000000000000000000)
  dδ := (11015361211003731403690331 / 250000000000000000000000000)
  dM := (56457666483462822393929459 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(14857160629267561091637617 / 1000000000000000000000000), (40916204665925661743131059 / 1000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
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
end ForestUnimodality.Stage170KernelData.Cell114
