import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell268
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (80)
  A := (-10215099145243991040743481 / 50000000000000000000000000)
  B := (19335645426104046407100867 / 1000000000000000000000000000)
  C := (65256272014074134801830951 / 1000000000000000000000000000)
  dδ := (13823557230758778610613113 / 1000000000000000000000000000)
  dM := (223750520593165321112019 / 2500000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(18450877500696314825745503 / 1000000000000000000000000), (15490349617635253309799737 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 187)
  hi := (27 / 47)
  vmin := (540 / 2209)
  damping := (540 / 2209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell268
