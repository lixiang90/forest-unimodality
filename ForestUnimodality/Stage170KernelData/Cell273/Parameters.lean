import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell273
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (56)
  A := (-26731274693244721051499369 / 100000000000000000000000000)
  B := (8080289179481902478441313 / 250000000000000000000000000)
  C := (91043662732351773869687861 / 1000000000000000000000000000)
  dδ := (11370991943226761017315951 / 500000000000000000000000000)
  dM := (5996443009218733913127941 / 25000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(28104040049149081603729883 / 10000000000000000000000000), (10195033942610891131153039 / 500000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (653 / 1128)
  hi := (7 / 12)
  vmin := (35 / 144)
  damping := (35 / 144)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell273
