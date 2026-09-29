import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell262
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (80)
  A := (-10678238871936259812400749 / 50000000000000000000000000)
  B := (9800770911094313156408653 / 500000000000000000000000000)
  C := (68188737982327093933854201 / 1000000000000000000000000000)
  dδ := (14183790774047924654333031 / 1000000000000000000000000000)
  dM := (46152734067843953437351029 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(18322837709143488638119379 / 1000000000000000000000000), (3947459283799761742272949 / 250000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 93)
  hi := (107 / 187)
  vmin := (8560 / 34969)
  damping := (8560 / 34969)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell262
