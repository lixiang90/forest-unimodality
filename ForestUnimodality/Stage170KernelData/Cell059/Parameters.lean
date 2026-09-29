import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (39)
  A := (17883728243062092412074549 / 100000000000000000000000000)
  B := (420447415176837199519283 / 31250000000000000000000000)
  C := (-38678743115485088310823159 / 1000000000000000000000000000)
  dδ := (17769526458707900554157 / 1250000000000000000000000)
  dM := (14858650348576710620990271 / 200000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(21903125611071505574045659 / 5000000000000000000000000), (2568684890159966371925293 / 250000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31 / 85)
  hi := (19 / 51)
  vmin := (1674 / 7225)
  damping := (1674 / 7225)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell059
