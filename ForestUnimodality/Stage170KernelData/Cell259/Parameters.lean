import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell259
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (65)
  A := (-36392182775307828745070537 / 100000000000000000000000000)
  B := (4595855835303188849372269 / 125000000000000000000000000)
  C := (2216205098965351449891159 / 20000000000000000000000000)
  dδ := (19953388807432211765093 / 781250000000000000000000)
  dM := (27539565411672497965284157 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(34919008183127706601567297 / 10000000000000000000000000), (23964826008624193320883933 / 1000000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell259
