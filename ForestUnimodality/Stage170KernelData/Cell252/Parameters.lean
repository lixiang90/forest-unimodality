import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell252
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (86)
  A := (-33043931913706841129396707 / 100000000000000000000000000)
  B := (22160086384079891869136603 / 1000000000000000000000000000)
  C := (1490259936738053681004601 / 20000000000000000000000000)
  dδ := (588147181386992207174913 / 40000000000000000000000000)
  dM := (10578985178273791621823829 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(2905990992417870444342043 / 200000000000000000000000), (561042584755702300469693 / 25000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13 / 23)
  hi := (21 / 37)
  vmin := (336 / 1369)
  damping := (336 / 1369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell252
