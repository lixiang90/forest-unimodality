import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell526
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (122)
  A := (-20853812521914897770614061 / 10000000000000000000000000)
  B := (11765766952544000345515229 / 100000000000000000000000000)
  C := (8708072068469073501173483 / 25000000000000000000000000)
  dδ := (62239670714696174180780019 / 1000000000000000000000000000)
  dM := (1409701601761449176169333 / 1250000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(11654041993118593456557619 / 1250000000000000000000000), (22595089197126348778965621 / 500000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57 / 107)
  hi := (29 / 54)
  vmin := (725 / 2916)
  damping := (725 / 2916)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell526
