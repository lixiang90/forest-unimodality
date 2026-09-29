import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 50
  A := (-69122353073215985318711319/100000000000000000000000000)
  B := (94935645150561853711224103/1000000000000000000000000000)
  C := (47813293130500008135119749/10000000000000000000000000000)
  dδ := (90796889546229442302660573/1000000000000000000000000000)
  dM := (7861978580489301744391173/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(72514989844212260905464973/10000000000000000000000000), (1311602247644282348559841/31250000000000000000000)]
  retention := ![(7/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1531/2926)
  hi := (11/21)
  vmin := (110/441)
  damping := (110/441)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell114
