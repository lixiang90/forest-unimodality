import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell179
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-7964404384750513826674023/5000000000000000000000000)
  B := (2218835439269531417671999/20000000000000000000000000)
  C := (49034101694785531266873591/10000000000000000000000000000)
  dδ := (70475392456393351481303/1000000000000000000000000)
  dM := (3322029231401804291214097/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7393922784206417908592357/1000000000000000000000000), (7157503888913678835592691/1250000000000000000000000), (30610815622712809869199191/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47837/90312)
  hi := (95699/180624)
  vmin := (8127237575/32625029376)
  damping := (8127237575/32625029376)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell179
