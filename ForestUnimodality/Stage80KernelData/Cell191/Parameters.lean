import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell191
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 68
  A := (9165038192828681739570129/500000000000000000000000)
  B := (-5637486683924772812304127/20000000000000000000000000)
  C := (14645511277669676086787831/25000000000000000000000000)
  dδ := (16398143908177750804888717/100000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(20021992229835035459473147/1000000000000000000000000), (11908459438385770035040423/2500000000000000000000000), (17290093308455841025761401/1000000000000000000000000), (64854549124633420476015999/10000000000000000000000000)]
  retention := ![(19/20), (3/5), (1/4), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2587/4752)
  hi := (6/11)
  vmin := (30/121)
  damping := (30/121)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell191
