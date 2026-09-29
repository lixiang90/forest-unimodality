import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell215
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 39
  A := (-24328624108931721808701809/25000000000000000000000000)
  B := (7815004248609050407914367/50000000000000000000000000)
  C := (5783073353336253275003287/20000000000000000000000000)
  dδ := (11895966571024478575235861/125000000000000000000000000)
  dM := (3861476956998392503529749/1250000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(18894394144026851467543793/5000000000000000000000000), (5729704743726690807648083/500000000000000000000000)]
  retention := ![(7/20), (3/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27/47)
  hi := (653/1128)
  vmin := (310175/1272384)
  damping := (310175/1272384)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell215
