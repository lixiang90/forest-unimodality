import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell234
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 28
  A := (-13459012744740932564724289/100000000000000000000000000)
  B := (20870889235060516297970423/500000000000000000000000000)
  C := (71409893440135943643021221/1000000000000000000000000000)
  dδ := (29076095394138204430767303/1000000000000000000000000000)
  dM := (23400747596994322529025123/50000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(4244669065941998886692943/2500000000000000000000000), (38007603617788160432766631/100000000000000000000000000), (806434871172912615122641/100000000000000000000000)]
  retention := ![(7/10), (3/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (467/742)
  hi := (236/371)
  vmin := (31860/137641)
  damping := (31860/137641)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell234
