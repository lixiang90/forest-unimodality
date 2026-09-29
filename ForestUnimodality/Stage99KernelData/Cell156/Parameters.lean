import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 100
  A := (18607923570443521910533491/50000000000000000000000000)
  B := (716981236564157436985667/10000000000000000000000000)
  C := (57417670116719299322483039/100000000000000000000000000)
  dδ := (3217710377910693031466849/25000000000000000000000000)
  dM := (6546230494702324998954057/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(62257416699254157776977081/10000000000000000000000000), (3402762789989163816350981/1250000000000000000000000), (3745030341582386057552867/100000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57/107)
  hi := (29/54)
  vmin := (725/2916)
  damping := (725/2916)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell156
