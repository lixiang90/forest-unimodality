import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 35
  A := (-21509915817391560665328143/100000000000000000000000000)
  B := (10560131008423989662503573/100000000000000000000000000)
  C := (38093380360332703381265329/5000000000000000000000000000)
  dδ := (6397342829234828331941287/50000000000000000000000000)
  dM := (1023719690117330313738897/400000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(26442467919686518662558683/5000000000000000000000000), (22963739638601516901417199/5000000000000000000000000), (24783341149655843338450723/1000000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell125
