import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 89
  A := (-10609082107188613674964017/10000000000000000000000000)
  B := (13686952337412827684914873/100000000000000000000000000)
  C := (10152659875008789303052481/20000000000000000000000000)
  dδ := (11701309513837176989881073/100000000000000000000000000)
  dM := (21168766454623530112733043/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(81137786137798766361584057/10000000000000000000000000), (2475775920582754974219597/125000000000000000000000), (5799086712827057787933427/500000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29/54)
  hi := (643/1188)
  vmin := (350435/1411344)
  damping := (350435/1411344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell157
