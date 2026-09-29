import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 60
  A := (-7160459155791478790931137/50000000000000000000000000)
  B := (31309541185934763873888187/500000000000000000000000000)
  C := (-5456007946575789357979147/20000000000000000000000000)
  dδ := (68523556942910943123870027/1000000000000000000000000000)
  dM := (87470421057488014372066631/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(11419275108867148471603059/2500000000000000000000000), (3345709009334176253780413/20000000000000000000000000), (2680893504408200733735157/125000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (67/153)
  hi := (4/9)
  vmin := (5762/23409)
  damping := (5762/23409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell025
