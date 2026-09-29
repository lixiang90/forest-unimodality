import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 79
  A := (-11021900616386978610705683/10000000000000000000000000)
  B := (43481763036464511629208829/500000000000000000000000000)
  C := (-57382281523818872218112297/10000000000000000000000000000)
  dδ := (34931977979265352307614023/500000000000000000000000000)
  dM := (10274927951154178094178571/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(3836526242023671784409089/400000000000000000000000), (311494327140739590831231/12500000000000000000000), (43322832434236794085791189/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22/47)
  hi := (1677/3572)
  vmin := (550/2209)
  damping := (550/2209)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell030
