import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell177
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-8291256797106156489718387/5000000000000000000000000)
  B := (5091229952627472632453731/50000000000000000000000000)
  C := (48522075902852762618877591/10000000000000000000000000000)
  dδ := (31449602904979723216882803/500000000000000000000000000)
  dM := (10929653268683136614625173/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(1142215983866767281540433/100000000000000000000000), (1318414855336263791230067/500000000000000000000000), (373797318413124080027643/31250000000000000000000), (6026320790379892144983387/100000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31883/60208)
  hi := (47837/90312)
  vmin := (2031876575/8156257344)
  damping := (2031876575/8156257344)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell177
