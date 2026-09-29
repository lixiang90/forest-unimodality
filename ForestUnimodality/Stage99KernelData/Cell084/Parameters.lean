import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 50
  A := (-275635454596114358186143/390625000000000000000000)
  B := (24395417259496128548068583/250000000000000000000000000)
  C := (32781303156392835665422503/10000000000000000000000000000)
  dδ := (2375525819770226906846311/25000000000000000000000000)
  dM := (8146963008007502551541257/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5182724127036950623192979/1250000000000000000000000), (51441709054201405493245147/10000000000000000000000000), (39912290126708882098682807/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/103)
  hi := (21967/42642)
  vmin := (454167725/1818340164)
  damping := (454167725/1818340164)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell084
