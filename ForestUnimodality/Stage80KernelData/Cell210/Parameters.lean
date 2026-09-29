import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell210
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 40
  A := (-9254212002262393499307791/10000000000000000000000000)
  B := (1807866906353503000381977/10000000000000000000000000)
  C := (4857179069175869556840297/12500000000000000000000000)
  dδ := (13256951888067167177887029/100000000000000000000000000)
  dM := (20225782156957409184394603/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(8013492573207894320574951/1250000000000000000000000), (93469519720614933078195463/10000000000000000000000000)]
  retention := ![(3/10), (1/4)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53/93)
  hi := (107/187)
  vmin := (8560/34969)
  damping := (8560/34969)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell210
