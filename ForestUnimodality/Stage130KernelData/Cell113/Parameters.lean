import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 73
  A := (-3889297511693624423401161/2500000000000000000000000)
  B := (1397268411206774307853351/12500000000000000000000000)
  C := (9343638563862646491745001/2500000000000000000000000000)
  dδ := (35396626695155350428301233/500000000000000000000000000)
  dM := (2753857998844828208762081/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7777011015839810914584973/1250000000000000000000000), (57572522081008541405822143/10000000000000000000000000), (29699187088292550384949209/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (109/209)
  hi := (4583/8778)
  vmin := (19225685/77053284)
  damping := (19225685/77053284)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell113
