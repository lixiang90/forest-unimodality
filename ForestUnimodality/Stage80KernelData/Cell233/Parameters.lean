import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell233
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 15
  A := (61342734877818356654444187/100000000000000000000000000)
  B := (49399009693239272211773283/5000000000000000000000000000)
  C := (73305645445723072173294099/1000000000000000000000000000)
  dδ := (44589056815476112161089617/1000000000000000000000000000)
  dM := (19435209601119407020475283/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(795971446690928174927393/156250000000000000000000), (3814644269355895594975081/12500000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (35/52)
  hi := (53/78)
  vmin := (1325/6084)
  damping := (13250000000000000000000000000000000000000000/150116682940569144593175659726526589679581089)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell233
