import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 48
  A := (-94745838626348826249312651/100000000000000000000000000)
  B := (11848260835031068638478757/100000000000000000000000000)
  C := (23836267133825225772447709/100000000000000000000000000)
  dδ := (68432691349699370508830043/1000000000000000000000000000)
  dM := (18268185449730597533224419/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(44913874358332099845370067/10000000000000000000000000), (7449765052768960948981203/500000000000000000000000)]
  retention := ![(3/5), (1/5)]
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
end ForestUnimodality.Stage99KernelData.Cell167
