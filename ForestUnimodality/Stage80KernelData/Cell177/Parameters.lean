import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell177
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 79
  A := (-11111674657506928520689371/10000000000000000000000000)
  B := (2551537018764072489718231/12500000000000000000000000)
  C := (71590036026040082539623199/100000000000000000000000000)
  dδ := (19280154388979053869945801/100000000000000000000000000)
  dM := (2153043461032259128090649/500000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(17625572951367523444332619/2000000000000000000000000), (5148285645697884405080913/200000000000000000000000)]
  retention := ![(3/5), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29/54)
  hi := (2557/4752)
  vmin := (5612615/22581504)
  damping := (5612615/22581504)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell177
