import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 20
  A := (302049668603082728282061/4000000000000000000000000)
  B := (21490435953146199560270801/1000000000000000000000000000)
  C := (-31872352701409513431318743/1000000000000000000000000000)
  dδ := (9959660079149250042074293/500000000000000000000000000)
  dM := (1700968604263754181595697/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(2107208392372861838204301/10000000000000000000000000), (5734494727547907039211239/50000000000000000000000000), (57300660422633633572786493/10000000000000000000000000)]
  retention := ![(3/5), (1/2), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37/126)
  hi := (19/63)
  vmin := (3293/15876)
  damping := (32930000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell006
