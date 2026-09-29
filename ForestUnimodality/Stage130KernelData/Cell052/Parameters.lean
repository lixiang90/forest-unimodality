import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 84
  A := (-2885587314154975804285641/2000000000000000000000000)
  B := (96126488904639026400467117/1000000000000000000000000000)
  C := (-20510030344958996538495821/10000000000000000000000000000)
  dδ := (65068103621042122641782157/1000000000000000000000000000)
  dM := (10695163663100117935889077/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(14807671444203498012370801/2000000000000000000000000), (51521036973806149106280827/10000000000000000000000000), (34969129911426804824259307/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4631/9506)
  hi := (9287/19012)
  vmin := (22576125/90364036)
  damping := (22576125/90364036)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell052
