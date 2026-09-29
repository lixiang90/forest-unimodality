import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 75
  A := (-11399392854582840917032627/10000000000000000000000000)
  B := (2888988653662266994914809/31250000000000000000000000)
  C := (13685233051210640101841287/5000000000000000000000000000)
  dδ := (36464100760659173827704649/500000000000000000000000000)
  dM := (2843286270328891315352371/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(5284246258465255863256971/500000000000000000000000), (11973892362151823931526451/200000000000000000000000), (3351925231941024652115857/1000000000000000000000000)]
  retention := ![(7/10), (1/100), (1/1000)]
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
end ForestUnimodality.Stage130KernelData.Cell089
