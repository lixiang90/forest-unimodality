import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell235
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 26
  A := (-8355948416166378565073103/250000000000000000000000000)
  B := (35768400188778533277389471/1000000000000000000000000000)
  C := (32984921336718653339659113/500000000000000000000000000)
  dδ := (7050059464579167683995209/250000000000000000000000000)
  dM := (19621610689094922340934557/50000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(651999475394399036209947/312500000000000000000000), (7167467837088746795970451/2500000000000000000000000), (10949867779387900679211043/2500000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (236/371)
  hi := (9/14)
  vmin := (45/196)
  damping := (45/196)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell235
