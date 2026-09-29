import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 53
  A := (-7829825648101115309174247/50000000000000000000000000)
  B := (1248625699184577374570293/31250000000000000000000000)
  C := (-13592796720220448603022589/100000000000000000000000000)
  dδ := (35622556340453630230324933/1000000000000000000000000000)
  dM := (38227579740850821041209251/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(36527335197764130292341633/10000000000000000000000000), (4633867328249986705657193/250000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (64/153)
  hi := (65/153)
  vmin := (5696/23409)
  damping := (5696/23409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell022
