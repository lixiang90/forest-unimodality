import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 41
  A := (-35124910693024140705631453/100000000000000000000000000)
  B := (19884402063322598186445589/200000000000000000000000000)
  C := (53248494757915203201559251/10000000000000000000000000000)
  dδ := (11487405197409554513665597/100000000000000000000000000)
  dM := (650074139197002960665131/312500000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11677846390762521622264103/2000000000000000000000000), (1696184916920749907731647/10000000000000000000000000), (34530670003498123321605817/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7339/14214)
  hi := (107/207)
  vmin := (10700/42849)
  damping := (10700/42849)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell104
