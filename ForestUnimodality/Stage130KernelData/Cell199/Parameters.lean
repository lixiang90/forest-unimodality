import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell199
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 88
  A := (-17122723675729367054287877/10000000000000000000000000)
  B := (10322924864584945292556029/100000000000000000000000000)
  C := (46113571073419894197353841/10000000000000000000000000000)
  dδ := (3858823885659786335350363/62500000000000000000000000)
  dM := (5513038575181114812548411/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(888629122821412806843/80000000000000000000), (55767932584700616871487/20000000000000000000000), (72334347142861147972325853/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (8069/15194)
  hi := (12116/22791)
  vmin := (129338300/519429681)
  damping := (129338300/519429681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell199
