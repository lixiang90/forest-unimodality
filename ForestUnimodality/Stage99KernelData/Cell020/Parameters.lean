import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 40
  A := (30571728089043913598743529/1000000000000000000000000000)
  B := (37035914954259403775171933/1000000000000000000000000000)
  C := (-2484049407962205524569299/20000000000000000000000000)
  dδ := (9377921901269299642667221/250000000000000000000000000)
  dM := (42206043567677225484408021/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(11899255401721349212351697/5000000000000000000000000), (13959604724988881940817009/1000000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (103/255)
  hi := (7/17)
  vmin := (15656/65025)
  damping := (15656/65025)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell020
