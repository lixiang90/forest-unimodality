import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 100
  A := (-6533552480755363345110709/20000000000000000000000000)
  B := (15213906255182949034399087/100000000000000000000000000)
  C := (81007143354708999183344531/100000000000000000000000000)
  dδ := (10020216661379797995490293/50000000000000000000000000)
  dM := (32133047862868721437912267/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(654173663105448777166373/62500000000000000000000), (17544794297894185319819371/500000000000000000000000)]
  retention := ![(7/10), (1/20)]
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
end ForestUnimodality.Stage80KernelData.Cell167
