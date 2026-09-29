import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell217
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 35
  A := (3721239513881475401433363/1000000000000000000000000)
  B := (-6437591738238350458356507/100000000000000000000000000)
  C := (6242864700739561567566227/25000000000000000000000000)
  dδ := (86176535354288971713110357/1000000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(25553348360254437565686203/5000000000000000000000000), (155400938755218265274749/2500000000000000000000000), (12795861676277958451919403/1000000000000000000000000)]
  retention := ![(9/10), (7/10), (1/4)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7/12)
  hi := (53/90)
  vmin := (1961/8100)
  damping := (1961/8100)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell217
