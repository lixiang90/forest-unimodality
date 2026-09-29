import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 86
  A := (-14064952346967502416674733/10000000000000000000000000)
  B := (92530555073169817870137877/1000000000000000000000000000)
  C := (-11960402476230993194794561/10000000000000000000000000000)
  dδ := (63675238060326974642855191/1000000000000000000000000000)
  dM := (10096516664858195232168381/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(9913546791985251571688309/1250000000000000000000000), (30790093336951436242543423/5000000000000000000000000), (35221089733256036424791091/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9529/19404)
  hi := (4777/9702)
  vmin := (94098875/376515216)
  damping := (94098875/376515216)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell058
