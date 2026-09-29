import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-8716802723316859574609339/5000000000000000000000000)
  B := (1461822158740903356000107/12500000000000000000000000)
  C := (50730842971878934918872339/10000000000000000000000000000)
  dδ := (69971831330576578222846251/1000000000000000000000000000)
  dM := (2778113201124260498581231/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(713226636420575960118029/156250000000000000000000), (5000804795570710226115807/500000000000000000000000), (59625490644070126222686667/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11791/22366)
  hi := (23607/44732)
  vmin := (498697875/2000951824)
  damping := (498697875/2000951824)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell136
