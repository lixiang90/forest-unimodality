import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 75
  A := (-15200138444229333478574517/10000000000000000000000000)
  B := (5358716308134722078326817/50000000000000000000000000)
  C := (-5137708621621005916635383/20000000000000000000000000000)
  dδ := (68910444694510991636704489/1000000000000000000000000000)
  dM := (12881637105208777489134819/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(23372282438056690700989293/5000000000000000000000000), (180140223228443829839307/25000000000000000000000), (61531277179564533241773461/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (395/792)
  hi := (1/2)
  vmin := (156815/627264)
  damping := (156815/627264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell066
