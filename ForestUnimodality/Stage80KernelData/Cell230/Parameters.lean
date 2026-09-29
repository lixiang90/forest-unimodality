import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell230
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := 15
  A := (3785179941002343713165601/4000000000000000000000000)
  B := (-517271598722728108248059/781250000000000000000000000)
  C := (5338103013785131661927963/50000000000000000000000000)
  dδ := (8020463246848096028340791/125000000000000000000000000)
  dM := (15623659475043241533220861/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(28876896095000490483073463/5000000000000000000000000)]
  retention := ![(7/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2/3)
  hi := (35/52)
  vmin := (595/2704)
  damping := (1487500000000000000000000000000000000000000/16679631437841016065908406636280732186620121)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell230
