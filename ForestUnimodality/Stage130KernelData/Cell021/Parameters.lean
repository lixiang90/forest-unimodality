import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 49
  A := (-55200558607400408419607629/1000000000000000000000000000)
  B := (17464915182926161324461489/500000000000000000000000000)
  C := (-3009508925081635227760657/25000000000000000000000000)
  dδ := (8267944395397802334612969/250000000000000000000000000)
  dM := (16392070844313856039196897/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(34128399190516600647526957/10000000000000000000000000), (16875249413925526908997199/1000000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7/17)
  hi := (64/153)
  vmin := (70/289)
  damping := (70/289)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell021
