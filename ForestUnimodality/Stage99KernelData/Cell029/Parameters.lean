import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 102
  A := (-75746257179635689738006477/10000000000000000000000000000)
  B := (88234538200911080685351351/1000000000000000000000000000)
  C := (-57954369277423356532352727/100000000000000000000000000)
  dδ := (6438951595106695569015187/50000000000000000000000000)
  dM := (14893699683628386365441543/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(708214405104964639381393/312500000000000000000000), (68421974678520687263016953/10000000000000000000000000), (2359903670519892582291277/4000000000000000000000000), (9332583504712415489734667/250000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1613/3478)
  hi := (22/47)
  vmin := (3008245/12096484)
  damping := (3008245/12096484)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell029
