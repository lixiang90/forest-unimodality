import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 38
  A := (-24730454703299058593302107/100000000000000000000000000)
  B := (10097065186814635495693437/100000000000000000000000000)
  C := (6723991999986462901606199/1250000000000000000000000000)
  dδ := (767207743457520331686883/6250000000000000000000000)
  dM := (5729499608465080497457511/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(54581389596086893334359047/10000000000000000000000000), (48887754730457695373502247/5000000000000000000000000), (4479928300382712791360973/200000000000000000000000)]
  retention := ![(7/10), (1/10), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21967/42642)
  hi := (10996/21321)
  vmin := (113533700/454585041)
  damping := (113533700/454585041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell100
