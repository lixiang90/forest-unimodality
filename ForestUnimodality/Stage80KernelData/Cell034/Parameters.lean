import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 113
  A := (-1076529250745301440304047/4000000000000000000000000)
  B := (6589383778352632392572019/50000000000000000000000000)
  C := (-79563372306966473335165801/100000000000000000000000000)
  dδ := (18349539212814897082282073/100000000000000000000000000)
  dM := (25262103509766349954124287/10000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(2701240081473941234690983/250000000000000000000000), (41314929343634112512972933/1000000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (841/1786)
  hi := (1687/3572)
  vmin := (794745/3189796)
  damping := (794745/3189796)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell034
