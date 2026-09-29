import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 61
  A := (-24879749553088955693169737/50000000000000000000000000)
  B := (72849084686937140564744197/1000000000000000000000000000)
  C := (7019540260925107369449627/2000000000000000000000000000)
  dδ := (9871083410159287724328081/125000000000000000000000000)
  dM := (5322151256719549923535073/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(14948666459238142412146999/10000000000000000000000000), (37200597047029457797862051/5000000000000000000000000), (667557912511240836295201/50000000000000000000000), (38140811806232882474887447/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22647/43472)
  hi := (109/209)
  vmin := (10900/43681)
  damping := (10900/43681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell107
