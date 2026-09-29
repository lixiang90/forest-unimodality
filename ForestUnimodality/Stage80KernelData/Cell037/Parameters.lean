import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 119
  A := (-38181243400936597630845881/100000000000000000000000000)
  B := (14387769366332311959943979/100000000000000000000000000)
  C := (-84887900859000620101824097/100000000000000000000000000)
  dδ := (973622572010997278102451/5000000000000000000000000)
  dM := (13820757311627761276806581/5000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(1408299224724609555181587/125000000000000000000000), (21838310648916561262922187/500000000000000000000000)]
  retention := ![(7/10), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1687/3572)
  hi := (9/19)
  vmin := (3179995/12759184)
  damping := (3179995/12759184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell037
