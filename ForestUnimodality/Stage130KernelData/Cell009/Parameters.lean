import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 25
  A := (10991734740976289886660311/100000000000000000000000000)
  B := (7889685411317098884254051/500000000000000000000000000)
  C := (-1127538411330853973524313/40000000000000000000000000)
  dδ := (15018201792327115495773171/1000000000000000000000000000)
  dM := (5083648898812706139107437/50000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(13254410176366633322686539/10000000000000000000000000), (68762003026252163095932701/10000000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (20/63)
  hi := (41/126)
  vmin := (860/3969)
  damping := (34400000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell009
