import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 54
  A := (14081109328094005729070659/100000000000000000000000000)
  B := (52718793842770256263818851/1000000000000000000000000000)
  C := (-21817529156319135155706057/5000000000000000000000000000)
  dδ := (88500430122065071314452211/1000000000000000000000000000)
  dM := (12170322160569211321096833/12500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(9307121166631506792299433/5000000000000000000000000), (886951952417061734168513/156250000000000000000000), (11629691860048374962843809/250000000000000000000000)]
  retention := ![(4/5), (7/10), (1/100)]
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
end ForestUnimodality.Stage99KernelData.Cell033
