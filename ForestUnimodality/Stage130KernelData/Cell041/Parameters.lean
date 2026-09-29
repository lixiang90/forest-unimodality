import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 70
  A := (-16363325092930657744716427/10000000000000000000000000)
  B := (12053839626383565375444817/100000000000000000000000000)
  C := (-6703408814578566167485807/2000000000000000000000000000)
  dδ := (9444110110696535623220349/125000000000000000000000000)
  dM := (7683790745639232019903453/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(6887613112497918521626161/500000000000000000000000), (54516250089234617348665779/1000000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (2983/6208)
  hi := (4487/9312)
  vmin := (9620175/38539264)
  damping := (9620175/38539264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell041
