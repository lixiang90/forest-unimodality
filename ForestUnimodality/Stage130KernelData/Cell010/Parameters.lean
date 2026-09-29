import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 26
  A := (2359777062523581636810377/20000000000000000000000000)
  B := (7960015649696759038045357/500000000000000000000000000)
  C := (-7695031680543851053399873/250000000000000000000000000)
  dδ := (15507864736623600335208017/1000000000000000000000000000)
  dM := (325532677421377112251589/3125000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(2735236125664903372722847/2000000000000000000000000), (4606724665938496943162761/625000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (41/126)
  hi := (1/3)
  vmin := (3485/15876)
  damping := (34850000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell010
