import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 23
  A := (2981915411173985647419471/25000000000000000000000000)
  B := (15401983788473820255471303/1000000000000000000000000000)
  C := (-1025164053757232629493501/40000000000000000000000000)
  dδ := (3785426575377768589059091/250000000000000000000000000)
  dM := (24286005590798902226785591/250000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(5140232228872407826969493/5000000000000000000000000), (30847584910382694900476963/5000000000000000000000000)]
  retention := ![(3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19/63)
  hi := (13/42)
  vmin := (836/3969)
  damping := (33440000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell007
