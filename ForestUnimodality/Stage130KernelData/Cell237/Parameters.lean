import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell237
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 23
  A := (10941573760332896026348237/50000000000000000000000000)
  B := (5680598219530299565482867/250000000000000000000000000)
  C := (28927827985571214625126757/500000000000000000000000000)
  dδ := (278475772941709012742173/10000000000000000000000000)
  dM := (11882388252563726952371753/50000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(18203149080953602290122717/2500000000000000000000000), (11045308016327090583352799/12500000000000000000000000)]
  retention := ![(7/10), (3/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (41/63)
  hi := (83/126)
  vmin := (3569/15876)
  damping := (35690000000000000000000000000000000000000000/391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell237
