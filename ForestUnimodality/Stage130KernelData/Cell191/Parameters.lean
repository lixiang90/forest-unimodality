import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell191
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-16747034710962231296349501/10000000000000000000000000)
  B := (10159867477981426864275249/100000000000000000000000000)
  C := (47517728885333549923575269/10000000000000000000000000000)
  dδ := (3868065882118890911472997/62500000000000000000000000)
  dM := (2710093520266342492948397/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(11474316743065729795603147/1000000000000000000000000), (11189940898631174359678653/5000000000000000000000000), (29537519261242913160003809/500000000000000000000000), (2696165160480127198638911/200000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47887/90312)
  hi := (31933/60208)
  vmin := (902905575/3625003264)
  damping := (902905575/3625003264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell191
