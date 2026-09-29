import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 118
  A := (49091814549978939901109243/500000000000000000000000000)
  B := (46550318760076134227965383/500000000000000000000000000)
  C := (66955953306475979314171809/100000000000000000000000000)
  dδ := (3637386279327198268518373/25000000000000000000000000)
  dM := (8011423782831106951002331/5000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(32199919660632456697157977/5000000000000000000000000), (41718371407996555078057099/10000000000000000000000000), (22792557298791368936008439/1000000000000000000000000), (21408479468821902003128343/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11953/22578)
  hi := (31883/60208)
  vmin := (903085975/3625003264)
  damping := (903085975/3625003264)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell141
