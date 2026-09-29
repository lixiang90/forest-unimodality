import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 61
  A := (-39065577932213129241034721/100000000000000000000000000)
  B := (17044306438758743266204121/250000000000000000000000000)
  C := (38125331575712818714396501/10000000000000000000000000000)
  dδ := (79454917261093424563078713/1000000000000000000000000000)
  dM := (10108214058255978080869131/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(18426381041326671539337667/10000000000000000000000000), (72271356679847977844133311/10000000000000000000000000), (16143767344362053961503989/1000000000000000000000000), (17660085360047411029427167/500000000000000000000000)]
  retention := ![(4/5), (7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4583/8778)
  hi := (2294/4389)
  vmin := (4805930/19263321)
  damping := (4805930/19263321)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell111
