import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 39
  A := (-12692334361655301277949093/10000000000000000000000000)
  B := (16364484348142946390503027/100000000000000000000000000)
  C := (-8435648940077483540558867/1250000000000000000000000000)
  dδ := (11925273369520072996863291/100000000000000000000000000)
  dM := (6534602166377634357985471/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(47919737665221973088591767/10000000000000000000000000), (32826298582769140921300277/1000000000000000000000000)]
  retention := ![(3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (581/1216)
  hi := (23/48)
  vmin := (368935/1478656)
  damping := (368935/1478656)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell041
