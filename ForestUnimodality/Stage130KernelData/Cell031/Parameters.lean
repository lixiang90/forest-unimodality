import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 79
  A := (-5107785254660702439721831/5000000000000000000000000)
  B := (41974797272647489110308783/500000000000000000000000000)
  C := (-54594114078804160256064293/10000000000000000000000000000)
  dδ := (35217169944825037208868679/500000000000000000000000000)
  dM := (49944166041698530387332733/50000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(10219077726378653636629679/1000000000000000000000000), (33847200147103727374542359/500000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1677/3572)
  hi := (841/1786)
  vmin := (3177915/12759184)
  damping := (3177915/12759184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell031
