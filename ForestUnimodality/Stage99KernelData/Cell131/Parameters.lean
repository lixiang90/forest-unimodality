import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 124
  A := (400907994251009851982559/3125000000000000000000000)
  B := (94970735100185374455428189/1000000000000000000000000000)
  C := (70471368022345370896175609/100000000000000000000000000)
  dδ := (945921910932400085425531/6250000000000000000000000)
  dM := (16523873740327211980666311/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(71503195552427296632913567/10000000000000000000000000), (19312055848979996497405409/5000000000000000000000000), (6990663268011767961240821/250000000000000000000000), (18822072422101822297690887/1000000000000000000000000)]
  retention := ![(4/5), (7/10), (3/20), (1/10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47239/89464)
  hi := (94503/178928)
  vmin := (7978415775/32015229184)
  damping := (7978415775/32015229184)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell131
