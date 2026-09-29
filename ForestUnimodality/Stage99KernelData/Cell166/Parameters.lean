import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 50
  A := (-4697577744466316601545941/5000000000000000000000000)
  B := (12009472207079686933983709/100000000000000000000000000)
  C := (12766736634385841830940933/50000000000000000000000000)
  dδ := (36186519432726702016900333/500000000000000000000000000)
  dM := (290867583530567621490949/156250000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(3272350279057211763777957/625000000000000000000000), (944915490917693667860533/62500000000000000000000)]
  retention := ![(3/5), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21/37)
  hi := (53/93)
  vmin := (2120/8649)
  damping := (2120/8649)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell166
