import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell230
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 34
  A := (-4426982841897280376741719/12500000000000000000000000)
  B := (2187171315085083000973043/40000000000000000000000000)
  C := (4824768874692175746332623/50000000000000000000000000)
  dδ := (33052130599066448235490157/1000000000000000000000000000)
  dM := (63916244745750407704049101/100000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(334235131451231376464861/625000000000000000000000), (34238264648902281273024073/10000000000000000000000000), (44783579838339084844278659/5000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (123/203)
  hi := (63/103)
  vmin := (2520/10609)
  damping := (2520/10609)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell230
