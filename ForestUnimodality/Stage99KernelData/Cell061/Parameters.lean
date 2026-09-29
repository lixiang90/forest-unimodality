import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 62
  A := (-707218371111857883182239/625000000000000000000000)
  B := (5031283947135741646539131/50000000000000000000000000)
  C := (26472323789852956338330969/100000000000000000000000000000)
  dδ := (38869000691825139615076523/500000000000000000000000000)
  dM := (6865837665350557486934613/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7677339090760186834927481/2500000000000000000000000), (84886902886377342269952351/10000000000000000000000000), (24615680701563000809528603/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1/2)
  hi := (405/808)
  vmin := (163215/652864)
  damping := (163215/652864)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell061
