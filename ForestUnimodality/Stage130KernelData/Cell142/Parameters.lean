import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 68
  A := (-9377731889899385225817241/5000000000000000000000000)
  B := (821153336027961172627343/6250000000000000000000000)
  C := (164032951543730004138541/31250000000000000000000000)
  dδ := (14625185968133100344878983/200000000000000000000000000)
  dM := (3345999546713804111142121/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(15387627566143610380322571/1000000000000000000000000), (25334479590241080870782753/500000000000000000000000)]
  retention := ![(3/5), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell142
