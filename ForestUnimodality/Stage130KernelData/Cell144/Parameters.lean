import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 88
  A := (-15814416573574651592082319/10000000000000000000000000)
  B := (49173624652403068180372969/500000000000000000000000000)
  C := (44992366688887449471812019/10000000000000000000000000000)
  dδ := (7873895097214544253061419/125000000000000000000000000)
  dM := (1316716085358766985796003/1250000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12209718763037265887305693/1000000000000000000000000), (546567345348019184569921/400000000000000000000000), (998187494384908724498473/62500000000000000000000), (28406469690972002695161791/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
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
end ForestUnimodality.Stage130KernelData.Cell144
