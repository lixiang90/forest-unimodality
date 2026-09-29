import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 74
  A := (-2753587442387781838419869/2000000000000000000000000)
  B := (10280901052776392212706469/100000000000000000000000000)
  C := (14665490238395606850674291/5000000000000000000000000000)
  dδ := (71694988723613267689316331/1000000000000000000000000000)
  dM := (12578387139484845883702357/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(67592550370171240459171713/10000000000000000000000000), (62610504585332762417237973/10000000000000000000000000), (29767074446289878864035927/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7339/14214)
  hi := (107/207)
  vmin := (10700/42849)
  damping := (10700/42849)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell095
