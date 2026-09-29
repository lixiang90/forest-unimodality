import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 89
  A := (-15517056681003559737064279/10000000000000000000000000)
  B := (95945037487766421380186443/1000000000000000000000000000)
  C := (6073718891315366651129093/2000000000000000000000000000)
  dδ := (12322228174330907002342883/200000000000000000000000000)
  dM := (2545880467436476175813187/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(12494831960110227342397593/1000000000000000000000000), (163798049272586482283387/7812500000000000000000), (53928747783472338994670281/1000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22597/43472)
  hi := (11311/21736)
  vmin := (117917175/472453696)
  damping := (117917175/472453696)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell108
