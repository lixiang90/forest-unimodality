import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell229
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 37
  A := (-17317602714568433086128607/50000000000000000000000000)
  B := (562359920157685724828589/10000000000000000000000000)
  C := (5493139458652235296298727/50000000000000000000000000)
  dδ := (18051680896509155610507591/500000000000000000000000000)
  dM := (6569980973994119953160431/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(279916638844109044725883/200000000000000000000000), (13197946418548036628948239/5000000000000000000000000), (10268519316810193586775313/1000000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3/5)
  hi := (123/203)
  vmin := (9840/41209)
  damping := (9840/41209)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell229
