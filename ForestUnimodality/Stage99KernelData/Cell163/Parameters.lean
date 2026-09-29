import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 59
  A := (8550994364258865469707871/1250000000000000000000000)
  B := (-42040596803120916513663019/500000000000000000000000000)
  C := (6095016206067477293473189/20000000000000000000000000)
  dδ := (39717495430029642333735751/500000000000000000000000000)
  dM := 0
  wL := 0
  wR := 1
  wC := 0
  price := ![(77544594571223948165084039/10000000000000000000000000), (23282559190019189720999293/5000000000000000000000000), (5066967654334851189901201/250000000000000000000000)]
  retention := ![(19/20), (7/10), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5/9)
  hi := (116/207)
  vmin := (10556/42849)
  damping := (10556/42849)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell163
