import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 50
  A := (-11738970064522590086397713/20000000000000000000000000)
  B := (4573476681055309994716751/50000000000000000000000000)
  C := (33605891577446391632610911/10000000000000000000000000000)
  dδ := (47446778576731456211756921/500000000000000000000000000)
  dM := (15489374054223825280529603/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(58306077605607402603027367/10000000000000000000000000), (2485051845410214621523437/1000000000000000000000000), (17281738187321860067413581/1000000000000000000000000), (11862065367742665955574921/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21967/42642)
  hi := (10996/21321)
  vmin := (113533700/454585041)
  damping := (113533700/454585041)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell086
