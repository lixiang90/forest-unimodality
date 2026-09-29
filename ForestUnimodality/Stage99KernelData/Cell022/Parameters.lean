import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 46
  A := (-17045475733593048516922863/50000000000000000000000000)
  B := (810434667815149167857669/12500000000000000000000000)
  C := (-9192580784986241482226177/50000000000000000000000000)
  dδ := (409113443363621868964497/7812500000000000000000000)
  dM := (83570014741884946461725203/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(37523842049981022128690711/10000000000000000000000000), (15212981804009602981864191/1000000000000000000000000)]
  retention := ![(3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (64/153)
  hi := (65/153)
  vmin := (5696/23409)
  damping := (5696/23409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell022
