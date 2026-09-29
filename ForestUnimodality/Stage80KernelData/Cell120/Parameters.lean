import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 42
  A := (-3609480550223663236408811/25000000000000000000000000)
  B := (16386355283458997611489849/200000000000000000000000000)
  C := (48137327644576692955991071/10000000000000000000000000000)
  dδ := (11105812811751787638758771/100000000000000000000000000)
  dM := (17212156613473470097297469/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(34371445231439183842780949/5000000000000000000000000), (16913505566837415017289459/500000000000000000000000), (10480862026753157145719797/10000000000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (109/209)
  hi := (4583/8778)
  vmin := (19225685/77053284)
  damping := (19225685/77053284)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell120
