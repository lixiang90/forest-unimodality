import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 58
  A := (-11996834888925335962817087/12500000000000000000000000)
  B := (248914928513686642408409/2500000000000000000000000)
  C := (-9438014947747180860559979/2000000000000000000000000000)
  dδ := (5204714614575802617002509/62500000000000000000000000)
  dM := (7307291075117713528494501/5000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(46437276406353529267789781/10000000000000000000000000), (18772639996226170300275271/5000000000000000000000000), (24281725571323026002801271/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (581/1216)
  hi := (23/48)
  vmin := (368935/1478656)
  damping := (368935/1478656)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell041
