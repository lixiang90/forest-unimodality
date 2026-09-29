import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 51
  A := (-1372949815822957048472297/1562500000000000000000000)
  B := (10593285748924381739488609/100000000000000000000000000)
  C := (49066893398193554831632213/10000000000000000000000000000)
  dδ := (91635646509516999191902187/1000000000000000000000000000)
  dM := (4314146785216920387470707/2500000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(28833129020491767846579023/5000000000000000000000000), (10096338546244401079832187/5000000000000000000000000), (21124349823678183923902907/500000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22647/43472)
  hi := (109/209)
  vmin := (10900/43681)
  damping := (10900/43681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage99KernelData.Cell106
