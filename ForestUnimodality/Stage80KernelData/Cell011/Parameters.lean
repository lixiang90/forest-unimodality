import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 21
  A := (10439948233831631730694767/100000000000000000000000000)
  B := (16811917353266900981845211/500000000000000000000000000)
  C := (-33303043846315633080834573/500000000000000000000000000)
  dδ := (16911071661752999362171579/500000000000000000000000000)
  dM := (40680689382641154784592263/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(33371965733619707306090163/100000000000000000000000000), (7338632553433953598087669/1250000000000000000000000), (96406143361086638066126397/100000000000000000000000000)]
  retention := ![(3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1/3)
  hi := (29/85)
  vmin := (2/9)
  damping := (80000000000000000000000000000000000000000/888264396098042275699264258736843725914681)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell011
