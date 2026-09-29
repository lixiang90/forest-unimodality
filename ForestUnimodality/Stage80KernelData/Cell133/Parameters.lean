import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 37
  A := (-55943872225717218285012677/1000000000000000000000000000)
  B := (82249206192422666394925557/1000000000000000000000000000)
  C := (1602331068945713962725641/312500000000000000000000000)
  dδ := (1441953378095828762484043/12500000000000000000000000)
  dM := (19041771507294930759757179/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(62089787386798942492305287/10000000000000000000000000), (17172168381254163449511907/1000000000000000000000000), (420396568656681679510001/31250000000000000000000)]
  retention := ![(7/10), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1549/2954)
  hi := (2326/4431)
  vmin := (4896230/19633761)
  damping := (4896230/19633761)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell133
