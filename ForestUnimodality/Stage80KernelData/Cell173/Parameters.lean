import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell173
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 85
  A := (1177347143291803094555803/25000000000000000000000000)
  B := (771782785499827272274187/6250000000000000000000000)
  C := (7438419395178668125367949/10000000000000000000000000)
  dδ := (19220573708715738003860451/100000000000000000000000000)
  dM := (5711738437516368678548151/2000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(89420400532979993357685089/10000000000000000000000000), (29888642324052948850976463/1000000000000000000000000)]
  retention := ![(7/10), (3/20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57/107)
  hi := (29/54)
  vmin := (725/2916)
  damping := (725/2916)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell173
