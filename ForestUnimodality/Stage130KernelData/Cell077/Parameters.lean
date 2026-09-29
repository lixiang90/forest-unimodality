import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 76
  A := (-785589810888945264810701/625000000000000000000000)
  B := (95442423655349523103907927/1000000000000000000000000000)
  C := (12938762065249722645055019/10000000000000000000000000000)
  dδ := (70392267852765588731500657/1000000000000000000000000000)
  dM := (11486114611990946594161089/10000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(22853398089028305051328971/2500000000000000000000000), (2027661729032188830945671/1250000000000000000000000), (12782095858465277160576079/200000000000000000000000)]
  retention := ![(7/10), (3/5), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5227/10302)
  hi := (3493/6868)
  vmin := (11788875/47169424)
  damping := (11788875/47169424)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell077
