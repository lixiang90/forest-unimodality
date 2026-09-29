import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 57
  A := (-27997405912233557344848123/100000000000000000000000000)
  B := (9117172250993249571493493/200000000000000000000000000)
  C := (-7587920616807401763548313/50000000000000000000000000)
  dδ := (18873287169090948584004863/500000000000000000000000000)
  dM := (44624640178145741136947477/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(1963942442700225221585697/500000000000000000000000), (2019088136348623763183241/100000000000000000000000)]
  retention := ![(7/10), (1/1000)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (65/153)
  hi := (22/51)
  vmin := (5720/23409)
  damping := (5720/23409)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell023
