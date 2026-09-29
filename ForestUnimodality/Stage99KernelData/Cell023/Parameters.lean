import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 50
  A := (-38816192117447316899614407/100000000000000000000000000)
  B := (68978740990720280312764601/1000000000000000000000000000)
  C := (-5221364511733490865186269/25000000000000000000000000)
  dδ := (57265564055588344394287503/1000000000000000000000000000)
  dM := (89979583346930095463095389/100000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(1834637884927490603104161/400000000000000000000000), (510242521030111584323663/31250000000000000000000)]
  retention := ![(3/5), (1/100)]
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
end ForestUnimodality.Stage99KernelData.Cell023
