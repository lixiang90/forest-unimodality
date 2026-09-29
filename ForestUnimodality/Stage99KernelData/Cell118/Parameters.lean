import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage99KernelData.Cell118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := 50
  A := (-16012514650651044978246773/20000000000000000000000000)
  B := (2538423505823609108156269/25000000000000000000000000)
  C := (52431645920644536981725103/10000000000000000000000000000)
  dδ := (2287425718439997646136419/25000000000000000000000000)
  dM := (3344044569969089730071543/2000000000000000000000000000)
  wL := 0
  wR := 0
  wC := 1
  price := ![(7746796405111417982425337/1250000000000000000000000), (14818463847601064387049519/10000000000000000000000000), (8286769378894535975632607/200000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20)]
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
end ForestUnimodality.Stage99KernelData.Cell118
