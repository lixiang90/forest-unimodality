import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell179
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 80
  A := (-2843003227830866289060907/2500000000000000000000000)
  B := (18490199377064109320656371/100000000000000000000000000)
  C := (16225195957224827769671549/25000000000000000000000000)
  dδ := (16853895481730093997008169/100000000000000000000000000)
  dM := (35911025171859278608266219/10000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(634335273792373754986329/62500000000000000000000), (779154205378762565459283/31250000000000000000000)]
  retention := ![(3/5), (1/5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29/54)
  hi := (2557/4752)
  vmin := (5612615/22581504)
  damping := (5612615/22581504)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage80KernelData.Cell179
