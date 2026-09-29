import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage80KernelData.Cell181
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := 84
  A := (-3118397362878704595061663/2000000000000000000000000)
  B := (2002535236023151310469359/10000000000000000000000000)
  C := (12180958308415958946113733/20000000000000000000000000)
  dδ := (3793538998617063118246051/25000000000000000000000000)
  dM := (7207191512282757825391677/2000000000000000000000000000)
  wL := 0
  wR := 1
  wC := 0
  price := ![(10489239178715756395376957/1000000000000000000000000), (26079671553368299896646931/1000000000000000000000000)]
  retention := ![(3/5), (1/10)]
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
end ForestUnimodality.Stage80KernelData.Cell181
