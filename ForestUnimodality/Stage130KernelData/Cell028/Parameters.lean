import ForestUnimodality.FiniteKernelInfiniteTails
/-! Mathematical parameters only; all signs are checked by the Lean kernel. -/
namespace ForestUnimodality.Stage130KernelData.Cell028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def row : RationalRow (Fin 4) where
  terms := Finset.univ
  scale := 104
  A := (-6303809308080610912483621/5000000000000000000000000)
  B := (1295187714500782398541201/12500000000000000000000000)
  C := (-38083012792945142299672057/100000000000000000000000000)
  dδ := (9542294670680280185837141/125000000000000000000000000)
  dM := (5806033439069913830790637/5000000000000000000000000000)
  wL := 1
  wR := 0
  wC := 0
  price := ![(19861813077806966809646383/2500000000000000000000000), (14870693298809523064107907/50000000000000000000000000), (13855455955662828060326319/1000000000000000000000000), (4883360404835285351055063/200000000000000000000000)]
  retention := ![(7/10), (3/5), (1/20), (1/100)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (17/37)
  hi := (1613/3478)
  vmin := (340/1369)
  damping := (340/1369)

theorem row_checked : row.signCheck=true := by decide +kernel
theorem interval_checked : interval.check=true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage130KernelData.Cell028
