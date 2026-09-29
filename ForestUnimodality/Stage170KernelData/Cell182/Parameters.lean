import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell182
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (287)
  A := (-2246050594429123055384423 / 1250000000000000000000000)
  B := (11875475044581106087715483 / 250000000000000000000000000)
  C := (357672251179118913348709 / 250000000000000000000000000)
  dδ := (28148391127627479801898147 / 1000000000000000000000000000)
  dM := (706719321925213623066973 / 3125000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(1631144376314115262971427 / 25000000000000000000000), (2199306767697692350793659 / 10000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27 / 52)
  hi := (109 / 209)
  vmin := (10900 / 43681)
  damping := (10900 / 43681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell182
