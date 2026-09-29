import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (139)
  A := (-8853348023985964881887867 / 5000000000000000000000000)
  B := (19135787234372304138618759 / 250000000000000000000000000)
  C := (13839507613375640667635613 / 10000000000000000000000000000)
  dδ := (45554973587926310407691943 / 1000000000000000000000000000)
  dM := (1483645162036354781583819 / 2500000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(16970775988009279444668209 / 500000000000000000000000), (5162180869817883177574913 / 50000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (26 / 51)
  hi := (53 / 103)
  vmin := (2650 / 10609)
  damping := (2650 / 10609)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell163
