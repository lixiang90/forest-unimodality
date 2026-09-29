import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (289)
  A := (-4521898772780524713965633 / 2500000000000000000000000)
  B := (2367039746351693590975529 / 50000000000000000000000000)
  C := (21417616740444713353125339 / 25000000000000000000000000000)
  dδ := (13970325351765251059577011 / 500000000000000000000000000)
  dM := (4479648016104434112352739 / 20000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(27341117171425867837797341 / 500000000000000000000000), (23248193220200218434001727 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell167
