import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell373
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (70)
  A := (-50481957346965094068025337 / 100000000000000000000000000)
  B := (42589439722986302538920711 / 1000000000000000000000000000)
  C := (-837864614576821695179909 / 6250000000000000000000000)
  dδ := (14669724804142919225014019 / 500000000000000000000000000)
  dM := (6643673006370417544533269 / 20000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(53455641308603594197279563 / 10000000000000000000000000), (1539988954936084564195653 / 62500000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22 / 51)
  hi := (67 / 153)
  vmin := (638 / 2601)
  damping := (638 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell373
