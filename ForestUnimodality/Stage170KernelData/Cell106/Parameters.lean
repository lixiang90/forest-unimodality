import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (99)
  A := (-71883260361612648758011801 / 100000000000000000000000000)
  B := (3979289072100061080972111 / 100000000000000000000000000)
  C := (-14736722253486439493386229 / 100000000000000000000000000)
  dδ := (26501359096640812046397073 / 1000000000000000000000000000)
  dM := (12601501427957190171712243 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(21100232329225772076597423 / 1000000000000000000000000), (1421894983048115124191213 / 62500000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (4 / 9)
  hi := (301 / 666)
  vmin := (20 / 81)
  damping := (20 / 81)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell106
