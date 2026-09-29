import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell493
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (103)
  A := (-18058871353685112437403859 / 10000000000000000000000000)
  B := (96120606806997688220661757 / 1000000000000000000000000000)
  C := (2329333286131984480024637 / 1250000000000000000000000000)
  dδ := (1728865585487334398384629 / 31250000000000000000000000)
  dM := (23050805829318612430109403 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(44577934643093675148861621 / 5000000000000000000000000), (18445015140781214313392411 / 200000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (10787 / 21012)
  hi := (53 / 103)
  vmin := (2650 / 10609)
  damping := (2650 / 10609)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell493
