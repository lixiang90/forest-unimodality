import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (172)
  A := (-7086309824331659906704317 / 5000000000000000000000000)
  B := (11367218634409244348848489 / 200000000000000000000000000)
  C := (13174148236784429845391831 / 10000000000000000000000000000)
  dδ := (7845643124667886492140667 / 200000000000000000000000000)
  dM := (9548067509431276873605593 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(7606391967002662291008619 / 500000000000000000000000), (15533205330032868118905753 / 100000000000000000000000)]
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
end ForestUnimodality.Stage170KernelData.Cell164
