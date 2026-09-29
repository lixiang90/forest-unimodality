import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell404
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (69)
  A := (-14146358055979625167708491 / 20000000000000000000000000)
  B := (13788993792247456263155847 / 250000000000000000000000000)
  C := (15341445576264950423350797 / 100000000000000000000000000)
  dδ := (10595390329296119121677 / 312500000000000000000000)
  dM := (9614573180121492547087203 / 20000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(95415913882097136422544281 / 10000000000000000000000000), (19897114337508238435248131 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (116 / 207)
  hi := (13 / 23)
  vmin := (130 / 529)
  damping := (130 / 529)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell404
