import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell388
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (116)
  A := (-19416188338898427334555663 / 10000000000000000000000000)
  B := (94534566242405498881495873 / 1000000000000000000000000000)
  C := (4655081019697448248967353 / 2500000000000000000000000000)
  dδ := (26034588951431996556307169 / 500000000000000000000000000)
  dM := (84416072426481798211123087 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(15438426454501701812205283 / 1000000000000000000000000), (12321219695764181523145453 / 125000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 103)
  hi := (107 / 207)
  vmin := (10700 / 42849)
  damping := (10700 / 42849)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell388
