import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell420
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (29)
  A := (1122286647807308568403073 / 10000000000000000000000000)
  B := (11004926476463231660440911 / 500000000000000000000000000)
  C := (10381193644302202927498513 / 200000000000000000000000000)
  dδ := (5363987296329931694915949 / 250000000000000000000000000)
  dM := (9114348269928374663383097 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(5295718697137084873816093 / 500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (236 / 371)
  hi := (9 / 14)
  vmin := (45 / 196)
  damping := (45 / 196)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell420
