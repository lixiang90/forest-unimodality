import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (131)
  A := (-760484544951693637756307 / 400000000000000000000000)
  B := (5265445755512054501479291 / 62500000000000000000000000)
  C := (-13021989570086262791998033 / 5000000000000000000000000000)
  dδ := (9345822757422797555371119 / 200000000000000000000000000)
  dM := (68506144102040589672492077 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(17573260153822836571180233 / 1000000000000000000000000), (111481413767924820490407 / 1000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9 / 19)
  hi := (23 / 48)
  vmin := (90 / 361)
  damping := (90 / 361)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell128
