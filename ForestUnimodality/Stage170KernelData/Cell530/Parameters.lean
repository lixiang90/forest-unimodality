import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell530
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (86)
  A := (-13948767905331384453404553 / 10000000000000000000000000)
  B := (22186649358140367316316599 / 250000000000000000000000000)
  C := (11191907609567219861190779 / 50000000000000000000000000)
  dδ := (45383812759879453568867547 / 1000000000000000000000000000)
  dM := (2110599972642945138488757 / 2500000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(5944730811603112785590497 / 1250000000000000000000000), (32450183092408309448728687 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97 / 177)
  hi := (49 / 89)
  vmin := (1960 / 7921)
  damping := (1960 / 7921)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell530
