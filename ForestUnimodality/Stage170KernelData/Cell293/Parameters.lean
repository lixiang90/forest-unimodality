import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell293
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (56)
  A := (-51090549196491631391836563 / 1000000000000000000000000000)
  B := (7971708723840356669576579 / 500000000000000000000000000)
  C := (531528393780251323663677 / 12500000000000000000000000)
  dδ := (5977094138595808077429883 / 500000000000000000000000000)
  dM := (75116313294090001901996689 / 1000000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(54284548584430627471419939 / 10000000000000000000000000), (16865988132581154701483683 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3 / 5)
  hi := (123 / 203)
  vmin := (9840 / 41209)
  damping := (9840 / 41209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell293
