import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell244
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (99)
  A := (-43175409230884686072826639 / 100000000000000000000000000)
  B := (12422675929792799387474389 / 500000000000000000000000000)
  C := (11825559634744974707443177 / 125000000000000000000000000)
  dδ := (8487740822538279369946501 / 500000000000000000000000000)
  dM := (1518686709829691310199521 / 12500000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(158561556160246697189109 / 7812500000000000000000), (2895099595057068597725447 / 125000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (5 / 9)
  hi := (116 / 207)
  vmin := (10556 / 42849)
  damping := (10556 / 42849)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell244
