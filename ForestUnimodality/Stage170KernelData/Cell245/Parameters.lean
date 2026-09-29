import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell245
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (74)
  A := (-6984103853590663837813679 / 12500000000000000000000000)
  B := (8670816378031168114581817 / 200000000000000000000000000)
  C := (3388069427928991350640331 / 25000000000000000000000000)
  dδ := (28823720750934131440423869 / 1000000000000000000000000000)
  dM := (6560841796346899646233397 / 20000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(17324237631615730936829323 / 10000000000000000000000000), (98260176452712943984124649 / 10000000000000000000000000), (10124947375797685111820101 / 500000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (1 / 2)]
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
end ForestUnimodality.Stage170KernelData.Cell245
