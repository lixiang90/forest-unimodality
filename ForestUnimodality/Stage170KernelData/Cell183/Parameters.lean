import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell183
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (138)
  A := (-3170193025351434858976063 / 2000000000000000000000000)
  B := (36148767126615161116021113 / 500000000000000000000000000)
  C := (26253754678514486589624433 / 10000000000000000000000000000)
  dδ := (11476374686446402448303239 / 250000000000000000000000000)
  dM := (57002176891257129182771779 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(78643161255299922629546927 / 10000000000000000000000000), (2691435051196237049353499 / 1250000000000000000000000), (6317708459877967186457681 / 50000000000000000000000)]
  retention := ![(4 / 5), (7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (109 / 209)
  hi := (11 / 21)
  vmin := (110 / 441)
  damping := (110 / 441)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell183
