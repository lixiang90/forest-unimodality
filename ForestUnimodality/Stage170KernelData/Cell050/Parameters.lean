import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (36)
  A := (2184044335961502755871777 / 12500000000000000000000000)
  B := (11155738658903718157899831 / 1000000000000000000000000000)
  C := (-27339706419339845910876363 / 1000000000000000000000000000)
  dδ := (742252039928236601040723 / 62500000000000000000000000)
  dM := (2645111534209445842535241 / 50000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(3659559572913014813266841 / 1250000000000000000000000), (97725760318412575600177661 / 10000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29 / 85)
  hi := (89 / 255)
  vmin := (1624 / 7225)
  damping := (2598400000000000000000000000000000000000000 / 28523156719148246408565263419438648532149201)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell050
