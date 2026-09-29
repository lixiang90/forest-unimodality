import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell504
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 3) where
  terms := Finset.univ
  scale := (102)
  A := (-4850178148521703094786517 / 2500000000000000000000000)
  B := (5191488229426792500031951 / 50000000000000000000000000)
  C := (28132081209579292042921583 / 10000000000000000000000000000)
  dδ := (29127440744062052524476769 / 500000000000000000000000000)
  dM := (253311254857367239724103 / 250000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(3990954077634689678433233 / 500000000000000000000000), (38291754074733987067702401 / 1000000000000000000000000), (53730834837220797339796263 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11311 / 21736)
  hi := (22647 / 43472)
  vmin := (471623775 / 1889814784)
  damping := (471623775 / 1889814784)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell504
