import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (199)
  A := (-14649660735594797655778621 / 10000000000000000000000000)
  B := (52338688552796969188918297 / 1000000000000000000000000000)
  C := (-4202852061851762403843491 / 2000000000000000000000000000)
  dδ := (35620224518218855658258093 / 1000000000000000000000000000)
  dM := (6341847892619497262939321 / 20000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(506385143570548978964041 / 31250000000000000000000), (4532430013342390395791881 / 25000000000000000000000)]
  retention := ![(4 / 5), (2 / 5)]
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
end ForestUnimodality.Stage170KernelData.Cell130
