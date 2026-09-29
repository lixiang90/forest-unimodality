import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell481
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (102)
  A := (-17849160880045537480498297 / 10000000000000000000000000)
  B := (97200949617804052738101461 / 1000000000000000000000000000)
  C := (6966430138900214947896691 / 500000000000000000000000000000000000000)
  dδ := (5764140959698602767469211 / 100000000000000000000000000)
  dM := (94455067445356380006343811 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(77459720124053177414680249 / 10000000000000000000000000), (18482296097998622030900151 / 200000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (395 / 792)
  hi := (1 / 2)
  vmin := (156815 / 627264)
  damping := (156815 / 627264)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell481
