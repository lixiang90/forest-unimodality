import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell491
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (103)
  A := (-16739739068701341884093381 / 10000000000000000000000000)
  B := (731198356883634992264831 / 8000000000000000000000000)
  C := (14737179834994795953051483 / 10000000000000000000000000000)
  dδ := (56386869325297149513342987 / 1000000000000000000000000000)
  dM := (87634934737864332836981829 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(12846006505952969334316549 / 1000000000000000000000000), (22106279108958773349513649 / 250000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (3579 / 7004)
  hi := (5381 / 10506)
  vmin := (27577625 / 110376036)
  damping := (27577625 / 110376036)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell491
