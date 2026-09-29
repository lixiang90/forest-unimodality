import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (38)
  A := (2399483816808138783693849 / 12500000000000000000000000)
  B := (115459417718549711001641 / 10000000000000000000000000)
  C := (-3718372503798942838026953 / 125000000000000000000000000)
  dδ := (12180020350334254397584033 / 1000000000000000000000000000)
  dM := (27416096550535466649239913 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(42237865447012588049346959 / 10000000000000000000000000), (11858799342485193406560029 / 1250000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (89 / 255)
  hi := (91 / 255)
  vmin := (14774 / 65025)
  damping := (14774 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell053
