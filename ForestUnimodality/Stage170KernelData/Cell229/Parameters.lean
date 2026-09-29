import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell229
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (117)
  A := (-8405302258715698651592163 / 12500000000000000000000000)
  B := (7598371158753464832402713 / 250000000000000000000000000)
  C := (288650584319232079988371 / 2500000000000000000000000)
  dδ := (4754201700740969156744331 / 250000000000000000000000000)
  dM := (1866401151251402849504113 / 12500000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(1890947186503802512902439 / 100000000000000000000000), (33164992845937476317885739 / 1000000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97 / 177)
  hi := (49 / 89)
  vmin := (1960 / 7921)
  damping := (1960 / 7921)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell229
