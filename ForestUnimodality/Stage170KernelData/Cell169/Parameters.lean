import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (172)
  A := (-2931149161000741056852803 / 2000000000000000000000000)
  B := (11681267804693538925331353 / 200000000000000000000000000)
  C := (7760432810218362504120493 / 5000000000000000000000000000)
  dδ := (19670121818026058829742553 / 500000000000000000000000000)
  dM := (39368462080278330541757703 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(1833945108124840350782847 / 125000000000000000000000), (15582508639743141998224019 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (53 / 103)
  hi := (107 / 207)
  vmin := (10700 / 42849)
  damping := (10700 / 42849)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell169
