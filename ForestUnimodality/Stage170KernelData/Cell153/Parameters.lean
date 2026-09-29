import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (141)
  A := (-18131125515403309533724041 / 10000000000000000000000000)
  B := (76943741919453884081647743 / 1000000000000000000000000000)
  C := (2227849368639656175614637 / 6250000000000000000000000000)
  dδ := (8960752507794443599831169 / 200000000000000000000000000)
  dM := (14759056233856656910677363 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(30239494622754786945506567 / 1000000000000000000000000), (10890295551906491766658291 / 100000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (1 / 2)
  hi := (51 / 101)
  vmin := (2550 / 10201)
  damping := (2550 / 10201)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell153
