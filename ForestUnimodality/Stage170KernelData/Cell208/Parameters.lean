import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell208
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (135)
  A := (-2160389649546087727216559 / 1250000000000000000000000)
  B := (4194270691326830446943319 / 50000000000000000000000000)
  C := (14655591066056927740390847 / 50000000000000000000000000)
  dδ := (48843579229604111580087533 / 1000000000000000000000000000)
  dM := (4072715650334362153797349 / 6250000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(6768977234333395820442547 / 250000000000000000000000), (16968973046005761062815509 / 500000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (57 / 107)
  hi := (29 / 54)
  vmin := (725 / 2916)
  damping := (725 / 2916)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell208
