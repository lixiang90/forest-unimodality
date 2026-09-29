import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell364
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (37)
  A := (1839121621574805287657739 / 10000000000000000000000000)
  B := (3849553203346167077475437 / 250000000000000000000000000)
  C := (-44344409144025327684790483 / 1000000000000000000000000000)
  dδ := (165357585795897384095543 / 10000000000000000000000000)
  dM := (96243820117157012823151663 / 1000000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(31493911802764311680391529 / 10000000000000000000000000), (10757964539647630886065599 / 1000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (31 / 85)
  hi := (19 / 51)
  vmin := (1674 / 7225)
  damping := (1674 / 7225)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell364
