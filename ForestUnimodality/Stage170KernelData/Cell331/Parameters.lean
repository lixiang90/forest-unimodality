import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell331
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (30)
  A := (1779029677611614318699651 / 25000000000000000000000000)
  B := (12066726234996601879734257 / 1000000000000000000000000000)
  C := (10973303948461283693904811 / 500000000000000000000000000)
  dδ := (10352199142158033037808273 / 1000000000000000000000000000)
  dM := (30969451755536253297930449 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(95972395036910496113335967 / 100000000000000000000000000), (93172436677915495550905689 / 10000000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (83 / 126)
  hi := (2 / 3)
  vmin := (2 / 9)
  damping := (80000000000000000000000000000000000000000 / 888264396098042275699264258736843725914681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell331
