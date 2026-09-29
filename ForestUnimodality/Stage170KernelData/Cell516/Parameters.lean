import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell516
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (101)
  A := (-10643122281987497884614413 / 5000000000000000000000000)
  B := (560334860666526560213363 / 5000000000000000000000000)
  C := (44014788806236871537835853 / 10000000000000000000000000000)
  dδ := (29572373859901940340577653 / 500000000000000000000000000)
  dM := (11007227369547400129545789 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(49153676078197490184606977 / 10000000000000000000000000), (93901274666959750447858823 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (11791 / 22366)
  hi := (23607 / 44732)
  vmin := (498697875 / 2000951824)
  damping := (498697875 / 2000951824)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell516
