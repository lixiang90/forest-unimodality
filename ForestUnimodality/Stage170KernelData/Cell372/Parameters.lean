import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell372
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (64)
  A := (-14452692377244454934981377 / 50000000000000000000000000)
  B := (35012253475892193832486043 / 1000000000000000000000000000)
  C := (-11761178831390269039491869 / 100000000000000000000000000)
  dδ := (27272932615094343244965813 / 1000000000000000000000000000)
  dM := (26760754172532269599266153 / 100000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(32186557308952998823770031 / 5000000000000000000000000), (20736603106990422418220987 / 1000000000000000000000000)]
  retention := ![(7 / 10), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (65 / 153)
  hi := (22 / 51)
  vmin := (5720 / 23409)
  damping := (5720 / 23409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell372
