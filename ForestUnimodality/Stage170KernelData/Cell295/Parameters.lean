import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell295
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (44)
  A := (-42332121304567116855110953 / 500000000000000000000000000)
  B := (2941346996643873397403457 / 125000000000000000000000000)
  C := (28178944888679179764379157 / 500000000000000000000000000)
  dδ := (17551589264390213968036747 / 1000000000000000000000000000)
  dM := (15663049385647169107170507 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(17181337756181626730267453 / 1000000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (123 / 203)
  hi := (63 / 103)
  vmin := (2520 / 10609)
  damping := (2520 / 10609)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell295
