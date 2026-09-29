import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell485
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (104)
  A := (-294816073155348055445657 / 156250000000000000000000)
  B := (99771019186747439411178107 / 1000000000000000000000000000)
  C := (47128253743049697450928637 / 100000000000000000000000000000)
  dδ := (56283619711287889708639653 / 1000000000000000000000000000)
  dM := (19163554351919900951145559 / 20000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(88078280723482667013968239 / 10000000000000000000000000), (93249546722283639610395767 / 1000000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (407 / 808)
  hi := (51 / 101)
  vmin := (2550 / 10201)
  damping := (2550 / 10201)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell485
