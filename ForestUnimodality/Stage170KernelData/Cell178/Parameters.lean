import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell178
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (138)
  A := (-14742013945872036073581057 / 10000000000000000000000000)
  B := (68801399668795559794176597 / 1000000000000000000000000000)
  C := (22891974254607488567514473 / 10000000000000000000000000000)
  dδ := (45819505387759501546796059 / 1000000000000000000000000000)
  dM := (10849394388715491704261451 / 20000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(22106393644501785011868833 / 2500000000000000000000000), (1276397208396497404692127 / 10000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27 / 52)
  hi := (109 / 209)
  vmin := (10900 / 43681)
  damping := (10900 / 43681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell178
