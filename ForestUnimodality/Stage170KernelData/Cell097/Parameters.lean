import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (80)
  A := (-1203515373837905012122107 / 3125000000000000000000000)
  B := (14362120297558237519419677 / 500000000000000000000000000)
  C := (-200039722373557327106397 / 2000000000000000000000000)
  dδ := (20246611544896982864960577 / 1000000000000000000000000000)
  dM := (2117119828077651698589913 / 12500000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(4527731892336976038393459 / 250000000000000000000000), (8208185388427180484427481 / 500000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22 / 51)
  hi := (67 / 153)
  vmin := (638 / 2601)
  damping := (638 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell097
