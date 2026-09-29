import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (291)
  A := (-1789055096311876914541017 / 1000000000000000000000000)
  B := (9385642435628568924776971 / 200000000000000000000000000)
  C := (1001761866163075609392763 / 2000000000000000000000000000)
  dδ := (27929071535029124928595223 / 1000000000000000000000000000)
  dM := (346451439891855382586963 / 1562500000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(59112545941864617304872809 / 1000000000000000000000000), (11503549038561085637866199 / 50000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (51 / 101)
  hi := (26 / 51)
  vmin := (650 / 2601)
  damping := (650 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell162
