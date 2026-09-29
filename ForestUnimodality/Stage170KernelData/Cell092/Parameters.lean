import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (68)
  A := (-7093276284746485610188671 / 25000000000000000000000000)
  B := (15015822996433999397813963 / 500000000000000000000000000)
  C := (-2038289257932528741878997 / 20000000000000000000000000)
  dδ := (22829024923263156743313829 / 1000000000000000000000000000)
  dM := (5010509777635566521815369 / 25000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(90633515085648017617359073 / 10000000000000000000000000), (4965379321389694844413043 / 250000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
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
end ForestUnimodality.Stage170KernelData.Cell092
