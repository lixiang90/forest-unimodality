import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell444
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (37)
  A := (12743539571668461741538181 / 100000000000000000000000000)
  B := (18548644914052787868730121 / 1000000000000000000000000000)
  C := (-52361351867206376575758497 / 1000000000000000000000000000)
  dδ := (3711099136424415856350123 / 200000000000000000000000000)
  dM := (807752910396432706940581 / 6250000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(23874947386237392876751073 / 10000000000000000000000000), (11743543613471974396134101 / 1000000000000000000000000)]
  retention := ![(7 / 10), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (19 / 51)
  hi := (97 / 255)
  vmin := (608 / 2601)
  damping := (608 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell444
