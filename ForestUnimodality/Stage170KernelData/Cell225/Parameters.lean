import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell225
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (128)
  A := (-36079812544316499700158829 / 50000000000000000000000000)
  B := (3031964701449946925082557 / 100000000000000000000000000)
  C := (1503190927726986807211329 / 12500000000000000000000000)
  dδ := (4752364733490526370329743 / 250000000000000000000000000)
  dM := (7127466922211794341911889 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(25657908463744703908560041 / 1000000000000000000000000), (31663058734035029573306019 / 1000000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (6 / 11)
  hi := (97 / 177)
  vmin := (7760 / 31329)
  damping := (7760 / 31329)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell225
