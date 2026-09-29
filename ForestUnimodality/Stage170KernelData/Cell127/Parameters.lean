import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (277)
  A := (-9115930870253432188832221 / 5000000000000000000000000)
  B := (10006596201474320106949989 / 200000000000000000000000000)
  C := (-22619413347759187438157369 / 10000000000000000000000000000)
  dδ := (3750551110050659962824593 / 125000000000000000000000000)
  dM := (771910479333078187438779 / 3125000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(14803358209259606326213543 / 500000000000000000000000), (2455423649398842371738283 / 10000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22 / 47)
  hi := (9 / 19)
  vmin := (550 / 2209)
  damping := (550 / 2209)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell127
