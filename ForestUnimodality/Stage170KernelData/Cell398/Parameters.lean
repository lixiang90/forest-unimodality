import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell398
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (102)
  A := (-7405667445104634155583767 / 5000000000000000000000000)
  B := (86192627330187704393082981 / 1000000000000000000000000000)
  C := (25252123693111222513252301 / 100000000000000000000000000)
  dδ := (47427353916616676876572001 / 1000000000000000000000000000)
  dM := (19094744553643666911020571 / 25000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(5381065704687133077754879 / 500000000000000000000000), (428121572546079764975957 / 12500000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (643 / 1188)
  hi := (6 / 11)
  vmin := (30 / 121)
  damping := (30 / 121)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell398
