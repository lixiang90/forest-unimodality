import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell197
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (284)
  A := (-17885679994434706030403959 / 10000000000000000000000000)
  B := (47946943028395791475126941 / 1000000000000000000000000000)
  C := (18628200953925686846057719 / 10000000000000000000000000000)
  dδ := (1436930753657453610494521 / 50000000000000000000000000)
  dM := (23061110985278326056258091 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(7326277039644847377530823 / 100000000000000000000000), (5223044895228249373531071 / 25000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (111 / 211)
  hi := (28 / 53)
  vmin := (700 / 2809)
  damping := (700 / 2809)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell197
