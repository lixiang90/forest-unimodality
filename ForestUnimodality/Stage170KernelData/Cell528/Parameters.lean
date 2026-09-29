import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell528
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (98)
  A := (-8191710485168654748378003 / 5000000000000000000000000)
  B := (6218609387684854647448951 / 62500000000000000000000000)
  C := (3422405182177174626234617 / 12500000000000000000000000)
  dδ := (2127864438705418803632341 / 40000000000000000000000000)
  dM := (95022797934334979168269353 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(9890444006751847538794209 / 2000000000000000000000000), (38047369331960993577013141 / 1000000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
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
end ForestUnimodality.Stage170KernelData.Cell528
