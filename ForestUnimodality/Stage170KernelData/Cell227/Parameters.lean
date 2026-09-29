import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell227
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (102)
  A := (-34706521156125005378001447 / 50000000000000000000000000)
  B := (10518494310768296273739253 / 250000000000000000000000000)
  C := (126694326993995609598187 / 800000000000000000000000)
  dδ := (14332559708537190648613979 / 500000000000000000000000000)
  dM := (27560713734051562077628783 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(83511900987038067967205279 / 10000000000000000000000000), (2304334460329271916378957 / 62500000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (97 / 177)
  hi := (49 / 89)
  vmin := (1960 / 7921)
  damping := (1960 / 7921)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell227
