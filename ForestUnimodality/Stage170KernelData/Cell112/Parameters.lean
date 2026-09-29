import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (133)
  A := (-70313858506728681540209891 / 100000000000000000000000000)
  B := (29609237870388764590767749 / 1000000000000000000000000000)
  C := (-6771473108034892218753953 / 50000000000000000000000000)
  dδ := (10282034809762365459850919 / 500000000000000000000000000)
  dM := (3578559550623716716205927 / 25000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(14141033617198559113603551 / 1000000000000000000000000), (46107952374062037392832281 / 1000000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (301 / 666)
  hi := (17 / 37)
  vmin := (109865 / 443556)
  damping := (109865 / 443556)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell112
