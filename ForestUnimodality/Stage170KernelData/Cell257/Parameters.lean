import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell257
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (83)
  A := (-578173989914896193624827 / 2000000000000000000000000)
  B := (10606714744426369231855567 / 500000000000000000000000000)
  C := (71179113762604523385491007 / 1000000000000000000000000000)
  dδ := (3606715584903576882203069 / 250000000000000000000000000)
  dM := (10058806085318046570110939 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(1387459590725734059901697 / 100000000000000000000000), (21642613013574891311918691 / 1000000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (21 / 37)
  hi := (53 / 93)
  vmin := (2120 / 8649)
  damping := (2120 / 8649)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell257
