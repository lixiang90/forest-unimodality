import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (33)
  A := (130274914467438004635369 / 800000000000000000000000)
  B := (84931064085966290200246931 / 10000000000000000000000000000)
  C := (-16436595282439590837153531 / 1000000000000000000000000000)
  dδ := (88856554429552446483508987 / 10000000000000000000000000000)
  dM := (15672402392924999223276089 / 500000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(2524387406675342226947123 / 62500000000000000000000)]
  retention := ![(3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13 / 42)
  hi := (20 / 63)
  vmin := (377 / 1764)
  damping := (3770000000000000000000000000000000000000000 / 43524955408804071509263948678105342569819369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell035
