import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (264)
  A := (-3582305588933778797127161 / 2000000000000000000000000)
  B := (50472378025305367210684437 / 1000000000000000000000000000)
  C := (-11593708340104099492259837 / 12500000000000000000000000000)
  dδ := (5994325933258797672875673 / 200000000000000000000000000)
  dM := (25605760427296116871209719 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(29791695754186395816986987 / 1000000000000000000000000), (23238811731834758234072069 / 100000000000000000000000)]
  retention := ![(4 / 5), (2 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (47 / 97)
  hi := (24 / 49)
  vmin := (2350 / 9409)
  damping := (2350 / 9409)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell142
