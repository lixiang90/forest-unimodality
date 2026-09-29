import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell308
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (47)
  A := (4665090971382725772542699 / 200000000000000000000000000)
  B := (14180444385420720027068953 / 1000000000000000000000000000)
  C := (33855595139644124869082731 / 1000000000000000000000000000)
  dδ := (223218656158227328478727 / 20000000000000000000000000)
  dM := (66806333614283290546140281 / 1000000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(5871623179065442732493807 / 1250000000000000000000000), (132714510056660799364181 / 10000000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (129 / 209)
  hi := (33 / 53)
  vmin := (660 / 2809)
  damping := (660 / 2809)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell308
