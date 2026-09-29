import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell213
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (120)
  A := (-1548224317645828064229363 / 1000000000000000000000000)
  B := (77434112539088190141356449 / 1000000000000000000000000000)
  C := (25129231948362951154507527 / 100000000000000000000000000)
  dδ := (43281730541375448839680473 / 1000000000000000000000000000)
  dM := (60098970052686179459805471 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(10542537204612411727566723 / 500000000000000000000000), (8156923194664974730017093 / 250000000000000000000000)]
  retention := ![(7 / 10), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (29 / 54)
  hi := (643 / 1188)
  vmin := (350435 / 1411344)
  damping := (350435 / 1411344)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell213
