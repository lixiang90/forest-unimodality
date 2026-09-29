import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell315
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (38)
  A := (4213198685070469352353939 / 100000000000000000000000000)
  B := (14985764043483821086888419 / 1000000000000000000000000000)
  C := (163615511870166055463649 / 5000000000000000000000000)
  dδ := (6083665753987616518771997 / 500000000000000000000000000)
  dM := (40223217268033260537486717 / 500000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(728301868161233212362049 / 400000000000000000000000), (76625342712799793254419 / 6250000000000000000000)]
  retention := ![(4 / 5), (7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (467 / 742)
  hi := (236 / 371)
  vmin := (31860 / 137641)
  damping := (31860 / 137641)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell315
