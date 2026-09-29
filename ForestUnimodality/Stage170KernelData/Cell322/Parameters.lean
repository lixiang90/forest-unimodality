import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell322
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (31)
  A := (29149981692954750620572213 / 1000000000000000000000000000)
  B := (4072929292222886819840877 / 250000000000000000000000000)
  C := (3049771920744115405454977 / 100000000000000000000000000)
  dδ := (3205346416055157750257809 / 250000000000000000000000000)
  dM := (9916117828524986636557631 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(5528634724124931842936803 / 500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (9 / 14)
  hi := (41 / 63)
  vmin := (902 / 3969)
  damping := (902 / 3969)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell322
