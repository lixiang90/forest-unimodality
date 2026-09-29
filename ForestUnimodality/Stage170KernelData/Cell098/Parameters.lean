import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (86)
  A := (-14997708329527228487521029 / 50000000000000000000000000)
  B := (11470059261634227634751859 / 500000000000000000000000000)
  C := (-540146294940810432066991 / 6250000000000000000000000)
  dδ := (3380154788478726551881337 / 200000000000000000000000000)
  dM := (2340040562299250176056531 / 20000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(26326605489090276535080193 / 500000000000000000000000)]
  retention := ![(7 / 10)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (22 / 51)
  hi := (67 / 153)
  vmin := (638 / 2601)
  damping := (638 / 2601)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell098
