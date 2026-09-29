import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (32)
  A := (17489025739733200405012781 / 100000000000000000000000000)
  B := (81590870695582434768411417 / 10000000000000000000000000000)
  C := (-14681437002849764134060351 / 1000000000000000000000000000)
  dδ := (17595545894691016347577417 / 2000000000000000000000000000)
  dM := (7079426789026728988462201 / 250000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(50864837089607590314699337 / 1000000000000000000000000)]
  retention := ![(3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (37 / 126)
  hi := (19 / 63)
  vmin := (3293 / 15876)
  damping := (32930000000000000000000000000000000000000000 / 391724598679236643583375538102948083128374321)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell028
