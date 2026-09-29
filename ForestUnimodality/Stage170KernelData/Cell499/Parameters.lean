import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell499
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (102)
  A := (-9025169805707788600557251 / 5000000000000000000000000)
  B := (98444291323770749535526647 / 1000000000000000000000000000)
  C := (28222405231706866254870469 / 10000000000000000000000000000)
  dδ := (11705392411856825607419097 / 200000000000000000000000000)
  dM := (95861432933585751566679667 / 100000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(81423777255198910296485337 / 10000000000000000000000000), (22999223397950604663719787 / 250000000000000000000000)]
  retention := ![(7 / 10), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (7427 / 14352)
  hi := (11153 / 21528)
  vmin := (115712375 / 463454784)
  damping := (115712375 / 463454784)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell499
