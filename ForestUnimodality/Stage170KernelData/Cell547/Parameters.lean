import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell547
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 1) where
  terms := Finset.univ
  scale := (33)
  A := (2610083265688868920051391 / 25000000000000000000000000)
  B := (23982530570769197697522657 / 1000000000000000000000000000)
  C := (67709848017648038842608571 / 1000000000000000000000000000)
  dδ := (12174107007964089441354183 / 500000000000000000000000000)
  dM := (20796302677153228471995661 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(6321967107981198985555693 / 500000000000000000000000)]
  retention := ![(7 / 10)]
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
end ForestUnimodality.Stage170KernelData.Cell547
