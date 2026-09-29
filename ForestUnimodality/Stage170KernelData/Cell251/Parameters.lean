import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell251
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (80)
  A := (-8919906643064258205733097 / 25000000000000000000000000)
  B := (13232326387038804635376543 / 500000000000000000000000000)
  C := (87270720430029632974644471 / 1000000000000000000000000000)
  dδ := (17830196139435854768562351 / 1000000000000000000000000000)
  dM := (14629683728018455296168709 / 100000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(22083603713202859530895239 / 2500000000000000000000000), (6371820007019748821619487 / 250000000000000000000000)]
  retention := ![(4 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (13 / 23)
  hi := (21 / 37)
  vmin := (336 / 1369)
  damping := (336 / 1369)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell251
