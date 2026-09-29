import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (200)
  A := (-1602671241098997546572491 / 1000000000000000000000000)
  B := (6941801284554542303406599 / 125000000000000000000000000)
  C := (-66844027678806085864676723 / 100000000000000000000000000000)
  dδ := (35130488542695778586555377 / 1000000000000000000000000000)
  dM := (8410087844687331862843921 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(4087154055314192291348263 / 250000000000000000000000), (1820142604893783015995723 / 10000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (24 / 49)
  hi := (49 / 99)
  vmin := (600 / 2401)
  damping := (600 / 2401)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell145
