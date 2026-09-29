import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (62)
  A := (5490563704763087084614881 / 200000000000000000000000000)
  B := (12460361949099375139526913 / 1000000000000000000000000000)
  C := (-21881356730874036015110917 / 500000000000000000000000000)
  dδ := (2711830076264059447010979 / 250000000000000000000000000)
  dM := (2167371609072749397400387 / 40000000000000000000000000000)
  wL := (1)
  wR := (0)
  wC := (0)
  price := ![(1137832302908570625277207 / 250000000000000000000000), (2618866917228575896814391 / 125000000000000000000000)]
  retention := ![(4 / 5), (7 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (103 / 255)
  hi := (7 / 17)
  vmin := (15656 / 65025)
  damping := (15656 / 65025)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell081
