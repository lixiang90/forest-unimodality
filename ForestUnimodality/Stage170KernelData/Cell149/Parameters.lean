import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (169)
  A := (-1501046000460907793296883 / 1000000000000000000000000)
  B := (6002356876717218625572059 / 100000000000000000000000000)
  C := (-1319451598245871598764651 / 12500000000000000000000000000)
  dδ := (19761955235507087241808577 / 500000000000000000000000000)
  dM := (10255412566803395659625897 / 25000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(11719454377914217957368237 / 1000000000000000000000000), (15574009126728171281683899 / 100000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (49 / 99)
  hi := (1 / 2)
  vmin := (2450 / 9801)
  damping := (2450 / 9801)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell149
