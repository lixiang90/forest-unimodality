import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell464
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (97)
  A := (-10674739719762939787983669 / 5000000000000000000000000)
  B := (2886914956020408817849443 / 25000000000000000000000000)
  C := (-32008385643576154483413987 / 10000000000000000000000000000)
  dδ := (372835294459574612124797 / 6250000000000000000000000)
  dM := (11706559191959186455589403 / 10000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(40184060547621083259173247 / 5000000000000000000000000), (86771797137974033375940053 / 1000000000000000000000000)]
  retention := ![(3 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (869 / 1824)
  hi := (581 / 1216)
  vmin := (829895 / 3326976)
  damping := (829895 / 3326976)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell464
