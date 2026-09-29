import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell543
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (42)
  A := (-5573974408828197080012501 / 20000000000000000000000000)
  B := (5120960711018405532579667 / 125000000000000000000000000)
  C := (91881305952256894786778219 / 1000000000000000000000000000)
  dδ := (3450983496562889680375763 / 125000000000000000000000000)
  dM := (19055628863670737269293831 / 50000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(2718198580645733386518259 / 2000000000000000000000000), (7638028074322148697206103 / 500000000000000000000000)]
  retention := ![(7 / 10), (3 / 5)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (107 / 180)
  hi := (3 / 5)
  vmin := (6 / 25)
  damping := (6 / 25)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell543
