import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell179
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (171)
  A := (-8051746803013883574351439 / 5000000000000000000000000)
  B := (15604268507366240298361859 / 250000000000000000000000000)
  C := (4036437362627215939825387 / 2000000000000000000000000000)
  dδ := (39595721394276688076541149 / 1000000000000000000000000000)
  dM := (8426482373573602070032651 / 20000000000000000000000000000)
  wL := (0)
  wR := (0)
  wC := (1)
  price := ![(12955242049568187923114237 / 1000000000000000000000000), (7819842054355801508336299 / 50000000000000000000000)]
  retention := ![(4 / 5), (9 / 20)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (27 / 52)
  hi := (109 / 209)
  vmin := (10900 / 43681)
  damping := (10900 / 43681)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell179
