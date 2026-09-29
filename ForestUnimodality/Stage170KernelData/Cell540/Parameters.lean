import ForestUnimodality.FiniteKernelInfiniteTails

/-! Exact parameters of a production stage170 row. Zero-priced Laplace terms are omitted. -/
namespace ForestUnimodality.Stage170KernelData.Cell540
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def row : RationalRow (Fin 2) where
  terms := Finset.univ
  scale := (51)
  A := (-56080334917966461304672521 / 100000000000000000000000000)
  B := (1076832003374538909712399 / 20000000000000000000000000)
  C := (5975412033831220548485419 / 50000000000000000000000000)
  dδ := (1977821379637034315129851 / 62500000000000000000000000)
  dM := (10220757575052964467171579 / 20000000000000000000000000000)
  wL := (0)
  wR := (1)
  wC := (0)
  price := ![(12931186966428132478768021 / 1000000000000000000000000), (19582325328571552613965423 / 2500000000000000000000000)]
  retention := ![(3 / 5), (1 / 2)]
  fixedIndices := ∅
  fixedPrice := fun _ => 0

def interval : IntervalWitness where
  lo := (653 / 1128)
  hi := (7 / 12)
  vmin := (35 / 144)
  damping := (35 / 144)

theorem row_checked : row.signCheck = true := by decide +kernel
theorem interval_checked : interval.check = true := by decide +kernel
#print axioms row_checked
#print axioms interval_checked
end ForestUnimodality.Stage170KernelData.Cell540
